use crate::{Label, NotaryLabelTree, UserLabelTree};

use alloc::vec::Vec;

use digest::Digest;
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRng, RngCore, SeedableRng};
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};

// The psuedorandom generator we use for all label and randomness generation
type Prg = ChaCha20Rng;
// The seed type of `Prg`
type Seed = <Prg as SeedableRng>::Seed;

/// A seed used by the Notary to generate random labels
#[derive(Copy, Clone, SerdeSerialize, SerdeDeserialize)]
pub struct LabelSeed(Seed);

/// A seed used by the User to generate random label blinders
#[derive(Copy, Clone, SerdeSerialize, SerdeDeserialize)]
pub struct LabelRandomnessSeed(Seed);

impl LabelSeed {
    /// Generates a random seed for label generation
    pub fn new<R: CryptoRng + RngCore>(mut rng: R) -> LabelSeed {
        let mut seed = Seed::default();
        rng.fill_bytes(&mut seed);

        LabelSeed(seed)
    }

    /// Generates a pseudorandom label set for the given number of bits. The labels are ordered as
    /// `[label1bit0, label1bit1, label2bit0, label2bit1, ...]`. That is, the output length is `2 *
    /// num_bits`.
    pub fn gen_notary_labels<H: Digest>(&self, num_bits: usize) -> Vec<Label> {
        // Make an RNG from our label seed
        let mut rng = Prg::from_seed(self.0);

        // Generate all the labels. There are 2*num_bits many of them
        (0..(2 * num_bits))
            .map(|_| {
                let mut buf = Label::default();
                rng.fill_bytes(&mut buf);
                buf
            })
            .collect()
    }
}

impl<H: Digest> NotaryLabelTree<H> {
    /// Commits to the Notary's label set by making a tree out of the labels. `num_bits` is the
    /// number of plaintext bits, and `label_seed` is used to generate the labels.
    pub fn gen_from_seed(num_bits: usize, label_seed: LabelSeed) -> NotaryLabelTree<H> {
        // Make the RNGs for the blinders and labels
        let mut label_rng = Prg::from_seed(label_seed.0);

        // Use the label seed to collect the Notary's labels. There are 2*num_bits many of them
        let labels = (0..2 * num_bits).map(|_| {
            // Compute the label
            let mut label = Label::default();
            label_rng.fill_bytes(&mut label);
            label
        });

        // Make the tree
        Self::from_labels(labels)
    }
}

impl LabelRandomnessSeed {
    /// Generates a random seed for label blinder generation
    pub fn new<R: RngCore + CryptoRng>(mut rng: R) -> LabelRandomnessSeed {
        let mut seed = <ChaCha20Rng as SeedableRng>::Seed::default();
        rng.fill_bytes(&mut seed);

        LabelRandomnessSeed(seed)
    }
}

impl<H: Digest> UserLabelTree<H> {
    /// Commits to the active label set by making a tree out of the (blinded) labels. `seed` is
    /// used to generate the blinds. This method is called by the User before she learns the
    /// decoding of her plaintext.
    pub fn gen_from_labels_with_seed<'a>(
        blinder_seed: LabelRandomnessSeed,
        user_labels: impl IntoIterator<Item = Label>,
    ) -> UserLabelTree<H> {
        // Make an RNG from our blinder seed
        let mut rng = Prg::from_seed(blinder_seed.0);

        UserLabelTree::gen_from_labels(&mut rng, user_labels)
    }

    /// Commits to the active label set by making a tree out of the (blinded) labels. `plaintext`
    /// are the plaintext bits. `blinder_seed` is used to generate the blinds. `label_seed` is used
    /// to generate the labels.
    pub fn gen_from_seeds(
        plaintext: &[bool],
        blinder_seed: LabelRandomnessSeed,
        label_seed: LabelSeed,
    ) -> UserLabelTree<H> {
        // Make the RNGs for the blinders and labels
        let mut label_rng = Prg::from_seed(label_seed.0);

        // Use the label seed to collect just the active labels
        let active_labels = (0..plaintext.len() * 2).filter_map(|i| {
            // Compute the label
            let mut label = Label::default();
            label_rng.fill_bytes(&mut label);

            // Get the plaintext bit that this label MAY represent
            let bit = plaintext[i / 2];

            // If the bit is 0, then the corresponding label is the even label. If the bit is 1
            // then it's the odd label. Only save the label if its parity matches the bit.
            if (bit as usize) == i % 2 {
                Some(label)
            } else {
                None
            }
        });

        Self::gen_from_labels_with_seed(blinder_seed, active_labels)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{verify_bits, Plaintext};

    use blake2::Blake2s256;
    use rand::{thread_rng, Rng};

    type H = Blake2s256;

    const LOG_PLAINTEXT_BITLEN: usize = 15;
    const PLAINTEXT_BITLEN: usize = 1 << LOG_PLAINTEXT_BITLEN;

    #[test]
    fn gen_correctness() {
        let mut rng = thread_rng();

        // Random plaintext
        let plaintext: Vec<bool> = core::iter::repeat_with(|| rng.gen::<bool>())
            .take(PLAINTEXT_BITLEN)
            .collect();

        //
        // Notary
        //

        // Pick a label seed and generate the labels
        let label_seed = LabelSeed::new(&mut rng);
        let all_labels = label_seed.gen_notary_labels::<H>(PLAINTEXT_BITLEN);

        // Commit to all the labels
        let notary_root = {
            let notary_tree = NotaryLabelTree::<H>::from_labels(all_labels.clone());
            notary_tree.root()
        };

        //
        // User
        //

        // Placeholder for a garbled circuit. The user ends up with a set of plaintext labels (that
        // we've determined in this test in advance)
        let plaintext_labels: Vec<Label> = plaintext
            .iter()
            .enumerate()
            .map(|(i, &b)| all_labels.get(2 * i + (b as usize)).unwrap())
            .cloned()
            .collect();

        // Commit to user's labels, using a seed for the commitment randomness
        let blinder_seed = LabelRandomnessSeed::new(&mut rng);
        let user_root = {
            let user_tree =
                UserLabelTree::<H>::gen_from_labels_with_seed(blinder_seed, plaintext_labels);
            user_tree.root()
        };

        //
        // User sends root to the notary, gets it signed, learns the plaintext, and learns the
        // Notary's label seed. The user now wants to do a selective disclosure to a third party
        //

        // Reconstruct the Plaintext struct from just seeds
        let user_tree = UserLabelTree::gen_from_seeds(&plaintext, blinder_seed, label_seed);
        assert_eq!(user_tree.root(), user_root);
        let notary_tree = NotaryLabelTree::gen_from_seed(PLAINTEXT_BITLEN, label_seed);
        let pt = Plaintext {
            bits: plaintext,
            label_tree: user_tree,
        };

        // Prove a randomly chosen bit slice
        let subslice_size = 100;
        let bit_idx = rng.gen_range(0..PLAINTEXT_BITLEN - subslice_size);
        let range = bit_idx..=(bit_idx + subslice_size - 1);
        let batch_proof = pt.prove_bits(range.clone(), &notary_tree);

        // Verify the batch proof
        let bits = &pt.bits[range.clone()];
        verify_bits(&bits, range.clone(), &user_root, &notary_root, &batch_proof).unwrap();
    }
}
