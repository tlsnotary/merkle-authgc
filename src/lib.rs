use ct_merkle::{
    batch_inclusion::BatchInclusionProof, inclusion::InclusionProof, CanonicalSerialize,
    CtMerkleTree, RootHash, SimpleWriter,
};
use digest::Digest;
use rand_core::{CryptoRng, RngCore};

type Label = [u8; 16];
type Randomness = [u8; 16];

//The UserLabel of bit `b` at index `i` appears in this data structure at index `2i + b`.
/// The Merkle tree containing all the Notary's labels.
pub struct NotaryLabels<H: Digest>(CtMerkleTree<H, Label>);
/// The Merkle tree containing all the User's labels.
pub struct UserLabels<H: Digest>(CtMerkleTree<H, LabelAndRandomness>);

/// The root hash of the Notary's label tree
pub struct NotaryLabelRoot<H: Digest>(RootHash<H>);
/// The root hash of the User's label tree
pub struct UserLabelRoot<H: Digest>(RootHash<H>);

impl<H: Digest> NotaryLabels<H> {
    /// Get the Merkle root of the Notary label tree
    pub fn root(&self) -> NotaryLabelRoot<H> {
        NotaryLabelRoot(self.0.root())
    }
}

impl<H: Digest> UserLabels<H> {
    /// Get the Merkle root of the User label tree
    pub fn root(&self) -> UserLabelRoot<H> {
        UserLabelRoot(self.0.root())
    }
}

/// Contains a label and a random string used for hiding in the commitment
#[derive(Copy, Clone)]
struct LabelAndRandomness {
    label: Label,
    randomness: Randomness,
}

impl CanonicalSerialize for LabelAndRandomness {
    fn serialize<W: SimpleWriter>(&self, mut w: W) {
        self.label.serialize(&mut w);
        self.randomness.serialize(&mut w);
    }
}

/// Contains all the info about the User's plaintext
pub struct Plaintext<H: Digest> {
    /// The plaintext bitstring
    pub bits: Vec<bool>,
    /// The Merkle tree of the plaintext
    pub label_tree: UserLabels<H>,
}

/// Commits to the given label set by making a tree out of the (blinded) labels. This is done by
/// the User before she learns the decoding of her plaintext.
pub fn user_commit<H, R>(mut rng: R, labels: &[Label]) -> UserLabels<H>
where
    R: CryptoRng + RngCore,
    H: Digest,
{
    let mut tree = CtMerkleTree::new();
    labels.iter().cloned().for_each(|label| {
        let mut randomness = Randomness::default();
        rng.fill_bytes(&mut randomness);

        let entry = LabelAndRandomness { label, randomness };
        tree.push(entry);
    });

    UserLabels(tree)
}

/// Commits to the given label set by making a tree out of the  labels. The labels must be ordered
/// as `[label1bit0, label1bit1, label2bit0, label2bit1, ...]`
pub fn notary_commit<H>(labels: &[Label]) -> NotaryLabels<H>
where
    H: Digest,
{
    let mut tree = CtMerkleTree::new();
    labels.iter().cloned().for_each(|label| {
        tree.push(label);
    });

    NotaryLabels(tree)
}

/// A proof revealing a plaintext bit
pub struct BitProof<H: Digest> {
    active_label: LabelAndRandomness,
    active_label_proof: InclusionProof<H>,
    full_label_proof: InclusionProof<H>,
}

/// A batch proof revealing a number of plaintext bits
pub struct BatchBitProof<H: Digest> {
    active_labels: Vec<LabelAndRandomness>,
    active_labels_proof: BatchInclusionProof<H>,
    full_labels_proof: BatchInclusionProof<H>,
}

impl<H: Digest> Plaintext<H> {
    pub fn prove_bit(&self, idx: usize, all_labels: &NotaryLabels<H>) -> BitProof<H> {
        let bit = *self.bits.get(idx).unwrap();
        let active_label = *self.label_tree.0.get(idx).unwrap();
        let active_label_proof = self.label_tree.0.prove_inclusion(idx);
        let full_label_proof = all_labels.0.prove_inclusion(2 * idx + (bit as usize));

        BitProof {
            active_label,
            active_label_proof,
            full_label_proof,
        }
    }

    pub fn prove_bits(
        &self,
        range: core::ops::RangeInclusive<usize>,
        all_labels: &NotaryLabels<H>,
    ) -> BatchBitProof<H> {
        let active_idxs: Vec<usize> = range.clone().collect();
        let bits = self.bits[range.clone()].to_vec();
        let full_idxs: Vec<usize> = active_idxs
            .iter()
            .zip(bits.iter())
            .map(|(idx, bit)| 2 * idx + (*bit as usize))
            .collect();

        let active_labels = range
            .map(|i| self.label_tree.0.get(i).unwrap())
            .cloned()
            .collect();
        let active_labels_proof = self.label_tree.0.prove_batch_inclusion(&active_idxs);
        let full_labels_proof = all_labels.0.prove_batch_inclusion(&full_idxs);

        BatchBitProof {
            active_labels,
            active_labels_proof,
            full_labels_proof,
        }
    }
}

/// Verifies that `bit` occurs in the plaintext committed by `user_root` in position `idx`.
pub fn verify_bit<H: Digest>(
    bit: bool,
    idx: usize,
    user_root: &UserLabelRoot<H>,
    notary_root: &NotaryLabelRoot<H>,
    proof: &BitProof<H>,
) -> Result<(), ()> {
    // First check the active label's presence in the user label tree
    user_root
        .0
        .verify_inclusion(&proof.active_label, idx, &proof.active_label_proof)
        .map_err(|_| ())?;

    // Then check the label's presence in the notary label tree
    notary_root
        .0
        .verify_inclusion(
            &proof.active_label.label,
            idx * 2 + (bit as usize),
            &proof.full_label_proof,
        )
        .map_err(|_| ())?;

    Ok(())
}

/// Verifies that `bits` occurs in the plaintext committed by `user_root` in the indices contained
/// in `range`.
pub fn verify_bits<H: Digest>(
    bits: &[bool],
    range: core::ops::RangeInclusive<usize>,
    user_root: &UserLabelRoot<H>,
    notary_root: &NotaryLabelRoot<H>,
    proof: &BatchBitProof<H>,
) -> Result<(), ()> {
    let active_idxs: Vec<usize> = range.clone().collect();

    // First check the active label's presence in the user label tree
    user_root
        .0
        .verify_batch_inclusion(
            &proof.active_labels,
            &active_idxs,
            &proof.active_labels_proof,
        )
        .map_err(|_| ())?;

    let active_labels: Vec<Label> = proof.active_labels.iter().map(|lr| lr.label).collect();
    let full_idxs: Vec<usize> = active_idxs
        .iter()
        .zip(bits.iter())
        .map(|(idx, bit)| 2 * idx + (*bit as usize))
        .collect();

    // Then check the label's presence in the notary label tree
    notary_root
        .0
        .verify_batch_inclusion(&active_labels, &full_idxs, &proof.full_labels_proof)
        .map_err(|_| ())?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::Blake2s256;
    use rand::{thread_rng, Rng};

    type H = Blake2s256;

    #[test]
    fn test_subslice_reveal() {
        let mut rng = thread_rng();
        let log_plaintext_bitlen = 15;
        let plaintext_bitlen = 1 << log_plaintext_bitlen;
        let subslice_size = 100;

        // Generate random labels
        let all_labels: Vec<Label> = core::iter::repeat_with(|| rng.gen::<Label>())
            .take(2 * plaintext_bitlen)
            .collect();

        // Pick a random plaintext
        let plaintext: Vec<bool> = core::iter::repeat_with(|| rng.gen::<bool>())
            .take(plaintext_bitlen)
            .collect();

        // Extract the plaintext labels from the set of all labels
        let plaintext_labels: Vec<Label> = plaintext
            .iter()
            .enumerate()
            .map(|(i, b)| all_labels.get(2 * i + (*b as usize)).unwrap())
            .cloned()
            .collect();

        // Commit to everything
        let user_tree = user_commit::<H, _>(&mut rng, &plaintext_labels);
        let notary_tree = notary_commit::<H>(&all_labels);
        let user_root = user_tree.root();
        let notary_root = notary_tree.root();

        let pt = Plaintext {
            label_tree: user_tree,
            bits: plaintext.clone(),
        };

        // Prove a randomly bit slice

        let bit_idx = rng.gen_range(0..plaintext_bitlen - subslice_size);

        // Do the proofs naively
        let start = std::time::Instant::now();
        let proofs: Vec<BitProof<H>> = (bit_idx..(bit_idx + subslice_size))
            .map(|i| pt.prove_bit(i, &notary_tree))
            .collect();
        let naive_proof_time = start.elapsed().as_micros();

        // Now do batching
        let range = bit_idx..=(bit_idx + subslice_size - 1);

        // Do the proofs using batching
        let start = std::time::Instant::now();
        let batch_proof = pt.prove_bits(range.clone(), &notary_tree);
        let batch_proof_time = start.elapsed().as_micros();

        // Verify the naive proofs
        let start = std::time::Instant::now();
        range.clone().zip(proofs.iter()).for_each(|(i, proof)| {
            verify_bit(plaintext[i], i, &user_root, &notary_root, &proof).unwrap()
        });
        let naive_verif_time = start.elapsed().as_micros();

        // Verify the batch proof
        let bits = &plaintext[range.clone()];
        let start = std::time::Instant::now();
        verify_bits(&bits, range, &user_root, &notary_root, &batch_proof).unwrap();
        let batch_verif_time = start.elapsed().as_micros();

        println!(
            "Naively revealing {} of 2^{} bits took: {}us / {}us (proof/verif)",
            subslice_size, log_plaintext_bitlen, naive_proof_time, naive_verif_time
        );
        println!(
            "Batched revealing {} of 2^{} bits took: {}us / {}us (proof/verif)",
            subslice_size, log_plaintext_bitlen, batch_proof_time, batch_verif_time
        );
        println!(
            "Proof size is {}B / {}B (naive/batched)",
            2 * proofs.len() * proofs[0].active_label_proof.as_bytes().len(),
            2 * batch_proof.active_labels_proof.as_bytes().len(),
        );
    }

    // A quick batch merkle tree benchmark using a different library. We really don't need this
    #[test]
    fn test_reveal_wintercrypto() {
        use winter_crypto::{Hasher, MerkleTree};
        type H = winter_crypto::hashers::Blake3_256<winter_math::fields::f128::BaseElement>;

        let placeholder = H::hash(b"hello");
        let leaves = vec![placeholder; 1 << 15];
        let tree = MerkleTree::<H>::new(leaves).unwrap();

        let indices: Vec<usize> = (100..200).collect();

        let start = std::time::Instant::now();
        let proof = tree.prove_batch(&indices).unwrap();
        let proof_time = start.elapsed().as_nanos();

        println!("Proving 100 of 2^15 bits: {proof_time}us");
        println!("Proof size is {}", proof.serialize_nodes().len());
    }
}
