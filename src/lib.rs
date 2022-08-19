#![no_std]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

use alloc::vec::Vec;

use ct_merkle::{
    batch_inclusion::BatchInclusionProof, error::InclusionVerifError, CanonicalSerialize,
    CtMerkleTree, RootHash, SimpleWriter,
};
use digest::Digest;
use rand_core::{CryptoRng, RngCore};
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};

type Label = [u8; 16];
type Randomness = [u8; 16];

/// Contains a label and a random string used for hiding in the commitment
#[derive(Copy, Clone, SerdeSerialize, SerdeDeserialize)]
struct LabelAndRandomness {
    label: Label,
    randomness: Randomness,
}

//The UserLabel of bit `b` at index `i` appears in this data structure at index `2i + b`.
/// The Merkle tree containing all the Notary's labels.
#[derive(Clone, SerdeSerialize, SerdeDeserialize)]
pub struct NotaryLabels<H: Digest>(CtMerkleTree<H, Label>);
/// The Merkle tree containing all the User's labels.
#[derive(Clone, SerdeSerialize, SerdeDeserialize)]
pub struct UserLabels<H: Digest>(CtMerkleTree<H, LabelAndRandomness>);

/// The root hash of the Notary's label tree
pub struct NotaryLabelRoot<H: Digest>(RootHash<H>);
/// The root hash of the User's label tree
pub struct UserLabelRoot<H: Digest>(RootHash<H>);

/// A batch proof revealing a number of plaintext bits
#[derive(Clone, SerdeSerialize, SerdeDeserialize)]
pub struct BatchBitProof<H: Digest> {
    /// The labels and blinds corresponding to the revealed bits
    active_labels: Vec<LabelAndRandomness>,
    ///  The batch proof of membership of the labels+blinds in the user's Merkle tree
    active_labels_proof: BatchInclusionProof<H>,
    ///  The batch proof of membership of the labels in the Notary's Merkle tree
    full_labels_proof: BatchInclusionProof<H>,
}

/// Contains all the info about the User's plaintext
#[derive(Clone, SerdeSerialize, SerdeDeserialize)]
pub struct Plaintext<H: Digest> {
    /// The plaintext bitstring
    pub bits: Vec<bool>,
    /// The Merkle tree of the plaintext
    pub label_tree: UserLabels<H>,
}

impl CanonicalSerialize for LabelAndRandomness {
    fn serialize<W: SimpleWriter>(&self, mut w: W) {
        CanonicalSerialize::serialize(&self.label, &mut w);
        CanonicalSerialize::serialize(&self.randomness, &mut w);
    }
}

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

/// Commits to the active label set by making a tree out of the (blinded) labels. This is done by
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

/// Commits to the full label set by making a tree out of the  labels. The labels must be ordered
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

impl<H: Digest> Plaintext<H> {
    /// Proves that the given range of bits occurs in this `Plaintext`.
    ///
    /// Panics if `range.is_empty()` or if `range.end >= self.len()`
    pub fn prove_bits(
        &self,
        range: core::ops::RangeInclusive<usize>,
        all_labels: &NotaryLabels<H>,
    ) -> BatchBitProof<H> {
        let active_idxs: Vec<usize> = range.clone().collect();
        let bits = self.bits[range.clone()].to_vec();

        // Get the corresponding indices into the full label set. Recall label i bit b occurs in
        // the full set at index 2i + b
        let full_idxs: Vec<usize> = active_idxs
            .iter()
            .zip(bits.iter())
            .map(|(idx, bit)| 2 * idx + (*bit as usize))
            .collect();

        // Now get the (blinded) active labels from the plaintext Merkle tree
        let active_labels = range
            .map(|i| self.label_tree.0.get(i).unwrap())
            .cloned()
            .collect();

        // Compute the proofs of inclusion for the user's Merkle tree and the Notary's Merkle tree
        let active_labels_proof = self.label_tree.0.prove_batch_inclusion(&active_idxs);
        let full_labels_proof = all_labels.0.prove_batch_inclusion(&full_idxs);

        BatchBitProof {
            active_labels,
            active_labels_proof,
            full_labels_proof,
        }
    }
}

/// Verifies that `bits` occurs in the plaintext committed by `user_root` in the indices contained
/// in `range`.
///
/// Panics if `range.len() != bits.len()` or if `range.end >= self.len()`
pub fn verify_bits<H: Digest>(
    bits: &[bool],
    range: core::ops::RangeInclusive<usize>,
    user_root: &UserLabelRoot<H>,
    notary_root: &NotaryLabelRoot<H>,
    proof: &BatchBitProof<H>,
) -> Result<(), InclusionVerifError> {
    let active_idxs: Vec<usize> = range.clone().collect();

    // First check the active label's presence in the user label tree
    user_root.0.verify_batch_inclusion(
        &proof.active_labels,
        &active_idxs,
        &proof.active_labels_proof,
    )?;

    let active_labels: Vec<Label> = proof.active_labels.iter().map(|lr| lr.label).collect();
    let full_idxs: Vec<usize> = active_idxs
        .iter()
        .zip(bits.iter())
        .map(|(idx, bit)| 2 * idx + (*bit as usize))
        .collect();

    // Then check the label's presence in the notary label tree
    notary_root
        .0
        .verify_batch_inclusion(&active_labels, &full_idxs, &proof.full_labels_proof)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::Blake2s256;
    use rand::{thread_rng, Rng};

    type H = Blake2s256;

    const LOG_PLAINTEXT_BITLEN: usize = 15;
    const PLAINTEXT_BITLEN: usize = 1 << LOG_PLAINTEXT_BITLEN;

    fn setup() -> (Plaintext<H>, NotaryLabels<H>) {
        let mut rng = thread_rng();

        // Generate random labels
        let all_labels: Vec<Label> = core::iter::repeat_with(|| rng.gen::<Label>())
            .take(2 * PLAINTEXT_BITLEN)
            .collect();

        // Pick a random plaintext
        let plaintext: Vec<bool> = core::iter::repeat_with(|| rng.gen::<bool>())
            .take(PLAINTEXT_BITLEN)
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

        let pt = Plaintext {
            label_tree: user_tree,
            bits: plaintext.clone(),
        };

        (pt, notary_tree)
    }

    // Helper function for doing very basic benchmarks. If the "std" feature is set, this returns
    // the time it takes to run f(), in microseconds. If "std" is not set, this returns 0.
    fn timeit_micros<T>(f: impl FnOnce() -> T) -> (T, u128) {
        #[cfg(feature = "std")]
        let start = std::time::Instant::now();

        let out = f();

        #[cfg(feature = "std")]
        return (out, start.elapsed().as_micros());

        #[cfg(not(feature = "std"))]
        return (out, 0);
    }

    // Checks that an honestly generated proof verifies successfully
    #[test]
    fn test_subslice_proof_correctness() {
        let mut rng = thread_rng();
        let subslice_size = 100;

        // Do setup
        let (pt, notary_tree) = setup();
        let user_root = pt.label_tree.root();
        let notary_root = notary_tree.root();

        // Prove a randomly chosen bit slice

        let bit_idx = rng.gen_range(0..pt.bits.len() - subslice_size);

        // Do the proofs naively, one bit at a time
        let (proofs, _naive_proof_time) = timeit_micros(|| {
            (bit_idx..(bit_idx + subslice_size))
                .map(|i| pt.prove_bits(i..=i, &notary_tree))
                .collect::<Vec<BatchBitProof<H>>>()
        });

        // Now do batching
        let range = bit_idx..=(bit_idx + subslice_size - 1);

        // Do the proofs using batching
        let (batch_proof, _batch_proof_time) =
            timeit_micros(|| pt.prove_bits(range.clone(), &notary_tree));

        // Verify the naive proofs, one bit at a time
        let (_, _naive_verif_time) = timeit_micros(|| {
            range.clone().zip(proofs.iter()).for_each(|(i, proof)| {
                verify_bits(&pt.bits[i..=i], i..=i, &user_root, &notary_root, &proof).unwrap()
            })
        });

        // Verify the batch proof
        let bits = &pt.bits[range.clone()];
        let (_, _batch_verif_time) = timeit_micros(|| {
            verify_bits(&bits, range, &user_root, &notary_root, &batch_proof).unwrap()
        });

        #[cfg(feature = "std")]
        std::println!(
            "Naively revealing {} of 2^{} bits took: {}us / {}us (proof/verif)",
            subslice_size,
            LOG_PLAINTEXT_BITLEN,
            _naive_proof_time,
            _naive_verif_time
        );
        #[cfg(feature = "std")]
        std::println!(
            "Batched revealing {} of 2^{} bits took: {}us / {}us (proof/verif)",
            subslice_size,
            LOG_PLAINTEXT_BITLEN,
            _batch_proof_time,
            _batch_verif_time
        );
        #[cfg(feature = "std")]
        std::println!(
            "Proof size is {}B / {}B (naive/batched)",
            2 * proofs.len() * proofs[0].active_labels_proof.as_bytes().len(),
            2 * batch_proof.active_labels_proof.as_bytes().len(),
        );
    }

    // Checks that mutating the proofs or the plaintext causes verification to fail
    #[test]
    fn test_subslice_proof_soundness() {
        let mut rng = thread_rng();
        let subslice_size = 100;

        // Do setup
        let (pt, notary_tree) = setup();
        let user_root = pt.label_tree.root();
        let notary_root = notary_tree.root();

        // Prove a randomly chosen bit slice

        let bit_idx = rng.gen_range(0..pt.bits.len() - subslice_size);
        let range = bit_idx..=(bit_idx + subslice_size - 1);
        let batch_proof = pt.prove_bits(range.clone(), &notary_tree);

        // Verify the batch proof
        let bits = &pt.bits[range.clone()];
        verify_bits(&bits, range.clone(), &user_root, &notary_root, &batch_proof).unwrap();

        //
        // Now modify parts of the proof or plaintext and ensure it fails to verify
        //

        // Flip a bit in the user label proof
        let mut bad_proof = batch_proof.clone();
        bad_proof.active_labels_proof = {
            let mut buf = bad_proof.active_labels_proof.as_bytes().to_vec();
            // Flip the lowest bit of the 10th byte
            buf[10] ^= 1;
            BatchInclusionProof::from_bytes(buf)
        };
        assert!(verify_bits(&bits, range.clone(), &user_root, &notary_root, &bad_proof).is_err());

        // Flip a bit in the notary label proof
        let mut bad_proof = batch_proof.clone();
        bad_proof.full_labels_proof = {
            let mut buf = bad_proof.active_labels_proof.as_bytes().to_vec();
            // Flip the lowest bit of the 10th byte
            buf[10] ^= 1;
            BatchInclusionProof::from_bytes(buf)
        };
        assert!(verify_bits(&bits, range.clone(), &user_root, &notary_root, &bad_proof).is_err());

        // Flip a bit of plaintext
        let mut bad_plaintext = bits.clone().to_vec();
        bad_plaintext[10] ^= true;
        assert!(verify_bits(
            &bad_plaintext,
            range.clone(),
            &user_root,
            &notary_root,
            &bad_proof
        )
        .is_err());
    }
}
