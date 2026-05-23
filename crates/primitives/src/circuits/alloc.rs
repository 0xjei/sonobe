use ark_ff::{Field, PrimeField};
use ark_r1cs_std::fields::fp::{AllocatedFp, FpVar};
use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef, SynthesisError, Variable};
use ark_std::{
    any::{Any, TypeId},
    collections::BTreeMap,
    hash::{BuildHasherDefault, Hasher},
};
use hashbrown::HashSet;

#[derive(Default)]
pub struct IdentityHasher {
    value: u64,
}

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.value
    }

    fn write(&mut self, _: &[u8]) {
        panic!("IdentityHasher only supports usize");
    }

    fn write_usize(&mut self, value: usize) {
        self.value = value as u64;
    }
}

pub type UsizeSet = HashSet<usize, BuildHasherDefault<IdentityHasher>>;

pub struct CommittedCache;
pub struct CommitmentCache;
pub struct CommitmentKeyCache;
pub struct RandomnessCache;
