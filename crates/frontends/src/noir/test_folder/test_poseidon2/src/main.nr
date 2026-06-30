fn main(state: pub [Field; 4]) -> pub [Field; 4] {
    std::hash::poseidon2_permutation(state)
}
