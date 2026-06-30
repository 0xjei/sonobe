fn main(state: pub [u64; 25]) -> pub [u64; 25] {
    std::hash::keccakf1600(state)
}
