fn main(input: pub [u8; 32]) -> pub [u8; 32] {
    std::hash::blake3(input)
}
