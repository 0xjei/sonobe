fn main(state: pub [u32; 8]) -> pub [u32; 8] {
    let message: [u32; 16] = [0; 16];
    std::hash::sha256_compression(message, state)
}
