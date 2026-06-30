fn main(io: pub [u8; 2]) -> pub [u8; 2] {
    let c = io[0] & io[1];
    let d = io[0] ^ io[1];
    [c, d]
}
