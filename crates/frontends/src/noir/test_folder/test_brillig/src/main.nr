// Field division emits an unconstrained (Brillig) inverse hint plus arithmetic
// constraints checking it.
fn main(io: pub [Field; 2]) -> pub [Field; 2] {
    let q = io[0] / io[1];
    let p = io[0] * io[1];
    [q, p]
}
