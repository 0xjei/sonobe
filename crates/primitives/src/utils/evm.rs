pub trait EVMSerialize {
    fn to_calldata(&self) -> Vec<u8>;
}

impl<T: EVMSerialize> EVMSerialize for [T] {
    fn to_calldata(&self) -> Vec<u8> {
        self.iter().flat_map(EVMSerialize::to_calldata).collect()
    }
}

impl EVMSerialize for u8 {
    fn to_calldata(&self) -> Vec<u8> {
        vec![*self]
    }
}
