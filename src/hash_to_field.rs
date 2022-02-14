use ark_ff::PrimeField;
use blake3::Hasher;
use std::{
    iter::repeat,
    ops::{Add, Div, Sub},
};

const K: u16 = 128;
///maps bytes to a field element with low bias
pub(crate) fn hash_to_field<F>(msg: &[u8]) -> F
where
    F: PrimeField,
{
    let len = ceil_div(F::size_in_bits(), 8) as u16;
    let len_bytes = len.to_le_bytes();

    let mut hasher = Hasher::new();
    let dst_prime = b"TODO";
    hasher.update(msg);
    hasher.update(&len_bytes);
    hasher.update(dst_prime);
    let mut reader = hasher.finalize_xof();
    let len = (len + K / 8) as usize;
    let mut bytes = repeat(0_u8).take(len).collect::<Vec<_>>();
    reader.fill(&mut *bytes);
    F::from_le_bytes_mod_order(&*bytes)
}

pub(crate) fn ceil_div<T>(a: T, b: T) -> T
where
    T: Div<Output = T> + Sub<Output = T> + Add<T, Output = T> + From<u8> + Copy,
{
    (a + b - T::from(1)) / b
}
