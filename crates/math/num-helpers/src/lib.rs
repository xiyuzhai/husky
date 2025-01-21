use num_bigint::BigInt;
use num_traits::{sign::Signed, *};

pub fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.abs();
    let mut b = b.abs();

    while !b.is_zero() {
        let t = b.clone();
        b = &a % &b;
        a = t;
    }

    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd() {
        assert_eq!(gcd(&BigInt::from(48), &BigInt::from(18)), BigInt::from(6));
        assert_eq!(gcd(&BigInt::from(54), &BigInt::from(24)), BigInt::from(6));
        assert_eq!(gcd(&BigInt::from(7), &BigInt::from(13)), BigInt::from(1));
        assert_eq!(gcd(&BigInt::from(-48), &BigInt::from(18)), BigInt::from(6));
        assert_eq!(gcd(&BigInt::from(0), &BigInt::from(5)), BigInt::from(5));
    }
}
