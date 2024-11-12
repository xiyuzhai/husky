use hex::encode;
use sealed::sealed;
use sha2::{Digest, Sha256, Sha512};
use std::hash::Hasher;

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Sha256Output(crypto_common::Output<Sha256>);

impl Sha256Output {
    pub fn hex(&self) -> String {
        hex::encode(&self.0)
    }
}

impl std::fmt::Debug for Sha256Output {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sha256Output(`{}`)", self.hex())
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Sha512Output(crypto_common::Output<Sha512>);

impl Sha512Output {
    pub fn hex(&self) -> String {
        hex::encode(&self.0)
    }
}

impl std::fmt::Debug for Sha512Output {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sha512Output(`{})`", self.hex())
    }
}

#[sealed]
pub trait ShaHash {
    fn sha256(&self) -> Sha256Output;
    fn sha512(&self) -> Sha512Output;
}

#[sealed]
impl<T: std::hash::Hash> ShaHash for T {
    fn sha256(&self) -> Sha256Output {
        let mut hasher: Sha256Hasher = Sha256Hasher::default();
        self.hash(&mut hasher);
        Sha256Output(hasher.0.finalize())
    }

    fn sha512(&self) -> Sha512Output {
        let mut hasher: Sha512Hasher = Sha512Hasher::default();
        self.hash(&mut hasher);
        Sha512Output(hasher.0.finalize())
    }
}

#[derive(Default)]
pub struct Sha256Hasher(Sha256);

impl Hasher for Sha256Hasher {
    fn finish(&self) -> u64 {
        // This is a simplification; you might want to handle this differently
        let result = self.0.clone().finalize();
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&result[..8]);
        u64::from_be_bytes(bytes)
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }
}

#[test]
fn test_sha256() {
    let input = b"hello world";
    let expected = "9fbc31964e86c79e0e3fffbcf8afafcedfbdd2a9e189cf93bdc608df5bcaa0a8";
    assert_eq!(input.sha256().hex(), expected);

    let input_vec = vec![1, 2, 3, 4, 5];
    let expected_vec = "268f9f97feb4c3a10c18abadc02f6db42d6c4cc1875f532bd293c749053274e2";
    assert_eq!(input_vec.sha256().hex(), expected_vec);
}

#[derive(Default)]
pub struct Sha512Hasher(Sha512);

impl Hasher for Sha512Hasher {
    fn finish(&self) -> u64 {
        // This is a simplification; you might want to handle this differently
        let result = self.0.clone().finalize();
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&result[..8]);
        u64::from_be_bytes(bytes)
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }
}

#[test]
fn test_sha512() {
    let input = b"hello world";
    let expected = "3c87bc935c66a8a5baa40bdbc8ae311bfdc659e3931353b1b0bd5419484a4c86161839ed8f0f3c299bf169211b68c7e8ddd8dee6aad79e85855ae9ada93c743a";
    assert_eq!(input.sha512().hex(), expected);

    let input_vec = vec![1, 2, 3, 4, 5];
    let expected_vec = "553177761401b5cfb10fb6a6444a7f9d3efd32f07892d3e2f8ea5d734b1e1612249a0d0a95062e0dc17bb89b8768bbd0f0f6d5247f56071d2770532bab8cbccc";
    assert_eq!(input_vec.sha512().hex(), expected_vec);
}

#[test]
fn sha2_works() {
    use hex_literal::hex;
    use sha2::{Digest, Sha256, Sha512};

    // create a Sha256 object
    let mut hasher = Sha256::new();

    // write input message
    hasher.update(b"hello world");

    // read hash digest and consume hasher
    let result = hasher.finalize();

    assert_eq!(
        result[..],
        hex!(
            "
    b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
"
        )[..]
    );

    // same for Sha512
    let mut hasher = Sha512::new();
    hasher.update(b"hello world");
    let result = hasher.finalize();

    assert_eq!(
        result[..],
        hex!(
            "
    309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f
    989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f
"
        )[..]
    );
}
