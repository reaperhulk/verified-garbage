//! SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4).
//!
//! All four share the compression function, the verified assembly primitive
//! `vg_sha512_compress` (contract `VG.Spec.Sha512.compressX86_64`); this
//! module adds the initial hash values (§5.3.4–§5.3.6), buffering, padding
//! (§5.1.2) and output truncation (§6.4–§6.7) around it.

/// The initial hash value `H⁽⁰⁾` of SHA-384 (FIPS 180-4 §5.3.4).
const H0_384: [u64; 8] = [
    0xcbbb9d5dc1059ed8,
    0x629a292a367cd507,
    0x9159015a3070dd17,
    0x152fecd8f70e5939,
    0x67332667ffc00b31,
    0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7,
    0x47b5481dbefa4fa4,
];

/// The initial hash value `H⁽⁰⁾` of SHA-512 (FIPS 180-4 §5.3.5).
const H0_512: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// The initial hash value `H⁽⁰⁾` of SHA-512/224 (FIPS 180-4 §5.3.6.1).
const H0_512_224: [u64; 8] = [
    0x8c3d37c819544da2,
    0x73e1996689dcd4d6,
    0x1dfab7ae32ff9c82,
    0x679dd514582f9fcf,
    0x0f6d2b697bd44da8,
    0x77e36f7304c48942,
    0x3f9d85a86a1d36c8,
    0x1112e6ad91d692a1,
];

/// The initial hash value `H⁽⁰⁾` of SHA-512/256 (FIPS 180-4 §5.3.6.2).
const H0_512_256: [u64; 8] = [
    0x22312194fc2bf72c,
    0x9f555fa3c84c64c2,
    0x2393b86b6f53b151,
    0x963877195940eabd,
    0x96283ee2a88effe3,
    0xbe5e1e2553863992,
    0x2b0199fc2c85b8aa,
    0x0eb72ddc81c52ca2,
];

/// The size of a message block, in bytes.
const BLOCK_SIZE: usize = 128;

/// Updates `state` with every 128-byte block of `blocks` (whose length must
/// be a multiple of 128).
fn compress(state: &mut [u64; 8], blocks: &[u8]) {
    debug_assert_eq!(blocks.len() % BLOCK_SIZE, 0);
    let mut scratch = [0u64; 22];
    // SAFETY: `state` is valid for reads and writes of 64 bytes, `blocks` for
    // reads of `128 * (blocks.len() / 128)` bytes and `scratch` for reads and
    // writes of 176 bytes; they are distinct objects, so they do not overlap
    // each other or the return address.
    unsafe {
        crate::asm::x86_64::sha512::vg_sha512_compress(
            state,
            blocks.as_ptr(),
            blocks.len() / BLOCK_SIZE,
            &mut scratch,
        )
    }
}

/// The computation shared by the four functions, which differ only in the
/// initial hash value and in how much of the final hash value they output.
#[derive(Clone)]
struct Core {
    state: [u64; 8],
    buffer: [u8; BLOCK_SIZE],
    buffered: usize,
    /// The message length so far, in bytes (modulo 2¹²⁸).
    length: u128,
}

impl Core {
    fn new(h0: [u64; 8]) -> Self {
        Core {
            state: h0,
            buffer: [0; BLOCK_SIZE],
            buffered: 0,
            length: 0,
        }
    }

    fn update(&mut self, mut data: &[u8]) {
        self.length = self.length.wrapping_add(data.len() as u128);
        if self.buffered > 0 {
            let take = (BLOCK_SIZE - self.buffered).min(data.len());
            self.buffer[self.buffered..self.buffered + take].copy_from_slice(&data[..take]);
            self.buffered += take;
            data = &data[take..];
            if self.buffered < BLOCK_SIZE {
                return;
            }
            compress(&mut self.state, &self.buffer);
            self.buffered = 0;
        }
        let whole = data.len() - data.len() % BLOCK_SIZE;
        compress(&mut self.state, &data[..whole]);
        let rest = &data[whole..];
        self.buffer[..rest.len()].copy_from_slice(rest);
        self.buffered = rest.len();
    }

    /// Pads the message (FIPS 180-4 §5.1.2) and returns the final hash value
    /// `H⁽ᴺ⁾` as 64 big-endian bytes.
    fn finalize(mut self) -> [u8; 64] {
        let bits = self.length.wrapping_mul(8);
        // `0x80`, then zeros up to 112 bytes modulo 128, then the length.
        let zeros = (239 - self.buffered) % BLOCK_SIZE;
        let mut padding = [0u8; 144];
        padding[0] = 0x80;
        padding[1 + zeros..17 + zeros].copy_from_slice(&bits.to_be_bytes());
        self.update(&padding[..17 + zeros]);
        debug_assert_eq!(self.buffered, 0);
        let mut out = [0u8; 64];
        for (chunk, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(self.state) {
            *chunk = word.to_be_bytes();
        }
        out
    }
}

/// Defines a public hash function: `$h0` is its initial hash value and its
/// digest is the first `$n` bytes of the final hash value.
macro_rules! sha512_variant {
    ($(#[$doc:meta])* $name:ident, $h0:expr, $n:literal) => {
        $(#[$doc])*
        ///
        /// Messages are limited to 2¹²⁵ − 1 bytes (2¹²⁸ − 1 bits), as in
        /// FIPS 180-4.
        #[derive(Clone)]
        pub struct $name(Core);

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $n;
            /// The size of a message block, in bytes.
            pub const BLOCK_SIZE: usize = BLOCK_SIZE;

            /// Starts a new computation.
            pub fn new() -> Self {
                $name(Core::new($h0))
            }

            /// Absorbs `data`.
            pub fn update(&mut self, data: &[u8]) {
                self.0.update(data)
            }

            /// Pads the message (FIPS 180-4 §5.1.2) and returns its digest.
            pub fn finalize(self) -> [u8; $n] {
                let mut digest = [0u8; $n];
                digest.copy_from_slice(&self.0.finalize()[..$n]);
                digest
            }

            /// The digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; $n] {
                let mut h = Self::new();
                h.update(data);
                h.finalize()
            }
        }
    };
}

sha512_variant!(
    /// An incremental SHA-384 computation (FIPS 180-4 §6.5).
    Sha384,
    H0_384,
    48
);
sha512_variant!(
    /// An incremental SHA-512 computation (FIPS 180-4 §6.4).
    Sha512,
    H0_512,
    64
);
sha512_variant!(
    /// An incremental SHA-512/224 computation (FIPS 180-4 §6.6).
    Sha512_224,
    H0_512_224,
    28
);
sha512_variant!(
    /// An incremental SHA-512/256 computation (FIPS 180-4 §6.7).
    Sha512_256,
    H0_512_256,
    32
);

#[cfg(test)]
mod tests {
    use super::{Core, H0_512, Sha384, Sha512, Sha512_224, Sha512_256};

    fn hex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    const TWO_BLOCK: &[u8] = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

    /// The FIPS 180-4 examples, the empty message and one million `a`s.
    #[test]
    fn known_answers_sha384() {
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b",
            ),
            (
                b"abc",
                "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7",
            ),
            (
                TWO_BLOCK,
                "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039",
            ),
        ];
        for (msg, digest) in cases {
            assert_eq!(Sha384::digest(msg), hex::<48>(digest));
        }
        let mut h = Sha384::default();
        for _ in 0..1000 {
            h.update(&[b'a'; 1000]);
        }
        assert_eq!(
            h.finalize(),
            hex::<48>(
                "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985"
            )
        );
        assert_eq!(Sha384::OUTPUT_SIZE, 48);
        assert_eq!(Sha384::BLOCK_SIZE, 128);
    }

    /// The FIPS 180-4 examples, the empty message and one million `a`s.
    #[test]
    fn known_answers_sha512() {
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
            ),
            (
                b"abc",
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
            ),
            (
                TWO_BLOCK,
                "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
            ),
        ];
        for (msg, digest) in cases {
            assert_eq!(Sha512::digest(msg), hex::<64>(digest));
        }
        let mut h = Sha512::default();
        for _ in 0..1000 {
            h.update(&[b'a'; 1000]);
        }
        assert_eq!(
            h.finalize(),
            hex::<64>(
                "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b"
            )
        );
        assert_eq!(Sha512::OUTPUT_SIZE, 64);
        assert_eq!(Sha512::BLOCK_SIZE, 128);
    }

    /// The FIPS 180-4 examples, the empty message and one million `a`s.
    #[test]
    fn known_answers_sha512_224() {
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "6ed0dd02806fa89e25de060c19d3ac86cabb87d6a0ddd05c333b84f4",
            ),
            (
                b"abc",
                "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa",
            ),
            (
                TWO_BLOCK,
                "23fec5bb94d60b23308192640b0c453335d664734fe40e7268674af9",
            ),
        ];
        for (msg, digest) in cases {
            assert_eq!(Sha512_224::digest(msg), hex::<28>(digest));
        }
        let mut h = Sha512_224::default();
        for _ in 0..1000 {
            h.update(&[b'a'; 1000]);
        }
        assert_eq!(
            h.finalize(),
            hex::<28>("37ab331d76f0d36de422bd0edeb22a28accd487b7a8453ae965dd287")
        );
        assert_eq!(Sha512_224::OUTPUT_SIZE, 28);
        assert_eq!(Sha512_224::BLOCK_SIZE, 128);
    }

    /// The FIPS 180-4 examples, the empty message and one million `a`s.
    #[test]
    fn known_answers_sha512_256() {
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a",
            ),
            (
                b"abc",
                "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23",
            ),
            (
                TWO_BLOCK,
                "3928e184fb8690f840da3988121d31be65cb9d3ef83ee6146feac861e19b563a",
            ),
        ];
        for (msg, digest) in cases {
            assert_eq!(Sha512_256::digest(msg), hex::<32>(digest));
        }
        let mut h = Sha512_256::default();
        for _ in 0..1000 {
            h.update(&[b'a'; 1000]);
        }
        assert_eq!(
            h.finalize(),
            hex::<32>("9a59a052930187a97038cae692f30708aa6491923ef5194394dc68d56c74fb21")
        );
        assert_eq!(Sha512_256::OUTPUT_SIZE, 32);
        assert_eq!(Sha512_256::BLOCK_SIZE, 128);
    }

    /// Every way of splitting a message into two updates gives the same
    /// hash value, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let mut h = Core::new(H0_512);
            h.update(&msg[..len]);
            let expected = h.finalize();
            for split in (0..=len).step_by(3) {
                let mut h = Core::new(H0_512);
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }
}
