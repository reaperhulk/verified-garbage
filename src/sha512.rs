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
    use super::{Sha384, Sha512, Sha512_224, Sha512_256};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha512::digest(&msg[..len]);
            for split in (0..=len).step_by(3) {
                let mut h = Sha512::default();
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

    /// The variants differ only in their initial hash value and output
    /// length, which the CAVP tests (`tests/cavp/`) check; here, that each
    /// digest is its computation's `finalize`.
    #[test]
    fn variants() {
        let msg = [0x5a; 300];
        for len in [0, 111, 112, 128, 300] {
            let mut h = Sha384::default();
            h.update(&msg[..len]);
            assert_eq!(h.finalize(), Sha384::digest(&msg[..len]));
            let mut h = Sha512_224::default();
            h.update(&msg[..len]);
            assert_eq!(h.finalize(), Sha512_224::digest(&msg[..len]));
            let mut h = Sha512_256::default();
            h.update(&msg[..len]);
            assert_eq!(h.finalize(), Sha512_256::digest(&msg[..len]));
        }
        assert_eq!(
            [
                Sha384::OUTPUT_SIZE,
                Sha512::OUTPUT_SIZE,
                Sha512_224::OUTPUT_SIZE,
                Sha512_256::OUTPUT_SIZE
            ],
            [48, 64, 28, 32]
        );
        assert_eq!(Sha512::BLOCK_SIZE, 128);
    }
}
