//! NIST CAVP (<https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program>)
//! known-answer tests.
//!
//! The response files are vendored under `vectors/nist-cavp/` (see
//! `vectors/sources.toml` for where each one comes from) and compiled into
//! the test binary, so these tests always run. Every vector of every file is
//! checked.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::sha256::Sha256;

/// The `key = value` lines of a CAVP response file, in order, without the
/// comments, blank lines and `[L = ...]` section headers.
fn fields(text: &str) -> Vec<(&str, &str)> {
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#') && !l.starts_with('['))
        .map(|l| l.split_once(" = ").unwrap())
        .collect()
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Checks every `Len`/`Msg`/`MD` vector of a message test file for a hash
/// function `digest` with `N`-byte digests, and returns how many there were.
fn check_messages<const N: usize>(text: &str, digest: fn(&[u8]) -> [u8; N]) -> usize {
    assert!(text.contains(&format!("[L = {N}]")));
    let fields = fields(text);
    assert_eq!(fields.len() % 3, 0);
    for v in fields.chunks(3) {
        assert_eq!([v[0].0, v[1].0, v[2].0], ["Len", "Msg", "MD"]);
        // `Len` is in bits; the zero-length message is written as `Msg = 00`.
        let len: usize = v[0].1.parse().unwrap();
        assert_eq!(len % 8, 0);
        let msg = unhex(v[1].1);
        assert_eq!(digest(&msg[..len / 8])[..], unhex(v[2].1));
    }
    fields.len() / 3
}

/// The SHAVS Monte Carlo test of a hash function `digest` with `N`-byte
/// digests: 100 checkpoints, each after 1000 iterations of hashing the
/// concatenation of the previous three digests.
fn check_monte_carlo<const N: usize>(text: &str, digest: fn(&[u8]) -> [u8; N]) {
    assert!(text.contains(&format!("[L = {N}]")));
    let fields = fields(text);
    assert_eq!(fields[0].0, "Seed");
    let mut seed: [u8; N] = unhex(fields[0].1).try_into().unwrap();
    let checkpoints = &fields[1..];
    assert_eq!(checkpoints.len(), 2 * 100);
    for (j, v) in checkpoints.chunks(2).enumerate() {
        assert_eq!([v[0].0, v[1].0], ["COUNT", "MD"]);
        assert_eq!(v[0].1, j.to_string());
        let mut md = [seed; 3];
        for _ in 3..1003 {
            md = [md[1], md[2], digest(&md.concat())];
        }
        seed = md[2];
        assert_eq!(seed[..], unhex(v[1].1));
    }
}

/// Every message length from 0 to 64 bytes.
#[test]
fn sha256_short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha256/SHA256ShortMsg.rsp"),
        Sha256::digest,
    );
    assert_eq!(n, 65);
}

#[test]
fn sha256_long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha256/SHA256LongMsg.rsp"),
        Sha256::digest,
    );
    assert_eq!(n, 64);
}

/// The SHAVS Monte Carlo test.
#[test]
fn sha256_monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha256/SHA256Monte.rsp"),
        Sha256::digest,
    );
}

/// SHA-384, SHA-512, SHA-512/224 and SHA-512/256: for each, every message
/// length from 0 to 128 bytes, 128 long messages (from 227 to 12800 bytes)
/// and the Monte Carlo test.
#[cfg(target_arch = "x86_64")]
mod sha512 {
    use super::{check_messages, check_monte_carlo};
    use verified_garbage::sha512::{Sha384, Sha512, Sha512_224, Sha512_256};

    macro_rules! cavp {
        ($name:ident, $hash:ident, $file:literal) => {
            mod $name {
                use super::*;

                #[test]
                fn short_messages() {
                    let n = check_messages(
                        include_str!(concat!(
                            "../../vectors/nist-cavp/sha512/",
                            $file,
                            "ShortMsg.rsp"
                        )),
                        $hash::digest,
                    );
                    assert_eq!(n, 129);
                }

                #[test]
                fn long_messages() {
                    let n = check_messages(
                        include_str!(concat!(
                            "../../vectors/nist-cavp/sha512/",
                            $file,
                            "LongMsg.rsp"
                        )),
                        $hash::digest,
                    );
                    assert_eq!(n, 128);
                }

                #[test]
                fn monte_carlo() {
                    check_monte_carlo(
                        include_str!(concat!(
                            "../../vectors/nist-cavp/sha512/",
                            $file,
                            "Monte.rsp"
                        )),
                        $hash::digest,
                    );
                }
            }
        };
    }

    cavp!(sha384, Sha384, "SHA384");
    cavp!(sha512, Sha512, "SHA512");
    cavp!(sha512_224, Sha512_224, "SHA512_224");
    cavp!(sha512_256, Sha512_256, "SHA512_256");
}
