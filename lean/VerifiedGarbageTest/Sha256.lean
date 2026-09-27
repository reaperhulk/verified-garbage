import VerifiedGarbage.Spec.Sha256

/-!
# Known-answer tests for the SHA-256 specification

The examples of FIPS 180-4 (from NIST's "Cryptographic Standards and
Guidelines: Examples with Intermediate Values"), checked against
`VG.Spec.Sha256.hash`, so that a transcription error in the spec shows up here.
-/

namespace VG.Test.Sha256

open Spec.Sha256

def hex (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let d (n : Nat) := Nat.digitChar n
    s!"{d (b.toNat / 16)}{d (b.toNat % 16)}")

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

#guard hex (hash (ascii "abc")) ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hex (hash []) ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hex (hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard hex (hash (ascii
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"

end VG.Test.Sha256
