import VerifiedGarbage.Spec.Sha512

/-!
# Known-answer tests for the SHA-512 family specification

For each function, the one-block ("abc") and two-block examples of FIPS 180-4
(NIST's "Cryptographic Standards and Guidelines: Examples with Intermediate
Values") and the empty message, plus 111- and 112-byte messages (the longest
whose padding fits in one block, and the shortest that needs a second),
checked against `VG.Spec.Sha512`, so that a transcription error in the spec
shows up here. The initial hash values of SHA-512/224 and SHA-512/256 are also
checked against the generation function of §5.3.6.
-/

namespace VG.Test.Sha512

open Spec.Sha512

def hex (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let d (n : Nat) := Nat.digitChar n
    s!"{d (b.toNat / 16)}{d (b.toNat % 16)}")

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The two-block example message. -/
def two : String :=
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

#guard hex (sha384 (ascii "abc")) ==
  "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
#guard hex (sha384 []) ==
  "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
#guard hex (sha384 (ascii two)) ==
  "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039"
#guard hex (sha384 (List.replicate 111 0x61)) ==
  "3c37955051cb5c3026f94d551d5b5e2ac38d572ae4e07172085fed81f8466b8f90dc23a8ffcdea0b8d8e58e8fdacc80a"
#guard hex (sha384 (List.replicate 112 0x61)) ==
  "187d4e07cb306103c69967bf544d0dfbe9042577599c73c330abc0cb64c61236d5ed565ee19119d8c31779a38f791fcd"
#guard hex (sha512 (ascii "abc")) ==
  "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
#guard hex (sha512 []) ==
  "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#guard hex (sha512 (ascii two)) ==
  "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
#guard hex (sha512 (List.replicate 111 0x61)) ==
  "fa9121c7b32b9e01733d034cfc78cbf67f926c7ed83e82200ef86818196921760b4beff48404df811b953828274461673c68d04e297b0eb7b2b4d60fc6b566a2"
#guard hex (sha512 (List.replicate 112 0x61)) ==
  "c01d080efd492776a1c43bd23dd99d0a2e626d481e16782e75d54c2503b5dc32bd05f0f1ba33e568b88fd2d970929b719ecbb152f58f130a407c8830604b70ca"
#guard hex (sha512_224 (ascii "abc")) ==
  "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa"
#guard hex (sha512_224 []) ==
  "6ed0dd02806fa89e25de060c19d3ac86cabb87d6a0ddd05c333b84f4"
#guard hex (sha512_224 (ascii two)) ==
  "23fec5bb94d60b23308192640b0c453335d664734fe40e7268674af9"
#guard hex (sha512_224 (List.replicate 111 0x61)) ==
  "3ebe1b48e8c66acb9ae014db95b4bec93de7e9572bff41cf566bd7d0"
#guard hex (sha512_224 (List.replicate 112 0x61)) ==
  "79b41fef2a0439d2705724a67615f7bcbcd2bf5664a7774b80818eb6"
#guard hex (sha512_256 (ascii "abc")) ==
  "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"
#guard hex (sha512_256 []) ==
  "c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a"
#guard hex (sha512_256 (ascii two)) ==
  "3928e184fb8690f840da3988121d31be65cb9d3ef83ee6146feac861e19b563a"
#guard hex (sha512_256 (List.replicate 111 0x61)) ==
  "0239e429f98d0ed61ee8e2a7c30afe98c1c3a80ce5dff62a107e9c538f7632ce"
#guard hex (sha512_256 (List.replicate 112 0x61)) ==
  "9216b5303edb66504570bee90e48ea5beaa5e9fe9f760bbd3e0460559fc005f6"

/-- §5.3.6: the initial hash value of SHA-512/t is the SHA-512 hash, starting
from `H0_512` with each word XORed with `a5a5a5a5a5a5a5a5`, of the ASCII
string "SHA-512/t". -/
def ivGen (t : String) : List Byte :=
  finalHash (H0_512.map (· ^^^ 0xa5a5a5a5a5a5a5a5)) (ascii s!"SHA-512/{t}")

#guard ivGen "224" == H0_512_224.toList.flatMap wordBytes
#guard ivGen "256" == H0_512_256.toList.flatMap wordBytes

end VG.Test.Sha512
