import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Proof.Selftest.X86_64
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Update
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Update
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Finalize

/-!
# The artifact registry

**The single entry point.** Every function emitted into the Rust crate is an
entry of `artifacts`, and `Emit.lean` emits exactly this list. An
`Artifact` bundles

* the target and the Rust name and signature of the function,
* the implementation (`Impl/`),
* the contract it satisfies (`Spec/`), and
* the proof of `Verified` for them (`Proof/`),

so nothing can be emitted without a proof. The `#assert_standard_axioms`
check below then ensures none of those proofs relies on `sorry`,
`native_decide` or any axiom beyond Lean's standard three.

To add a function: write its spec and contract under `Spec/`, the code under
`Impl/`, the proof under `Proof/`, and append an entry here. Then run
`lake build && lake env lean --run Emit.lean` (in `lean/`) and commit the
regenerated `src/asm/`.

**Review note**: `rustSig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "selftest"
    name := "vg_selftest_add"
    rustSig := "(a: u64, b: u64) -> u64"
    doc := "Pipeline self-test: returns `a.wrapping_add(b)`.\n\n\
      Contract: `VG.Spec.Selftest.addX86_64`. No safety requirements."
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addX86_64
    verified := Proof.Selftest.X86_64.add_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_compress"
    rustSig := "(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])"
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressX86_64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.compress
    contract := Spec.Sha256.compressX86_64
    verified := Proof.Sha256.X86_64.compress_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_init"
    rustSig := "(state: *mut [u8; 96])"
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initX86_64`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not overlap the return address on the stack (a Rust object never does)."
    code := Impl.Sha256.X86_64.Stream.init
    contract := Spec.Sha256.initX86_64
    verified := Proof.Sha256.X86_64.Stream.init_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_update"
    rustSig := "(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])"
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateX86_64`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.update
    contract := Spec.Sha256.updateX86_64
    verified := Proof.Sha256.X86_64.Stream.Update.update_verified },
  { target := X86_64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    rustSig := "(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])"
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeX86_64`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha256.X86_64.Stream.finalize
    contract := Spec.Sha256.finalizeX86_64
    verified := Proof.Sha256.X86_64.Stream.Finalize.finalize_verified },
  { target := X86_64.target
    module := "sha512"
    name := "vg_sha512_compress"
    rustSig := "(state: *mut [u64; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 22])"
    doc := "The SHA-512 compression function (FIPS 180-4 §6.4.2), shared by SHA-384, SHA-512, \
      SHA-512/224 and SHA-512/256: updates the hash value `*state` with the `n` 128-byte \
      blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha512.compressX86_64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 64 bytes.\n\
      * `blocks` must be valid for reads of `128 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 176 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, nor the return address on the \
      stack (distinct Rust objects never do)."
    code := Impl.Sha512.X86_64.compress
    contract := Spec.Sha512.compressX86_64
    verified := Proof.Sha512.X86_64.compress_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_compress"
    rustSig := "(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])"
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressAArch64`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.compress
    contract := Spec.Sha256.compressAArch64
    verified := Proof.Sha256.AArch64.compress_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_init"
    rustSig := "(state: *mut [u8; 96])"
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initAArch64`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes."
    code := Impl.Sha256.AArch64.Stream.init
    contract := Spec.Sha256.initAArch64
    verified := Proof.Sha256.AArch64.Stream.init_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_update"
    rustSig := "(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])"
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateAArch64`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.Stream.update
    contract := Spec.Sha256.updateAArch64
    verified := Proof.Sha256.AArch64.Stream.Update.update_verified },
  { target := AArch64.target
    module := "sha256"
    name := "vg_sha256_finalize"
    rustSig := "(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])"
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeAArch64`. Constant time: only the pointers and \
      `count` may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other."
    code := Impl.Sha256.AArch64.Stream.finalize
    contract := Spec.Sha256.finalizeAArch64
    verified := Proof.Sha256.AArch64.Stream.Finalize.finalize_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_compress"
    rustSig := "(state: *mut [u32; 8], blocks: *const u8, n: usize, scratch: *mut [u64; 14])"
    doc := "The SHA-256 compression function (FIPS 180-4 §6.2.2): updates the hash value \
      `*state` with the `n` 64-byte blocks starting at `blocks`, in order.\n\n\
      Contract: `VG.Spec.Sha256.compressArm`. Constant time: only the pointers and `n` \
      may affect timing, not the hash value or the blocks.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 32 bytes.\n\
      * `blocks` must be valid for reads of `64 * n` bytes.\n\
      * `scratch` must be valid for reads and writes of 112 bytes; its contents on \
      return are unspecified.\n\
      * These three regions must not overlap each other, and none of them may wrap \
      around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.compress
    contract := Spec.Sha256.compressArm
    verified := Proof.Sha256.Arm.compress_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_init"
    rustSig := "(state: *mut [u8; 96])"
    doc := "Starts a SHA-256 computation: makes the streaming state `*state` represent the \
      empty message.\n\n\
      Contract: `VG.Spec.Sha256.initArm`. The streaming state is the hash value followed \
      by a buffered partial block (`VG.Spec.Sha256.Repr`).\n\n\
      # Safety\n\n\
      * `state` must be valid for writes of 96 bytes.\n\
      * It must not wrap around the end of the address space (no Rust object does)."
    code := Impl.Sha256.Arm.Stream.init
    contract := Spec.Sha256.initArm
    verified := Proof.Sha256.Arm.Stream.init_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_update"
    rustSig := "(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])"
    doc := "Absorbs data into a SHA-256 computation: if the streaming state `*state` represents \
      a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by \
      the `len` bytes at `data`.\n\n\
      Contract: `VG.Spec.Sha256.updateArm`. Constant time: only the pointers, `count` and \
      `len` may affect timing, not the state or the data.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes.\n\
      * `data` must be valid for reads of `len` bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.update
    contract := Spec.Sha256.updateArm
    verified := Proof.Sha256.Arm.Stream.Update.update_verified },
  { target := Arm.target
    module := "sha256"
    name := "vg_sha256_finalize"
    rustSig := "(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])"
    doc := "Finishes a SHA-256 computation: if the streaming state `*state` represents a \
      message of `count` bytes (modulo 2⁶⁴), writes the SHA-256 digest of that message to \
      `*out`.\n\n\
      Contract: `VG.Spec.Sha256.finalizeArm`. Constant time: only the pointers and `count` \
      may affect timing, not the state.\n\n\
      # Safety\n\n\
      * `state` must be valid for reads and writes of 96 bytes; its contents on return are \
      unspecified.\n\
      * `out` must be valid for writes of 32 bytes.\n\
      * `scratch` must be valid for reads and writes of 160 bytes; its contents on return \
      are unspecified.\n\
      * These three regions must not overlap each other, nor the arguments passed on the \
      stack, and none of them may wrap around the end of the address space (distinct Rust \
      objects never do)."
    code := Impl.Sha256.Arm.Stream.finalize
    contract := Spec.Sha256.finalizeArm
    verified := Proof.Sha256.Arm.Stream.Finalize.finalize_verified }
]

#assert_standard_axioms artifacts

end VG
