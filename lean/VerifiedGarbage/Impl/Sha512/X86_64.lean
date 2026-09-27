import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86_64.Target

/-!
# SHA-512 compression function: x86-64 implementation

`vg_sha512_compress(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`.

* The working variables `a … h` live in eight registers. Rather than moving
  them at the end of every round, the fully unrolled rounds rename them: in
  round `t`, variable `k` is in `var t k`.
* The message schedule is kept as a 16-word window `W[t mod 16]` in
  `scratch[0..128)`.
* `rbx, rbp, r12–r15` are saved in `scratch[128..176)` and restored on exit.
* `Kₜ` does not fit in a sign-extended 32-bit immediate, so it is loaded with
  `movabs` into a temporary.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha512.X86_64

open VG.X86_64
open VG.Spec.Sha512 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.rax, .rbx, .rbp, .r8, .r9, .r10, .r11, .r12]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .rax

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .r13
def T1 : Reg := .r14
def T2 : Reg := .r15

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : MemOp := at_ .rcx (8 * (i % 16))

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .mov T0 (.mem (at_ .rsi (8 * t))),
    .bswap T0,
    .store (slot t) T0]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .mov T1 (.mem (slot (t + 14))),
    .mov T0 (.reg T1),
    .shift .ror T0 42,
    .alu .xor T0 (.reg T1),
    .shift .ror T0 19,
    .shift .shr T1 6,
    .alu .xor T0 (.reg T1),
    -- T0 := T0 + Wₜ₋₇
    .alu .add T0 (.mem (slot (t + 9))),
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .mov T1 (.mem (slot (t + 1))),
    .mov T2 (.reg T1),
    .shift .ror T2 7,
    .alu .xor T2 (.reg T1),
    .shift .ror T2 1,
    .shift .shr T1 7,
    .alu .xor T2 (.reg T1),
    .alu .add T0 (.reg T2),
    -- T0 := T0 + Wₜ₋₁₆
    .alu .add T0 (.mem (slot t)),
    .store (slot t) T0]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .mov T1 (.reg e),
    .shift .ror T1 14,
    .mov T2 (.reg e),
    .shift .ror T2 18,
    .alu .xor T1 (.reg T2),
    .shift .ror T2 23,
    .alu .xor T1 (.reg T2),
    .alu .add h (.reg T1),
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .mov T1 (.reg f),
    .alu .xor T1 (.reg g),
    .alu .and T1 (.reg e),
    .alu .xor T1 (.reg g),
    .alu .add h (.reg T1),
    -- h := h + Kₜ + Wₜ, which is T₁
    .movImm64 T1 (K t),
    .alu .add h (.reg T1),
    .alu .add h (.reg T0),
    -- e' := d + T₁
    .alu .add d (.reg h),
    -- h := h + Σ₀(a)
    .mov T1 (.reg a),
    .shift .ror T1 28,
    .mov T2 (.reg a),
    .shift .ror T2 34,
    .alu .xor T1 (.reg T2),
    .shift .ror T2 5,
    .alu .xor T1 (.reg T2),
    .alu .add h (.reg T1),
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .mov T1 (.reg a),
    .alu .or T1 (.reg b),
    .alu .and T1 (.reg c),
    .mov T2 (.reg a),
    .alu .and T2 (.reg b),
    .alu .or T1 (.reg T2),
    .alu .add h (.reg T1)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 128), (.rbp, 136), (.r12, 144), (.r13, 152), (.r14, 160), (.r15, 168)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value (`80 % 8 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 8).map fun k => .mov (var 0 k) (.mem (at_ .rdi (8 * k)))

/-- Add the working variables into the hash value. -/
def update : List Instr :=
  (List.range 8).map (fun k => .alu .add (var 0 k) (.mem (at_ .rdi (8 * k)))) ++
  (List.range 8).map (fun k => .store (at_ .rdi (8 * k)) (var 0 k))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha512.X86_64
