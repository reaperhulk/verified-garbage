import VerifiedGarbage.Spec.Sha256

/-!
# SHA-256 compression function: x86-64 implementation

`vg_sha256_compress(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`.

* The working variables `a … h` live in the low 32 bits of eight registers.
  Rather than moving them at the end of every round, the fully unrolled
  rounds rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is kept as a 16-word window `W[t mod 16]` in
  `scratch[0..64)`.
* `rbx, rbp, r12–r15` are saved in `scratch[64..112)` and restored on exit.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha256.X86_64

open VG.X86_64
open VG.Spec.Sha256 (K)

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
def slot (i : Nat) : MemOp := at_ .rcx (4 * (i % 16))

/-- Leave `Wₜ` in `T0` and in its slot. The additions are in the order of the
specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .mov32 T0 (.mem (at_ .rsi (4 * t))),
    .bswap32 T0,
    .store32 (slot t) T0]
  else [
    -- T0 := σ₁(Wₜ₋₂)
    .mov32 T1 (.mem (slot (t + 14))),
    .mov32 T0 (.reg T1),
    .shift32 .ror T0 2,
    .alu32 .xor T0 (.reg T1),
    .shift32 .ror T0 17,
    .shift32 .shr T1 10,
    .alu32 .xor T0 (.reg T1),
    -- T0 := T0 + Wₜ₋₇
    .alu32 .add T0 (.mem (slot (t + 9))),
    -- T0 := T0 + σ₀(Wₜ₋₁₅)
    .mov32 T1 (.mem (slot (t + 1))),
    .mov32 T2 (.reg T1),
    .shift32 .ror T2 11,
    .alu32 .xor T2 (.reg T1),
    .shift32 .ror T2 7,
    .shift32 .shr T1 3,
    .alu32 .xor T2 (.reg T1),
    .alu32 .add T0 (.reg T2),
    -- T0 := T0 + Wₜ₋₁₆
    .alu32 .add T0 (.mem (slot t)),
    .store32 (slot t) T0]

/-- Round `t`, with `Wₜ` in `T0`. The additions are in the order of the
specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Σ₁(e)
    .mov32 T1 (.reg e),
    .shift32 .ror T1 6,
    .mov32 T2 (.reg e),
    .shift32 .ror T2 11,
    .alu32 .xor T1 (.reg T2),
    .shift32 .ror T2 14,
    .alu32 .xor T1 (.reg T2),
    .alu32 .add h (.reg T1),
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .mov32 T1 (.reg f),
    .alu32 .xor T1 (.reg g),
    .alu32 .and T1 (.reg e),
    .alu32 .xor T1 (.reg g),
    .alu32 .add h (.reg T1),
    -- h := h + Kₜ + Wₜ, which is T₁
    .alu32 .add h (.imm (K t)),
    .alu32 .add h (.reg T0),
    -- e' := d + T₁
    .alu32 .add d (.reg h),
    -- h := h + Σ₀(a)
    .mov32 T1 (.reg a),
    .shift32 .ror T1 2,
    .mov32 T2 (.reg a),
    .shift32 .ror T2 13,
    .alu32 .xor T1 (.reg T2),
    .shift32 .ror T2 9,
    .alu32 .xor T1 (.reg T2),
    .alu32 .add h (.reg T1),
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .mov32 T1 (.reg a),
    .alu32 .or T1 (.reg b),
    .alu32 .and T1 (.reg c),
    .mov32 T2 (.reg a),
    .alu32 .and T2 (.reg b),
    .alu32 .or T1 (.reg T2),
    .alu32 .add h (.reg T1)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 64), (.rbp, 72), (.r12, 80), (.r13, 88), (.r14, 96), (.r15, 104)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).map fun k => .mov32 (var 0 k) (.mem (at_ .rdi (4 * k)))

/-- Add the working variables into the hash value. -/
def update : List Instr :=
  (List.range 8).map (fun k => .alu32 .add (var 0 k) (.mem (at_ .rdi (4 * k)))) ++
  (List.range 8).map (fun k => .store32 (at_ .rdi (4 * k)) (var 0 k))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha256.X86_64
