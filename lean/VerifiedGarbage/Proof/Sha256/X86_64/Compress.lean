import VerifiedGarbage.Proof.Sha256.X86_64.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

/-!
# SHA-256 compression function on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86_64

open VG VG.X86_64 VG.Impl.Sha256.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 4 (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 =
    m.readW (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 112⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Spec.Sha256.compressX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_save {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((64 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((72 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((80 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((88 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((96 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((104 : Nat) : Int)) 64 = s₀.gpr .r15

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .rbx (.mem (at_ .rdi (4 * 1))),
    .mov32 .rbp (.mem (at_ .rdi (4 * 2))), .mov32 .r8 (.mem (at_ .rdi (4 * 3))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 4))), .mov32 .r10 (.mem (at_ .rdi (4 * 5))),
    .mov32 .r11 (.mem (at_ .rdi (4 * 6))), .mov32 .r12 (.mem (at_ .rdi (4 * 7)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .rbx (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .rbp (.mem (at_ .rdi (4 * 2))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 3))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 4))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 5))),
    .alu32 .add .r11 (.mem (at_ .rdi (4 * 6))), .alu32 .add .r12 (.mem (at_ .rdi (4 * 7))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .rbx,
    .store32 (at_ .rdi (4 * 2)) .rbp, .store32 (at_ .rdi (4 * 3)) .r8,
    .store32 (at_ .rdi (4 * 4)) .r9, .store32 (at_ .rdi (4 * 5)) .r10,
    .store32 (at_ .rdi (4 * 6)) .r11, .store32 (at_ .rdi (4 * 7)) .r12,
    .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
    s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
    s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
    s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64 := Iff.rfl

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp (config := {decide := true}) only [vars0, runBlock, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, State.setReg, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Eight 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofInt 64 ((4 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((4 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((4 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((4 * 3 : Nat) : Int)) v[3]).writeW
    (p + BitVec.ofInt 64 ((4 * 4 : Nat) : Int)) v[4]).writeW
    (p + BitVec.ofInt 64 ((4 * 5 : Nat) : Int)) v[5]).writeW
    (p + BitVec.ofInt 64 ((4 * 6 : Nat) : Int)) v[6]).writeW
    (p + BitVec.ofInt 64 ((4 * 7 : Nat) : Int)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  interval_cases k <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg, arithFlags,
    State.setFlags, hrdi, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], trivial⟩
  simp only [writeState, Vector.getElem_zipWith]

/-- A saved register's slot `⟨scr + d, 8⟩`. -/
theorem saveSlot_sub (p : Addr) {d : Nat} (hd : d + 8 ≤ 112) :
    Region.Sub ⟨p + BitVec.ofInt 64 (d : Int), 8⟩ ⟨p, 112⟩ := by
  rw [ofInt_natCast]; exact sub_offset hd (by omega)

theorem saveSlot_win (p : Addr) {d : Nat} (hd : 64 ≤ d) (hd' : d + 8 ≤ 112) :
    Region.Disjoint ⟨p + BitVec.ofInt 64 (d : Int), 8⟩ (winRegion p) := by
  intro a h₁ h₂
  simp only [Region.Contains, ofInt_natCast] at h₁ h₂
  bv_omega

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 64 ≤ d → d + 8 ≤ 112 →
      m'.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 = m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
    intro d hd hd'
    rcases hf with hf | hf
    · exact hf.readW (Region.contains_self _ _) (by simpa using saveSlot_win (scr s₀) hd hd') (by decide)
    · exact hf.readW (Region.contains_self _ _)
        (by simpa using Region.Disjoint.sub_left hp.st_scr.symm (saveSlot_sub (scr s₀) hd')) (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 64 (by omega) (by omega)).trans h1, (key 72 (by omega) (by omega)).trans h2,
    (key 80 (by omega) (by omega)).trans h3, (key 88 (by omega) (by omega)).trans h4,
    (key 96 (by omega) (by omega)).trans h5, (key 104 (by omega) (by omega)).trans h6⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    bswap32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) =
      W (blk s₀ i) t := by
  rw [W_lt _ ht, bswap32_readW, ofInt_natCast]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) by
      bv_omega]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 112⟩ := Region.sub_prefix (by omega)

set_option maxHeartbeats 400000 in
theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap32 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hrsi₁ : s₁.gpr .rsi = blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  have hrcx₁ : s₁.gpr .rcx = scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hrsi₁ hrcx₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 le_rfl)
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset' (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrcx₃, hrsp₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx]
    have := (s₀.gpr .rdx).isLt
    bv_omega
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrcx₃, pub₂ .rcx (by decide), hL.rcx],
      by rw [hrsp₃, pub₂ .rsp (by decide), hL.rsp], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₃]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon _ rfl with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₃, pub₂ .rsi (by decide), hL.rsi]
      simp only [blkAddr]
      bv_omega
    · rw [hrdx₃, hrdx]

/-! ## Prologue and epilogue -/

theorem save_eq : save ++ [.alu .test .rdx (.reg .rdx)] = [
    .store (at_ .rcx 64) .rbx, .store (at_ .rcx 72) .rbp, .store (at_ .rcx 80) .r12,
    .store (at_ .rcx 88) .r13, .store (at_ .rcx 96) .r14, .store (at_ .rcx 104) .r15,
    .alu .test .rdx (.reg .rdx)] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rcx 64)), .mov .rbp (.mem (at_ .rcx 72)), .mov .r12 (.mem (at_ .rcx 80)),
    .mov .r13 (.mem (at_ .rcx 88)), .mov .r14 (.mem (at_ .rcx 96)), .mov .r15 (.mem (at_ .rcx 104))] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((64 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((72 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((80 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((88 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((96 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((104 : Nat) : Int)) (s₀.gpr .r15)

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ [.alu .test .rdx (.reg .rdx)])) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  have o0 := hp.out_save (d := 64) (by omega); have o1 := hp.out_save (d := 72) (by omega)
  have o2 := hp.out_save (d := 80) (by omega); have o3 := hp.out_save (d := 88) (by omega)
  have o4 := hp.out_save (d := 96) (by omega); have o5 := hp.out_save (d := 104) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock, exec, execAlu, readSrc, isa, ea_at,
    State.store64, arithFlags, State.setFlags, o0, o1, o2, o3, o4, o5, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 112 →
      (scrR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 72 (by omega))).writeW (List.mem_singleton_self _) _
    (c 80 (by omega))).writeW (List.mem_singleton_self _) _ (c 88 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 96 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 104 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
      (by simpa using hp.st_scr)
      (by decide), ← stateAt_get _ _ hk]
    rfl

set_option maxHeartbeats 0 in
set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ Spec.Sha256.compressX86_64.post s₀ s' := by
  have i0 := hp.in_save (d := 64) (by omega); have i1 := hp.in_save (d := 72) (by omega)
  have i2 := hp.in_save (d := 80) (by omega); have i3 := hp.in_save (d := 88) (by omega)
  have i4 := hp.in_save (d := 96) (by omega); have i5 := hp.in_save (d := 104) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hc.saved
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  have hrsp := hc.rsp
  have hstate := hc.state
  have hrcx := hc.rcx
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hrcx, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · exact hret
  · exact hstate

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Sha256.X86_64.compress Spec.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by decide +kernel)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.X86_64
