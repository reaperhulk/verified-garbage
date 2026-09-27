import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Taint tracking for x86-64

Untrusted: everything here is checked by Lean.

The abstract state is the list of registers known to be public, and whether
the (modelled) flags are public. Memory is always secret: a value loaded from
memory is secret, and an address must be computed from public registers.
-/

namespace VG.X86_64.Taint

structure T where
  regs : List Reg
  flags : Bool
  deriving DecidableEq

def pub (τ : T) (r : Reg) : Bool := τ.regs.contains r

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  (∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r) ∧
  (τ.flags = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : List Reg :=
  if p then r :: τ.regs else τ.regs.filter (· != r)

def memPub (τ : T) (m : MemOp) : Bool :=
  pub τ m.base && match m.index with
    | none => true
    | some i => pub τ i

/-- The addresses the operand accesses are public. -/
def srcOk (τ : T) : Src → Bool
  | .mem m => memPub τ m
  | _ => true

/-- The operand's value is public. -/
def srcPub (τ : T) : Src → Bool
  | .reg r => pub τ r
  | .imm _ => true
  | .mem _ => false

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

def aluStep (τ : T) (op : AluOp) (d : Reg) (src : Src) : Option T :=
  if srcOk τ src then
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    some ⟨if writes op then set τ d p else τ.regs, p⟩
  else none

def step (τ : T) : Instr → Option T
  | .mov d src | .mov32 d src =>
    if srcOk τ src then some ⟨set τ d (srcPub τ src), τ.flags⟩ else none
  | .store m _ | .store32 m _ => if memPub τ m then some τ else none
  | .alu op d src | .alu32 op d src => aluStep τ op d src
  -- The result is a function of the old value of `d`, and so are the
  -- flags that change.
  | .shift32 _ d _ => some ⟨τ.regs, τ.flags && pub τ d⟩
  | .bswap32 _ => some τ

def meet (τ₁ τ₂ : T) : T := ⟨τ₁.regs.filter (pub τ₂), τ₁.flags && τ₂.flags⟩

def le (τ σ : T) : Bool := τ.regs.all (pub σ) && (!τ.flags || σ.flags)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := by
  simp [pub]

section
variable {τ : T} {s₁ s₂ : State}

theorem Agree.reg (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) : s₁.gpr r = s₂.gpr r :=
  h.1 r (pub_iff.mp hr)

theorem Agree.ea (h : Agree τ s₁ s₂) {m : MemOp} (hm : memPub τ m = true) : s₁.ea m = s₂.ea m := by
  simp only [memPub, Bool.and_eq_true] at hm
  obtain ⟨hb, hi⟩ := hm
  unfold State.ea
  split <;> rename_i heq <;> rw [heq] at hi <;> simp only at hi
  · rw [h.reg hb]
  · rw [h.reg hb, h.reg hi]

theorem Agree.srcAddrs (h : Agree τ s₁ s₂) {src : Src} (hs : srcOk τ src = true) :
    X86_64.srcAddrs s₁ src = X86_64.srcAddrs s₂ src := by
  cases src <;> simp only [X86_64.srcAddrs]
  simp only [srcOk] at hs
  rw [h.ea hs]

theorem Agree.readSrc (h : Agree τ s₁ s₂) {src : Src} (hs : srcPub τ src = true) :
    readSrc s₁ src = readSrc s₂ src := by
  cases src with
  | reg r => exact congrArg some (h.reg hs)
  | imm v => rfl
  | mem m => simp [srcPub] at hs

theorem Agree.readSrc32 (h : Agree τ s₁ s₂) {src : Src} (hs : srcPub τ src = true) :
    readSrc32 s₁ src = readSrc32 s₂ src := by
  cases src with
  | reg r => exact congrArg (fun x => some (BitVec.setWidth 32 x)) (h.reg hs)
  | imm v => rfl
  | mem m => simp [srcPub] at hs

end

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    ∀ r ∈ set τ d p, (s₁.setReg d v₁).gpr r = (s₂.setReg d v₂).gpr r := by
  intro r hr
  simp only [State.setReg]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, List.mem_cons] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, List.mem_filter, bne_iff_ne, ne_eq] at hr
    simp [hr.2, h r hr.1]

/-! ### ALU instructions, uniformly -/

/-- The result, carry and overflow of an ALU operation at width `w`. -/
def aluOut {w : Nat} (op : AluOp) (a b : BitVec w) (cf : Option Bool) :
    Option (BitVec w × Bool × Bool) :=
  match op with
  | .add => let r := a + b; some (r, 2 ^ w ≤ a.toNat + b.toNat, addOverflow a b r)
  | .adc => cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth w
    (r, 2 ^ w ≤ a.toNat + b.toNat + c.toNat, addOverflow a b r)
  | .sub | .cmp => let r := a - b; some (r, a.toNat < b.toNat, subOverflow a b r)
  | .sbb => cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth w
    (r, a.toNat < b.toNat + c.toNat, subOverflow a b r)
  | .and | .test => some (a &&& b, false, false)
  | .or => some (a ||| b, false, false)
  | .xor => some (a ^^^ b, false, false)

theorem aluOut_cf {w : Nat} {op : AluOp} (h : usesCarry op = false) (a b : BitVec w)
    (c c' : Option Bool) : aluOut op a b c = aluOut op a b c' := by
  cases op <;> simp_all [usesCarry, aluOut]

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (readSrc s src).bind fun b =>
      (aluOut op (s.gpr d) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg d r else arithFlags s r c o := by
  cases op <;> simp [execAlu, aluOut, writes, Function.comp_def]

theorem execAlu32_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu32 op d src s = (readSrc32 s src).bind fun b =>
      (aluOut op ((s.gpr d).setWidth 32) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg32 d r else arithFlags s r c o := by
  cases op <;> simp [execAlu32, aluOut, writes, Function.comp_def]

section
variable {s : State} {r : Reg} {w : Nat} {v : BitVec 64} {x : BitVec w} {c o : Bool}
@[simp] theorem arithFlags_gpr : (arithFlags s x c o).gpr = s.gpr := rfl
@[simp] theorem arithFlags_cf : (arithFlags s x c o).cf = some c := rfl
@[simp] theorem arithFlags_of : (arithFlags s x c o).of = some o := rfl
@[simp] theorem arithFlags_zf : (arithFlags s x c o).zf = some (x == 0) := rfl
@[simp] theorem arithFlags_sf : (arithFlags s x c o).sf = some x.msb := rfl
@[simp] theorem setReg_cf : (s.setReg r v).cf = s.cf := rfl
@[simp] theorem setReg_of : (s.setReg r v).of = s.of := rfl
@[simp] theorem setReg_zf : (s.setReg r v).zf = s.zf := rfl
@[simp] theorem setReg_sf : (s.setReg r v).sf = s.sf := rfl
end

theorem regs_filter {τ : T} {s₁ s₂ s₁' s₂' : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} (h₁ : ∀ r, r ≠ d → s₁'.gpr r = s₁.gpr r) (h₂ : ∀ r, r ≠ d → s₂'.gpr r = s₂.gpr r) :
    ∀ r ∈ τ.regs.filter (· != d), s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hr
  rw [h₁ r hr.2, h₂ r hr.2, h r hr.1]

theorem not_pub_set {τ : T} {d : Reg} {p : Bool} (hp : ¬ p = true) : set τ d p = τ.regs.filter (· != d) := by
  simp [set, hp]

/-- ALU soundness, for both widths: `wr` writes the result register. -/
theorem alu_sound {w : Nat} {τ : T} {op : AluOp} {d : Reg} {src : Src} {s₁ s₂ : State}
    {b₁ b₂ : BitVec w} {out₁ out₂ : BitVec w × Bool × Bool}
    (ha : Agree τ s₁ s₂) (get : State → BitVec w) (wr : State → BitVec w → State)
    (hget : s₁.gpr d = s₂.gpr d → get s₁ = get s₂)
    (hwr : ∀ s x r, (wr s x).gpr r = if r = d then (wr s x).gpr d else s.gpr r)
    (hwrd : ∀ s₁ s₂ x, (wr s₁ x).gpr d = (wr s₂ x).gpr d)
    (hwrf : ∀ s x, (wr s x).cf = s.cf ∧ (wr s x).zf = s.zf ∧ (wr s x).sf = s.sf ∧ (wr s x).of = s.of)
    (hb : srcPub τ src = true → b₁ = b₂)
    (ho₁ : aluOut op (get s₁) b₁ s₁.cf = some out₁) (ho₂ : aluOut op (get s₂) b₂ s₂.cf = some out₂) :
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    Agree ⟨if writes op then set τ d p else τ.regs, p⟩
      (if writes op then wr (arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2) out₁.1
        else arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2)
      (if writes op then wr (arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) out₂.1
        else arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) := by
  intro p
  by_cases hp : p = true
  · have hp' := hp
    simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp'
    obtain ⟨⟨hd, hsp⟩, hc⟩ := hp'
    obtain rfl := hb hsp
    have hout : aluOut op (get s₁) b₁ s₁.cf = aluOut op (get s₂) b₁ s₂.cf := by
      rw [hget (ha.reg hd)]
      rcases hc with hc | hc
      · exact aluOut_cf hc _ _ _ _
      · rw [(ha.2 hc).1]
    rw [hout, ho₂] at ho₁
    cases ho₁
    refine ⟨fun r hr => ?_, fun _ => ?_⟩
    · split
      · rename_i hw
        simp only [hw, ite_true] at hr
        rw [hwr _ _ r, hwr (arithFlags s₂ _ _ _) _ r]
        split
        · exact hwrd _ _ _
        · rename_i hrd
          simp only [set, hp, ite_true, List.mem_cons, hrd, false_or] at hr
          simpa using ha.1 r hr
      · rename_i hw
        simp only [hw, Bool.false_eq_true, ite_false] at hr ⊢
        simpa using ha.1 r hr
    · split <;> simp [hwrf]
  · refine ⟨fun r hr => ?_, fun h => absurd h hp⟩
    split
    · rename_i hw
      simp only [hw, ite_true, not_pub_set hp] at hr
      refine regs_filter ha.1 (fun r hr => ?_) (fun r hr => ?_) r hr <;>
        (rw [hwr]; simp [hr])
    · rename_i hw
      simp only [hw, Bool.false_eq_true, ite_false] at hr
      simpa using ha.1 r hr

theorem setReg_gpr_eq (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then (s.setReg d v).gpr d else s.gpr r := by
  simp only [State.setReg]; split <;> simp_all

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    refine ⟨ha.srcAddrs hok, regs_set ha.1 fun hp => ?_, ha.2⟩
    rw [ha.readSrc hp, hv₂] at hv₁; cases hv₁; rfl
  | mov32 d src =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    refine ⟨ha.srcAddrs hok, regs_set ha.1 fun hp => ?_, ha.2⟩
    rw [ha.readSrc32 hp, hv₂] at hv₁; cases hv₁; rfl
  | store m r =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store64] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha⟩
  | store32 m r =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha⟩
  | alu op d src =>
    simp only [step, aluStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    refine ⟨ha.srcAddrs hok, ?_⟩
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
    exact alu_sound ha (fun s => s.gpr d) (fun s x => s.setReg d x) id
      (setReg_gpr_eq · d) (by simp [State.setReg]) (by simp)
      (fun hp => by rw [ha.readSrc hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂
  | alu32 op d src =>
    simp only [step, aluStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    refine ⟨ha.srcAddrs hok, ?_⟩
    simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
    exact alu_sound ha (fun s => (s.gpr d).setWidth 32) (fun s x => s.setReg32 d x)
      (fun h => by simp only [h]) (fun s x => setReg_gpr_eq s d _) (by simp [State.setReg32, State.setReg])
      (by simp [State.setReg32])
      (fun hp => by rw [ha.readSrc32 hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂
  | shift32 op d n =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    by_cases hn : 1 ≤ n ∧ n ≤ 31
    swap; · simp [exec, execShift32, hn] at e₁
    simp only [exec, execShift32, hn, and_self, ite_true] at e₁ e₂
    refine ⟨rfl, fun r hr => ?_, fun hf => ?_⟩
    · by_cases hrd : r = d
      · subst hrd
        have := ha.1 r hr
        cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg32, State.setReg, this]
      · cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
          simp [State.setReg32, State.setReg, State.setFlags, hrd, ha.1 r hr]
    · simp only [Bool.and_eq_true] at hf
      have hd := ha.reg hf.2
      have hfl := ha.2 hf.1
      cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg32, State.setFlags, hd, hfl]
  | bswap32 d =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, fun r hr => ?_, fun hf => by simpa [State.setReg32] using ha.2 hf⟩
    by_cases hrd : r = d
    · subst hrd; simp [State.setReg32, State.setReg, ha.1 r hr]
    · simp [State.setReg32, State.setReg, hrd, ha.1 r hr]

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨hcf, hzf, -, -⟩ := ha.2 hc
  cases c <;> simp [eval, hcf, hzf]

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ :=
  ⟨fun r hr => h.1 r (List.mem_filter.mp hr).1,
   fun hf => h.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.1)⟩

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ :=
  ⟨fun r hr => h.1 r (pub_iff.mp (List.mem_filter.mp hr).2),
   fun hf => h.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.2)⟩

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
  refine ⟨fun r hr => h.1 r (pub_iff.mp (hle.1 r hr)), fun hf => h.2 ?_⟩
  rcases hle.2 with h' | h'
  · simp [hf] at h'
  · exact h'

end VG.X86_64.Taint

namespace VG.X86_64

/-- Taint tracking for x86-64. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.le
  le_sound := Taint.le_sound

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := ⟨rs, false⟩

theorem Taint.agree_ofRegs {rs : List Reg} {s₁ s₂ : State}
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨h, fun h => by cases h⟩

end VG.X86_64
