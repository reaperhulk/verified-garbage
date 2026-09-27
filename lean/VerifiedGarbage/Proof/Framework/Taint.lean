import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Constant time by taint tracking

Untrusted: everything here is checked by Lean.

A `Taint M` is a sound, executable information-flow analysis for the ISA `M`:
an abstract domain `T` of "which parts of the state are public", a relation
`Agree τ s₁ s₂` ("the two states agree on everything `τ` says is public"),
and a transfer function for instructions that fails (`none`) whenever an
instruction would leak (through the addresses it accesses) something that is
not public. `Taint.check` lifts it to structured code; `Taint.constantTime`
turns a successful check into `ConstantTime`, which can then be established
for a whole program by evaluation (`decide +kernel`).
-/

namespace VG

structure Taint (M : ISA) where
  T : Type
  Agree : T → M.State → M.State → Prop
  step : T → M.Instr → Option T
  step_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → step τ i = some τ' →
    M.exec i s₁ = some s₁' → M.exec i s₂ = some s₂' →
    M.addrs i s₁ = M.addrs i s₂ ∧ Agree τ' s₁' s₂'
  /-- The condition only depends on public data. -/
  condPub : T → M.Cond → Bool
  cond_sound : ∀ {τ c s₁ s₂}, Agree τ s₁ s₂ → condPub τ c = true → M.eval c s₁ = M.eval c s₂
  /-- Something public in both. -/
  meet : T → T → T
  meet_left : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₁ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  meet_right : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₂ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  /-- `le τ σ`: everything public in `τ` is public in `σ`. -/
  le : T → T → Bool
  le_sound : ∀ {τ σ s₁ s₂}, le τ σ = true → Agree σ s₁ s₂ → Agree τ s₁ s₂

namespace Taint

variable {M : ISA} (A : Taint M)

def checkBlock : A.T → List M.Instr → Option A.T
  | τ, [] => some τ
  | τ, i :: is => (A.step τ i).bind fun τ' => checkBlock τ' is

/-- The analysis of structured code. A loop is checked with its entry taint
as the invariant: the body must keep public everything that was public on
entry, and leave the loop condition public. -/
def check : A.T → Prog M → Option A.T
  | τ, .block is => A.checkBlock τ is
  | τ, .seq c₁ c₂ => (check τ c₁).bind fun τ' => check τ' c₂
  | τ, .ite c t e =>
    if A.condPub τ c then
      (check τ t).bind fun τ₁ => (check τ e).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | τ, .loop body c =>
    (check τ body).bind fun τ' => if A.le τ τ' && A.condPub τ' c then some τ' else none

variable {A}

theorem checkBlock_sound {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : execBlock M is s₁ = some (s₁', t₁)) (e₂ : execBlock M is s₂ = some (s₂', t₂)) :
    t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction is generalizing τ s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂; subst h; exact ⟨rfl, ha⟩
  | cons i is ih =>
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> rename_i h₁ <;> [cases e₁; skip]
    split at e₂ <;> rename_i h₂ <;> [cases e₂; skip]
    rename_i s₁₁ _ s₂₁
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, e₁, he₁⟩ := e₁
    obtain ⟨_, u₂, e₂, he₂⟩ := e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    obtain ⟨hadd, ha₁⟩ := A.step_sound ha hs h₁ h₂
    obtain ⟨ht, ha'⟩ := ih hr ha₁ e₁ e₂
    exact ⟨by rw [hadd, ht], ha'⟩

theorem check_sound {c : Prog M} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak}
    (h : A.check τ c = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂') : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction e₁ generalizing τ τ' s₂ t₂ s₂' with
  | block h₁ =>
    cases e₂ with
    | block h₂ => exact checkBlock_sound h ha h₁ h₂
  | seq _ _ ih₁ ih₂ =>
    cases e₂ with
    | seq a b =>
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      obtain ⟨rfl, ha₁⟩ := ih₁ h₁ ha a
      obtain ⟨rfl, ha₂⟩ := ih₂ h₂ ha₁ b
      exact ⟨rfl, ha₂⟩
  | iteT hc _ ih =>
    simp only [check] at h
    split at h <;> [skip; cases h]
    rename_i hp
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
    cases e₂ with
    | iteT _ b => obtain ⟨rfl, hq⟩ := ih h₁ ha b; exact ⟨rfl, A.meet_left hq⟩
    | iteF hc' _ => rw [← A.cond_sound ha hp, hc] at hc'; cases hc'
  | iteF hc _ ih =>
    simp only [check] at h
    split at h <;> [skip; cases h]
    rename_i hp
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
    cases e₂ with
    | iteT hc' _ => rw [← A.cond_sound ha hp, hc] at hc'; cases hc'
    | iteF _ b => obtain ⟨rfl, hq⟩ := ih h₂ ha b; exact ⟨rfl, A.meet_right hq⟩
  | loopExit _ hc ih =>
    have h' := h
    simp only [check, Option.bind_eq_some_iff] at h'
    obtain ⟨τ₁, hb, hl⟩ := h'
    split at hl <;> [skip; cases hl]
    rename_i hle
    cases hl
    simp only [Bool.and_eq_true] at hle
    cases e₂ with
    | loopExit a _ => obtain ⟨rfl, hq⟩ := ih hb ha a; exact ⟨rfl, hq⟩
    | loopNext a hc' _ =>
      obtain ⟨_, ha₁⟩ := ih hb ha a
      rw [← A.cond_sound ha₁ hle.2, hc] at hc'; cases hc'
  | loopNext _ hc _ ih₁ ih₂ =>
    have h' := h
    simp only [check, Option.bind_eq_some_iff] at h'
    obtain ⟨τ₁, hb, hl⟩ := h'
    split at hl <;> [skip; cases hl]
    rename_i hle
    cases hl
    simp only [Bool.and_eq_true] at hle
    cases e₂ with
    | loopExit a hc' =>
      obtain ⟨_, ha₁⟩ := ih₁ hb ha a
      rw [← A.cond_sound ha₁ hle.2, hc] at hc'; cases hc'
    | loopNext a _ b =>
      obtain ⟨rfl, ha₁⟩ := ih₁ hb ha a
      obtain ⟨rfl, ha₂⟩ := ih₂ h (A.le_sound hle.1 ha₁) b
      exact ⟨rfl, ha₂⟩

/-- A successful check proves constant time, for any `Pub` under which the
initial states agree on what the initial taint says is public. -/
theorem constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂)
    (h : (A.check τ c).isSome = true) : ConstantTime M Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (check_sound hc (hpub _ _ h₁ h₂ hp) e₁ e₂).1

end Taint

end VG
