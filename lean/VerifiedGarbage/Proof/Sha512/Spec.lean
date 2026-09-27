import Mathlib.Tactic
import VerifiedGarbage.Spec.Sha512

/-!
# SHA-512: lemmas about the specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha512

open VG.Spec.Sha512

/-! ## The message schedule -/

theorem schedule_succ (M : Block) (t : Nat) : schedule M (t + 1) = W M t :: schedule M t := rfl

theorem schedule_getElem! (M : Block) {t i : Nat} (hi : i < t) :
    (schedule M t)[i]! = W M (t - 1 - i) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    rw [schedule_succ]
    cases i with
    | zero => simp
    | succ i =>
      simp only [getElem!_pos (W M t :: schedule M t) (i + 1) (by
          simp only [List.length_cons]
          have : (schedule M t).length = t := by
            clear ih hi; induction t with
            | zero => rfl
            | succ t ih => rw [schedule_succ, List.length_cons, ih]
          omega),
        List.getElem_cons_succ]
      rw [← getElem!_pos, ih (by omega)]
      congr 1; omega

theorem W_lt (M : Block) {t : Nat} (h : t < 16) : W M t = M ⟨t, h⟩ := by
  simp [W, schedule, h]

theorem W_ge (M : Block) {t : Nat} (h : 16 ≤ t) :
    W M t = ssig1 (W M (t - 2)) + W M (t - 7) + ssig0 (W M (t - 15)) + W M (t - 16) := by
  show (schedule M (t + 1)).headD 0 = _
  simp only [schedule, show ¬ t < 16 by omega, dite_false, List.headD_cons]
  rw [schedule_getElem! M (by omega), schedule_getElem! M (by omega),
    schedule_getElem! M (by omega), schedule_getElem! M (by omega),
    show t - 1 - 1 = t - 2 by omega, show t - 1 - 6 = t - 7 by omega,
    show t - 1 - 14 = t - 15 by omega, show t - 1 - 15 = t - 16 by omega]

/-! ## Rounds -/

/-- One round with explicit `Kₜ` and `Wₜ`. -/
def roundKW (v : HashValue) (k w : Word) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let e := v[4]; let f := v[5]; let g := v[6]; let h := v[7]
  let T₁ := h + bsig1 e + ch e f g + k + w
  let T₂ := bsig0 a + maj a b c
  #v[T₁ + T₂, a, b, c, d + T₁, e, f, g]

theorem round_eq (M : Block) (v : HashValue) (t : Nat) :
    round M v t = roundKW v (K t) (W M t) := rfl

theorem rounds_zero (H : HashValue) (M : Block) : rounds H M 0 = H := rfl

theorem rounds_succ (H : HashValue) (M : Block) (t : Nat) :
    rounds H M (t + 1) = round M (rounds H M t) t := by
  simp [rounds, List.range_succ, List.foldl_append]

/-! ## Bitwise identities used by the implementations -/

theorem add_left_comm {n : Nat} (a b c : BitVec n) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

/-- Normalizes sums (with `simp only`) up to associativity and commutativity. -/
theorem add_ac {n : Nat} : (∀ a b c : BitVec n, a + b + c = a + (b + c)) ∧
    (∀ a b : BitVec n, a + b = b + a) ∧ (∀ a b c : BitVec n, a + (b + c) = b + (a + c)) :=
  ⟨BitVec.add_assoc, BitVec.add_comm, add_left_comm⟩

theorem rotateRight_rotateRight (x : Word) {a b : Nat} (hab : a + b < 64) :
    (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight]
  split_ifs <;> first | omega | (congr 1; omega)

theorem ch_eq (x y z : Word) : ch x y z = (y ^^^ z) &&& x ^^^ z := by
  ext i; simp only [ch, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem maj_eq (x y z : Word) : maj x y z = (x ||| y) &&& z ||| x &&& y := by
  ext i; simp only [maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem bsig0_eq (x : Word) :
    bsig0 x = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ (x.rotateRight 34).rotateRight 5 := by
  rw [rotateRight_rotateRight x (by omega)]; rfl

theorem bsig1_eq (x : Word) :
    bsig1 x = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ (x.rotateRight 18).rotateRight 23 := by
  rw [rotateRight_rotateRight x (by omega)]; rfl

theorem rotateRight_xor (x y : Word) (n : Nat) :
    (x ^^^ y).rotateRight n = x.rotateRight n ^^^ y.rotateRight n := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_xor]
  split_ifs <;> rfl

theorem ssig0_eq (x : Word) :
    ssig0 x = (x.rotateRight 7 ^^^ x).rotateRight 1 ^^^ x >>> 7 := by
  rw [rotateRight_xor, rotateRight_rotateRight x (by omega), BitVec.xor_comm (x.rotateRight (7 + 1))]
  rfl

theorem ssig1_eq (x : Word) :
    ssig1 x = (x.rotateRight 42 ^^^ x).rotateRight 19 ^^^ x >>> 6 := by
  rw [rotateRight_xor, rotateRight_rotateRight x (by omega), BitVec.xor_comm (x.rotateRight (42 + 19))]
  rfl

end VG.Proof.Sha512
