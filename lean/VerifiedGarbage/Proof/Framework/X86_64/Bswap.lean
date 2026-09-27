import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# `bswap` of a little-endian load is a big-endian load

Untrusted: everything here is checked by Lean.
-/

namespace VG.X86_64

theorem getLsbD_cat4 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec (8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b3.getLsbD i else if i < 16 then b2.getLsbD (i - 8)
      else if i < 24 then b1.getLsbD (i - 16) else b0.getLsbD (i - 24) := by
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | rfl

theorem bswap32_bytes (b0 b1 b2 b3 : BitVec 8) :
    bswap32 ((0#0 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 32) = (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 := getLsbD_cat4 b0 b1 b2 b3 i
  simp only [BitVec.setWidth_eq] at *
  simp only [bswap32]
  rw [getLsbD_cat4, e1]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_zero_length]
  interval_cases i <;> simp

/-- A 32-bit load followed by `bswap` reads the four bytes big-endian. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    bswap32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  bswap32_bytes _ _ _ _

theorem getLsbD_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 :
        BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b7.getLsbD i else if i < 16 then b6.getLsbD (i - 8)
      else if i < 24 then b5.getLsbD (i - 16) else if i < 32 then b4.getLsbD (i - 24)
      else if i < 40 then b3.getLsbD (i - 32) else if i < 48 then b2.getLsbD (i - 40)
      else if i < 56 then b1.getLsbD (i - 48) else b0.getLsbD (i - 56) := by
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | rfl

theorem bswap64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bswap64 ((0#0 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 := getLsbD_cat8 b0 b1 b2 b3 b4 b5 b6 b7 i
  simp only [BitVec.setWidth_eq] at *
  simp only [bswap64]
  rw [getLsbD_cat8, e1]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_zero_length]
  interval_cases i <;> simp

/-- A 64-bit load followed by `bswap` reads the eight bytes big-endian. -/
theorem bswap64_readW (m : Mem) (a : Addr) :
    bswap64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  bswap64_bytes _ _ _ _ _ _ _ _

end VG.X86_64
