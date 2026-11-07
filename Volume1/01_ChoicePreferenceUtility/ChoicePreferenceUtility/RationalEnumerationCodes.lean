/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.RationalUtilityExamples
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing

/-!
# Reduced fraction codes for the printed rational enumeration

Kreps I, Problem 1.12, p. 26 enumerates the rational unit interval by increasing
reduced denominator, then increasing numerator. A valid natural code is the
pairing of a positive denominator with a coprime numerator between zero and
that denominator. Pairing preserves this ordering on the indicated triangle.
Counting preceding valid codes gives a bijection with the natural numbers.
-/

namespace Kreps.ChoicePreferenceUtility

/-- A code decodes to a positive denominator and a reduced numerator in its unit interval. -/
abbrev ValidRationalCode (c : ℕ) : Prop :=
  0 < (Nat.unpair c).1 ∧ (Nat.unpair c).2 ≤ (Nat.unpair c).1 ∧
    (Nat.unpair c).2.Coprime (Nat.unpair c).1

/-- Read a valid code as the corresponding canonical reduced rational. -/
def RationalCodeValue (c : {c : ℕ // ValidRationalCode c}) : ℚ :=
  ⟨(Nat.unpair c.val).2, (Nat.unpair c.val).1, c.property.1.ne',
    by simpa using c.property.2.2⟩

/-- Every valid code represents a rational in the closed unit interval. -/
theorem rationalCodeValue_mem (c : {c : ℕ // ValidRationalCode c}) :
    RationalCodeValue c ∈ Set.Icc (0 : ℚ) 1 := by
  constructor
  · apply Rat.num_nonneg.mp
    exact Int.natCast_nonneg _
  · rw [Rat.le_iff]
    simpa [RationalCodeValue] using c.property.2.1

/-- Encode a unit rational by its canonical denominator and nonnegative numerator. -/
def UnitRationalCode (q : Set.Icc (0 : ℚ) 1) : ℕ :=
  Nat.pair q.val.den q.val.num.toNat

/-- The canonical rational numerator is nonnegative on the unit interval. -/
theorem unitRational_num_nonneg (q : Set.Icc (0 : ℚ) 1) : 0 ≤ q.val.num :=
  Rat.num_nonneg.mpr q.property.1

/-- The canonical numerator does not exceed the denominator on the unit interval. -/
theorem unitRational_num_le_den (q : Set.Icc (0 : ℚ) 1) :
    q.val.num.toNat ≤ q.val.den := by
  have h : q.val.num ≤ q.val.den := by simpa [Rat.le_iff] using q.property.2
  omega

/-- Every unit rational produces a valid reduced-fraction code. -/
theorem unitRationalCode_valid (q : Set.Icc (0 : ℚ) 1) :
    ValidRationalCode (UnitRationalCode q) := by
  simp only [ValidRationalCode, UnitRationalCode, Nat.unpair_pair]
  refine ⟨q.val.den_pos, unitRational_num_le_den q, ?_⟩
  have hn : (q.val.num.toNat : ℤ) = q.val.num := by
    have h := unitRational_num_nonneg q
    omega
  have h := q.val.reduced
  rw [← hn] at h
  simpa only [Int.natAbs_natCast] using h

/-- Decoding the canonical code recovers the original rational. -/
theorem rationalCodeValue_unitRationalCode (q : Set.Icc (0 : ℚ) 1) :
    RationalCodeValue ⟨UnitRationalCode q, unitRationalCode_valid q⟩ = q.val := by
  apply Rat.ext
  · simp only [RationalCodeValue, UnitRationalCode, Nat.unpair_pair]
    have h := unitRational_num_nonneg q
    omega
  · simp [RationalCodeValue, UnitRationalCode]

/-- Encoding a decoded valid code recovers precisely that code. -/
theorem unitRationalCode_rationalCodeValue (c : {c : ℕ // ValidRationalCode c}) :
    UnitRationalCode ⟨RationalCodeValue c, rationalCodeValue_mem c⟩ = c.val := by
  simp [UnitRationalCode, RationalCodeValue]

/-- The closed rational unit interval is equivalent to the valid reduced-fraction codes. -/
def UnitRationalCodeEquiv : Set.Icc (0 : ℚ) 1 ≃ {c : ℕ // ValidRationalCode c} where
  toFun q := ⟨UnitRationalCode q, unitRationalCode_valid q⟩
  invFun c := ⟨RationalCodeValue c, rationalCodeValue_mem c⟩
  left_inv q := Subtype.ext (rationalCodeValue_unitRationalCode q)
  right_inv c := Subtype.ext (unitRationalCode_rationalCodeValue c)

/-- Fractions with numerator one supply infinitely many valid codes. -/
theorem validRationalCode_infinite : (Set.ofPred ValidRationalCode).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => Nat.pair (n + 1) 1)
  · intro m n h
    have h' := (Nat.pair_eq_pair.mp h).1
    omega
  · intro n
    simp [ValidRationalCode]

/-- Ranking valid codes and selecting their successive values are inverse operations. -/
noncomputable def RationalCodeIndex : {c : ℕ // ValidRationalCode c} ≃ ℕ where
  toFun c := Nat.count ValidRationalCode c.val
  invFun n := ⟨Nat.nth ValidRationalCode n,
    Nat.nth_mem_of_infinite validRationalCode_infinite n⟩
  left_inv c := Subtype.ext (Nat.nth_count c.property)
  right_inv n := Nat.count_nth_of_infinite validRationalCode_infinite n

/-- The index of a rational is the number of valid codes strictly before its own code. -/
noncomputable def UnitRationalIndex : Set.Icc (0 : ℚ) 1 ≃ ℕ :=
  UnitRationalCodeEquiv.trans RationalCodeIndex

/-- On the reduced-fraction triangle, pairing orders denominator first, then numerator. -/
theorem rationalCode_lt_iff {d n e m : ℕ} (hn : n ≤ d) (hm : m ≤ e) :
    Nat.pair d n < Nat.pair e m ↔ d < e ∨ d = e ∧ n < m := by
  simp only [Nat.pair, not_lt_of_ge hn, not_lt_of_ge hm, ite_false]
  constructor
  · intro h
    by_cases hde : d < e
    · exact Or.inl hde
    · right
      have hed : e ≤ d := le_of_not_gt hde
      have heq : d = e := by
        by_contra hne
        have hlt : e < d := lt_of_le_of_ne hed (Ne.symm hne)
        nlinarith
      exact ⟨heq, by subst e; omega⟩
  · rintro (h | ⟨rfl, h⟩)
    · nlinarith
    · omega

/-- Natural indices agree exactly with the ordering of their valid codes. -/
theorem rationalCodeIndex_lt_iff (c d : {c : ℕ // ValidRationalCode c}) :
    RationalCodeIndex c < RationalCodeIndex d ↔ c.val < d.val := by
  constructor
  · intro h
    exact (Nat.count_monotone ValidRationalCode).reflect_lt h
  · intro h
    exact Nat.count_strict_mono c.property h

/-- The exact ordering interpretation: denominator, then numerator, in increasing order. -/
theorem unitRationalIndex_lt_iff (q r : Set.Icc (0 : ℚ) 1) :
    UnitRationalIndex q < UnitRationalIndex r ↔
      q.val.den < r.val.den ∨ q.val.den = r.val.den ∧ q.val.num < r.val.num := by
  change RationalCodeIndex (UnitRationalCodeEquiv q) <
    RationalCodeIndex (UnitRationalCodeEquiv r) ↔ _
  rw [rationalCodeIndex_lt_iff]
  change Nat.pair q.val.den q.val.num.toNat < Nat.pair r.val.den r.val.num.toNat ↔ _
  rw [rationalCode_lt_iff (unitRational_num_le_den q) (unitRational_num_le_den r)]
  have hq := unitRational_num_nonneg q
  have hr := unitRational_num_nonneg r
  omega

end Kreps.ChoicePreferenceUtility
