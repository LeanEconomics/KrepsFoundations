/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.RationalEnumerationCodes

/-!
# The exact rational enumeration in Problem 1.12

The printed enumeration is zero first, then the reduced fractions with increasing
denominator and increasing numerator within each denominator. `PrintedRationalIndex`
is a bijection, so `PrintedRationalSequence` has neither repetitions nor gaps.
The order theorem specifies every term, and the first nine terms agree with the
display on p. 26: `0, 1, 1/2, 1/3, 2/3, 1/4, 3/4, 1/5, 2/5`.
-/

namespace Kreps.ChoicePreferenceUtility

/-- Regard a rational in the closed unit interval as a rational point of the real interval. -/
def RationalUnitPoint (q : Set.Icc (0 : ℚ) 1) : RationalUnitPoints :=
  ⟨⟨q.val, ⟨by exact_mod_cast q.property.1, by exact_mod_cast q.property.2⟩⟩,
    ⟨q.val, rfl⟩⟩

/-- Rational numbers in the interval and rational points of the interval coincide bijectively. -/
theorem rationalUnitPoint_bijective : Function.Bijective RationalUnitPoint := by
  constructor
  · intro q r h
    apply Subtype.ext
    have heq : (q.val : ℝ) = r.val := congrArg (fun x => x.val.val) h
    exact_mod_cast heq
  · intro x
    obtain ⟨q, hq⟩ := x.property
    have hmem : q ∈ Set.Icc (0 : ℚ) 1 := by
      have hreal : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        rw [hq]
        exact x.val.property
      exact ⟨by exact_mod_cast hreal.1, by exact_mod_cast hreal.2⟩
    refine ⟨⟨q, hmem⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hq)

/-- Identify the rational interval with the chapter's existing rational-point type. -/
noncomputable def RationalUnitPointEquiv : Set.Icc (0 : ℚ) 1 ≃ RationalUnitPoints :=
  Equiv.ofBijective RationalUnitPoint rationalUnitPoint_bijective

/-- The exact zero-based index in Kreps's displayed enumeration of the rational unit interval. -/
noncomputable def PrintedRationalIndex : RationalUnitPoints ≃ ℕ :=
  RationalUnitPointEquiv.symm.trans UnitRationalIndex

/-- Kreps's rational sequence, defined as the inverse of its bijective index. -/
noncomputable def PrintedRationalSequence (n : ℕ) : RationalUnitPoints :=
  PrintedRationalIndex.symm n

/-- Every index is attained by its sequence term. -/
theorem printedRationalIndex_sequence (n : ℕ) :
    PrintedRationalIndex (PrintedRationalSequence n) = n :=
  PrintedRationalIndex.apply_symm_apply n

/-- Every rational point occurs in the sequence, at its unique assigned index. -/
theorem printedRationalSequence_index (q : RationalUnitPoints) :
    PrintedRationalSequence (PrintedRationalIndex q) = q :=
  PrintedRationalIndex.symm_apply_apply q

/-- The printed sequence has no repeated terms and omits no rational point. -/
theorem printedRationalSequence_bijective : Function.Bijective PrintedRationalSequence :=
  PrintedRationalIndex.symm.bijective

/-- A canonical unit rational has its reduced-fraction counting index. -/
theorem printedRationalIndex_point (q : Set.Icc (0 : ℚ) 1) :
    PrintedRationalIndex (RationalUnitPoint q) =
      Nat.count ValidRationalCode (Nat.pair q.val.den q.val.num.toNat) := by
  change UnitRationalIndex (RationalUnitPointEquiv.symm (RationalUnitPointEquiv q)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The printed order is precisely increasing denominator, then increasing numerator. -/
theorem printedRationalIndex_lt_iff (q r : Set.Icc (0 : ℚ) 1) :
    PrintedRationalIndex (RationalUnitPoint q) < PrintedRationalIndex (RationalUnitPoint r) ↔
      q.val.den < r.val.den ∨ q.val.den = r.val.den ∧ q.val.num < r.val.num := by
  rw [printedRationalIndex_point, printedRationalIndex_point]
  exact unitRationalIndex_lt_iff q r

/-- A computed index determines the real value of the corresponding sequence term. -/
theorem printedRationalSequence_value_of_index (q : Set.Icc (0 : ℚ) 1) (n : ℕ)
    (h : Nat.count ValidRationalCode (Nat.pair q.val.den q.val.num.toNat) = n) :
    (PrintedRationalSequence n).val.val = (q.val : ℝ) := by
  have hi : PrintedRationalIndex (RationalUnitPoint q) = n :=
    (printedRationalIndex_point q).trans h
  rw [← hi, printedRationalSequence_index]
  rfl

/-- The printed enumeration begins with zero. -/
theorem printedRationalSequence_zero : (PrintedRationalSequence 0).val.val = 0 := by
  simpa using printedRationalSequence_value_of_index ⟨0, by norm_num⟩ 0 (by decide +kernel)

/-- The second printed term is one. -/
theorem printedRationalSequence_one : (PrintedRationalSequence 1).val.val = 1 := by
  simpa using printedRationalSequence_value_of_index ⟨1, by norm_num⟩ 1 (by decide +kernel)

/-- The third printed term is one half. -/
theorem printedRationalSequence_two : (PrintedRationalSequence 2).val.val = 1 / 2 := by
  simpa using printedRationalSequence_value_of_index ⟨1 / 2, by norm_num⟩ 2 (by decide +kernel)

/-- The fourth printed term is one third. -/
theorem printedRationalSequence_three : (PrintedRationalSequence 3).val.val = 1 / 3 := by
  simpa using printedRationalSequence_value_of_index ⟨1 / 3, by norm_num⟩ 3 (by decide +kernel)

/-- The fifth printed term is two thirds. -/
theorem printedRationalSequence_four : (PrintedRationalSequence 4).val.val = 2 / 3 := by
  simpa using printedRationalSequence_value_of_index ⟨2 / 3, by norm_num⟩ 4 (by decide +kernel)

/-- The sixth printed term is one quarter. -/
theorem printedRationalSequence_five : (PrintedRationalSequence 5).val.val = 1 / 4 := by
  simpa using printedRationalSequence_value_of_index ⟨1 / 4, by norm_num⟩ 5 (by decide +kernel)

/-- The seventh printed term is three quarters, with the unreduced two quarters omitted. -/
theorem printedRationalSequence_six : (PrintedRationalSequence 6).val.val = 3 / 4 := by
  simpa using printedRationalSequence_value_of_index ⟨3 / 4, by norm_num⟩ 6 (by decide +kernel)

/-- The eighth printed term is one fifth. -/
theorem printedRationalSequence_seven : (PrintedRationalSequence 7).val.val = 1 / 5 := by
  simpa using printedRationalSequence_value_of_index ⟨1 / 5, by norm_num⟩ 7 (by decide +kernel)

/-- The ninth printed term is two fifths. -/
theorem printedRationalSequence_eight : (PrintedRationalSequence 8).val.val = 2 / 5 := by
  simpa using printedRationalSequence_value_of_index ⟨2 / 5, by norm_num⟩ 8 (by decide +kernel)

end Kreps.ChoicePreferenceUtility
