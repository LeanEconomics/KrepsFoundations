/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.RationalEnumeration
import ChoicePreferenceUtility.RationalUtilityValues

/-!
# Utility for the printed rational enumeration

Kreps I, Problem 1.12, p. 26, with the actual enumeration and the weights from
Proposition 1.12, p. 11. Its first terms are zero, one, one half, and one third;
their weights are one half, one quarter, one eighth, and one sixteenth. The utility
is the sum of weights at rational points no larger than its argument. It represents
the usual order, is discontinuous at every positive rational, and has endpoint
values one half and one. There is no arbitrary enumeration parameter in this
construction.
-/

namespace Kreps.ChoicePreferenceUtility

/-- The book's geometric weights for its displayed denominator-then-numerator enumeration. -/
noncomputable def PrintedRationalWeights : RationalUnitPoints → ℝ :=
  GeometricRationalWeights PrintedRationalIndex.toEmbedding

/-- Every printed weight is positive, and the family is summable. -/
theorem printedRationalWeights_valid :
    (∀ q, 0 < PrintedRationalWeights q) ∧ Summable PrintedRationalWeights :=
  geometricRationalWeights_valid PrintedRationalIndex.toEmbedding

/-- The zero-based term numbered `n` carries the book's one-based weight `2 ^ (-(n+1))`. -/
theorem printedRationalWeights_sequence (n : ℕ) :
    PrintedRationalWeights (PrintedRationalSequence n) = (1 / 2 : ℝ) ^ (n + 1) := by
  simp [PrintedRationalWeights, GeometricRationalWeights, PrintedRationalSequence]

/-- The first four weights belong, respectively, to zero, one, one half, and one third. -/
theorem printedRationalWeights_first_four :
    PrintedRationalWeights (PrintedRationalSequence 0) = 1 / 2 ∧
      PrintedRationalWeights (PrintedRationalSequence 1) = 1 / 4 ∧
      PrintedRationalWeights (PrintedRationalSequence 2) = 1 / 8 ∧
      PrintedRationalWeights (PrintedRationalSequence 3) = 1 / 16 := by
  norm_num [printedRationalWeights_sequence]

/-- The total mass of the actual printed weights is one. -/
theorem printedRationalWeights_sum : ∑' q, PrintedRationalWeights q = 1 :=
  geometricRationalWeights_sum PrintedRationalIndex

/-- The specific utility produced from the printed enumeration, not merely an ordinal equivalent. -/
noncomputable def PrintedRationalUtility : UnitSegment → ℝ :=
  RationalUtility PrintedRationalWeights

/-- The literal construction in **Problem 1.12** represents the usual order on `[0,1]`. -/
theorem problem_1_12_printed_represents :
    Represents PrintedRationalUtility (UtilityPref (fun x : UnitSegment => x.val)) :=
  problem_1_12_represents printedRationalWeights_valid.1 printedRationalWeights_valid.2

/-- Every strict increase in the argument strictly increases the printed utility. -/
theorem printedRationalUtility_strictMono : StrictMono PrintedRationalUtility := by
  intro x y hxy
  exact (strict_iff_utility_lt problem_1_12_printed_represents y x).mp
    ⟨hxy.le, not_le_of_gt hxy⟩

/-- An exact natural-number series formula for the graph requested in **Problem 1.12**. -/
theorem printedRationalUtility_series (x : UnitSegment) :
    PrintedRationalUtility x = ∑' n : ℕ,
      if (PrintedRationalSequence n).val.val ≤ x.val then (1 / 2 : ℝ) ^ (n + 1) else 0 :=
  rationalUtility_geometric_series PrintedRationalIndex x

/-- Approaching a rational from below misses its full, explicitly indexed weight. -/
theorem printedRationalUtility_jump (q : RationalUnitPoints) {x : UnitSegment}
    (hx : x.val < q.val.val) :
    PrintedRationalUtility x + (1 / 2 : ℝ) ^ (PrintedRationalIndex q + 1) ≤
      PrintedRationalUtility q.val :=
  rationalUtility_jump printedRationalWeights_valid.1 printedRationalWeights_valid.2 q hx

/-- The literal utility is discontinuous at every positive rational, including one. -/
theorem problem_1_12_printed_discontinuous (q : RationalUnitPoints) (hq : 0 < q.val.val) :
    ¬ContinuousAt PrintedRationalUtility q.val :=
  problem_1_12_discontinuous printedRationalWeights_valid.1 printedRationalWeights_valid.2 q hq

/-- The particular utility produced in the exercise is not a continuous function. -/
theorem printedRationalUtility_not_continuous : ¬Continuous PrintedRationalUtility := by
  intro hc
  apply problem_1_12_printed_discontinuous (PrintedRationalSequence 1) _ hc.continuousAt
  rw [printedRationalSequence_one]
  norm_num

/-- Only the first, zero-valued rational contributes to the utility at zero. -/
theorem printedRationalUtility_zero :
    PrintedRationalUtility ⟨0, by norm_num⟩ = 1 / 2 := by
  have hzero : (PrintedRationalSequence 0).val = (⟨0, by norm_num⟩ : UnitSegment) :=
    Subtype.ext printedRationalSequence_zero
  rw [← hzero]
  change RationalUtility PrintedRationalWeights (PrintedRationalSequence 0).val = _
  rw [rationalUtility_at_zero _ _ printedRationalSequence_zero,
    printedRationalWeights_sequence]
  norm_num

/-- At one the utility includes every printed weight, whose sum is one. -/
theorem printedRationalUtility_one :
    PrintedRationalUtility ⟨1, by norm_num⟩ = 1 := by
  change RationalUtility PrintedRationalWeights _ = _
  rw [rationalUtility_at_one _ _ rfl, printedRationalWeights_sum]

/-- The exact endpoint values bound the entire graph. -/
theorem printedRationalUtility_mem_Icc (x : UnitSegment) :
    PrintedRationalUtility x ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  constructor
  · rw [← printedRationalUtility_zero]
    exact printedRationalUtility_strictMono.monotone x.property.1
  · rw [← printedRationalUtility_one]
    exact printedRationalUtility_strictMono.monotone x.property.2

end Kreps.ChoicePreferenceUtility
