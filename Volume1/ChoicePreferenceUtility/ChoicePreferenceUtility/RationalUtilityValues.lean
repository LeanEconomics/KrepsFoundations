/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.RationalUtilityExamples

/-!
# Endpoint values and reindexing for rational utility

Kreps I, Problem 1.12, p. 26, using the geometric weights in the proof of
Proposition 1.12, p. 11. A bijective enumeration gives the ordinary natural-number
series, with total weight one. At zero only the weight of zero contributes.
The printed enumeration is specialized in `PrintedRationalUtility`.
-/

namespace Kreps.ChoicePreferenceUtility

/-- At zero, the rational lower contour contains only zero itself. -/
theorem rationalUtility_at_zero (w : RationalUnitPoints → ℝ) (q : RationalUnitPoints)
    (hq : q.val.val = 0) : RationalUtility w q.val = w q := by
  classical
  rw [rationalUtility_formula]
  rw [tsum_eq_single q]
  · simp
  · intro p hp
    have hnot : ¬p.val.val ≤ q.val.val := by
      intro hle
      apply hp
      apply Subtype.ext
      apply Subtype.ext
      exact le_antisymm hle (by rw [hq]; exact p.val.property.1)
    simp only [hnot, ite_false]

/-- At one, every rational point contributes its weight. -/
theorem rationalUtility_at_one (w : RationalUnitPoints → ℝ) (x : UnitSegment)
    (hx : x.val = 1) : RationalUtility w x = ∑' q, w q := by
  rw [rationalUtility_formula]
  apply tsum_congr
  intro q
  rw [hx, ite_eq_left q.val.property.2]

/-- Reindexing by a bijection gives exactly the geometric natural-number series. -/
theorem rationalUtility_geometric_series (e : RationalUnitPoints ≃ ℕ) (x : UnitSegment) :
    RationalUtility (GeometricRationalWeights e.toEmbedding) x =
      ∑' n : ℕ, if (e.symm n).val.val ≤ x.val then (1 / 2 : ℝ) ^ (n + 1) else 0 := by
  rw [rationalUtility_formula, ← e.symm.tsum_eq]
  apply tsum_congr
  intro n
  simp only [GeometricRationalWeights, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]

/-- The one-based geometric weights used in the book have total mass one. -/
theorem geometricRationalWeights_sum (e : RationalUnitPoints ≃ ℕ) :
    ∑' q, GeometricRationalWeights e.toEmbedding q = 1 := by
  rw [← e.symm.tsum_eq]
  simp only [GeometricRationalWeights, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
  simp only [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]
  norm_num

end Kreps.ChoicePreferenceUtility
