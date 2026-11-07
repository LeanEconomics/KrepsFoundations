/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.HomotheticDemand
import ConsumerDemand.PositiveLogDemand
import ConsumerDemand.LinearLeontiefHomogeneity

/-!
# Homotheticity of the explicit demand examples

Kreps I, Problem 3.10(a), p. 65. Unshifted Cobb-Douglas, linear and Leontief
preferences are homothetic. The ordinary logarithmic example has the same
scaling comparison on its positive domain; no utility is assigned to undefined
zero logarithms. Nonzero shifts require a separate classification.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Positive commodity scaling multiplies Cobb-Douglas utility by the total-exponent power. -/
theorem cobbDouglas_scale_pos {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) :
    CobbDouglas a (ScaleBundle t x) = (t : ℝ) ^ (∑ j, a j) * CobbDouglas a x := by
  unfold CobbDouglas ShiftedCobbDouglas
  simp only [ScaleBundle, Pi.zero_apply, add_zero]
  have hterm (j : Fin k) : ((t : ℝ) * x.val j) ^ a j =
      (t : ℝ) ^ a j * x.val j ^ a j := Real.mul_rpow t.property (x.property j)
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht]

/-- **Problem 3.10(a):** Cobb-Douglas preferences are homothetic without exponent normalization. -/
theorem cobbDouglas_homothetic {k : ℕ} (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (CobbDouglas a)) := by
  intro x z t hxz
  by_cases ht : 0 < (t : ℝ)
  · change CobbDouglas a (ScaleBundle t z) ≤ CobbDouglas a (ScaleBundle t x)
    rw [cobbDouglas_scale_pos a t ht, cobbDouglas_scale_pos a t ht]
    exact mul_le_mul_of_nonneg_left hxz (Real.rpow_pos_of_pos ht _).le
  · have ht0 : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property)
    subst t
    rw [scaleBundle_zero_scalar, scaleBundle_zero_scalar]
    exact le_rfl

/-- On positive consumption, scaling adds the same weighted logarithm to utility. -/
theorem weightedLog_scale_pos {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j) :
    ShiftedLogUtility a 0 (ScaleBundle t x) =
      (∑ j, a j) * Real.log t + ShiftedLogUtility a 0 x := by
  unfold ShiftedLogUtility
  simp only [ScaleBundle, Pi.zero_apply, add_zero]
  simp_rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (hx _)), mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- **Problem 3.10(a), logarithms:** positive scaling preserves all defined log comparisons. -/
theorem logarithmic_positive_scaling_iff {k : ℕ} (a : Fin k → ℝ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (x z : NonnegativeOrthant k)
    (hx : ∀ j, 0 < x.val j) (hz : ∀ j, 0 < z.val j) :
    UtilityPref (ShiftedLogUtility a 0) (ScaleBundle t x) (ScaleBundle t z) ↔
      UtilityPref (ShiftedLogUtility a 0) x z := by
  unfold UtilityPref
  rw [weightedLog_scale_pos a t ht z hz, weightedLog_scale_pos a t ht x hx]
  exact add_le_add_iff_left _

end Kreps.ConsumerDemand
