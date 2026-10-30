/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CESContinuity
import ConsumerDemand.HomotheticDemand

/-!
# Homotheticity of CES preferences

Kreps I, Problems 3.7 and 3.10(a), pp. 64-65. CES utility is homogeneous of
degree one, including its zero boundary extension for negative exponents.
The resulting preference is homothetic for every nonnegative rescaling.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Scaling a commodity vector scales its power sum by the corresponding real power. -/
theorem cesPowerSum_scale {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (t : ℝ≥0) (x : NonnegativeOrthant k) :
    CESPowerSum a mu (ScaleBundle t x) = (t : ℝ) ^ mu * CESPowerSum a mu x := by
  simp only [CESPowerSum, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.mul_rpow (x := (t : ℝ)) (y := x.val j) (z := mu) t.property (x.property j)]
  ring

/-- The CES utility of the origin is zero for every nonzero exponent. -/
theorem cesUtility_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ) {mu : ℝ} (hm0 : mu ≠ 0) :
    CESUtility a mu (ZeroBundle k) = 0 := by
  by_cases hm : mu < 0
  · exact cesUtility_zero_of_coordinate a hm (j := ⟨0, NeZero.pos k⟩) rfl
  · simp [CESUtility, CESPowerSum, ZeroBundle, hm, Real.zero_rpow hm0,
      Real.zero_rpow (inv_ne_zero hm0)]

/-- Positive scaling preserves the CES formula on the full orthant. -/
theorem cesUtility_scale_pos {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) :
    CESUtility a mu (ScaleBundle t x) = (t : ℝ) * CESUtility a mu x := by
  have he : (∃ j, (ScaleBundle t x).val j = 0) ↔ ∃ j, x.val j = 0 := by
    simp only [ScaleBundle, mul_eq_zero, ht.ne', false_or]
  by_cases hb : mu < 0 ∧ ∃ j, x.val j = 0
  · have hb' : mu < 0 ∧ ∃ j, (ScaleBundle t x).val j = 0 := ⟨hb.1, he.mpr hb.2⟩
    simp only [CESUtility, ite_eq_left hb, ite_eq_left hb', mul_zero]
  · have hb' : ¬(mu < 0 ∧ ∃ j, (ScaleBundle t x).val j = 0) :=
      fun h => hb ⟨h.1, he.mp h.2⟩
    rw [CESUtility, ite_eq_right hb', CESUtility, ite_eq_right hb, cesPowerSum_scale,
      Real.mul_rpow (x := (t : ℝ) ^ mu) (y := CESPowerSum a mu x) (z := 1 / mu)
        (Real.rpow_nonneg t.property mu) (cesPowerSum_nonneg a ha mu x),
      ← Real.rpow_mul (x := (t : ℝ)) t.property]
    simp [hm0]

/-- CES utility is homogeneous of degree one, including at zero scale and zero quantities. -/
theorem cesUtility_scale {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) (t : ℝ≥0) (x : NonnegativeOrthant k) :
    CESUtility a mu (ScaleBundle t x) = (t : ℝ) * CESUtility a mu x := by
  by_cases ht : 0 < (t : ℝ)
  · exact cesUtility_scale_pos a ha hm0 t ht x
  · have he : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property)
    subst t
    rw [scaleBundle_zero_scalar, cesUtility_zero a hm0]
    simp

/-- **Problem 3.10(a), CES:** the nonzero-exponent CES utilities represent homothetic preference. -/
theorem cesUtility_homothetic {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) : HomotheticPreference (UtilityPref (CESUtility a mu)) :=
  homothetic_of_homogeneous (cesUtility_scale a ha hm0)

end Kreps.ConsumerDemand
