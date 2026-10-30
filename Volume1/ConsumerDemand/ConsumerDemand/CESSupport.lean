/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict support inequalities for CES powers

Kreps I, Problem 3.7, pp. 64-65. Dividing the power by its nonzero exponent
gives an increasing, strictly concave transform for every exponent below one.
The comparison permits a zero alternative when the exponent is positive; for
negative exponents it applies on the positive half-line. These inequalities
will prove global optimality without differentiating at a zero coordinate.
-/

namespace Kreps.ConsumerDemand

/-- The normalized power lies strictly below its tangent at one. -/
theorem normalizedPower_unit_tangent_lt {mu t : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (ht : 0 ≤ t) (htp : mu < 0 → 0 < t) (hne : t ≠ 1) :
    (t ^ mu - 1) / mu < t - 1 := by
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · have hl := Real.log_lt_sub_one_of_pos (htp hm) hne
    have he := Real.add_one_le_exp (Real.log t * mu)
    rw [← Real.rpow_def_of_pos (htp hm)] at he
    have hm' := mul_lt_mul_of_neg_right hl hm
    apply (div_lt_iff_of_neg hm).mpr
    nlinarith
  · have hb := rpow_one_add_lt_one_add_mul_self
      (s := t - 1) (by linarith) (sub_ne_zero.mpr hne) hm hmu
    simp only [add_sub_cancel] at hb
    exact (div_lt_iff₀ hm).mpr (by linarith)

/-- The normalized power has a strict supporting tangent at every positive point. -/
theorem normalizedPower_tangent_lt {mu x z : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (hx : 0 < x) (hz : 0 ≤ z) (hzp : mu < 0 → 0 < z) (hne : z ≠ x) :
    (z ^ mu - x ^ mu) / mu < x ^ (mu - 1) * (z - x) := by
  have hxp := Real.rpow_pos_of_pos hx mu
  have ht := normalizedPower_unit_tangent_lt hmu hm0 (div_nonneg hz hx.le)
    (fun hm => div_pos (hzp hm) hx) (by
      intro he
      exact hne ((div_eq_one_iff_eq hx.ne').mp he))
  calc
    (z ^ mu - x ^ mu) / mu = x ^ mu * ((z / x) ^ mu - 1) / mu := by
      rw [Real.div_rpow hz hx.le]
      field_simp
    _ < x ^ mu * (z / x - 1) := by
      simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left ht hxp
    _ = x ^ (mu - 1) * (z - x) := by
      rw [Real.rpow_sub_one hx.ne']
      field_simp

/-- The weak supporting inequality also includes an alternative equal to the base point. -/
theorem normalizedPower_tangent_le {mu x z : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (hx : 0 < x) (hz : 0 ≤ z) (hzp : mu < 0 → 0 < z) :
    (z ^ mu - x ^ mu) / mu ≤ x ^ (mu - 1) * (z - x) := by
  by_cases he : z = x
  · simp [he]
  · exact (normalizedPower_tangent_lt hmu hm0 hx hz hzp he).le

end Kreps.ConsumerDemand
