/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Arrow–Pratt risk aversion and power utility

Kreps I, Definition 6.10 and the relative coefficient, pp. 130–132, and Problem
6.4, p. 141. Economic uses impose positive marginal utility and appropriate
differentiability at the wealth being evaluated.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- **Definition 6.10:** the Arrow–Pratt coefficient of absolute risk aversion. -/
noncomputable def AbsoluteRiskAversion (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv U) x) / deriv U x

/-- Relative risk aversion measures curvature in proportion to wealth. -/
noncomputable def RelativeRiskAversion (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * AbsoluteRiskAversion U x

/-- Nonpositive utility curvature and strictly positive marginal utility imply nonnegative risk. -/
theorem absoluteRiskAversion_nonneg {U : ℝ → ℝ} {x : ℝ} (h₁ : 0 < deriv U x)
    (h₂ : deriv (deriv U) x ≤ 0) : 0 ≤ AbsoluteRiskAversion U x :=
  div_nonneg (neg_nonneg.mpr h₂) h₁.le

/-- The power utility specified in Problem 6.4, economically restricted to positive wealth. -/
noncomputable def PowerUtility (a x : ℝ) : ℝ := x ^ a / a

/-- The first derivative on the positive wealth domain. -/
theorem powerUtility_hasDerivAt {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    HasDerivAt (PowerUtility a) (x ^ (a - 1)) x := by
  unfold PowerUtility
  convert (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).div_const a using 1
  field_simp

/-- The second derivative on the positive wealth domain. -/
theorem powerUtility_second_deriv {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    deriv (deriv (PowerUtility a)) x = (a - 1) * x ^ (a - 1 - 1) := by
  have he : deriv (PowerUtility a) =ᶠ[𝓝 x] fun y : ℝ => y ^ (a - 1) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (powerUtility_hasDerivAt ha hy).deriv
  rw [he.deriv_eq, Real.deriv_rpow_const]

/-- **Problem 6.4:** absolute risk aversion is inversely proportional to wealth;
relative risk aversion is constant. -/
theorem problem_6_4 {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    AbsoluteRiskAversion (PowerUtility a) x = (1 - a) / x ∧
      RelativeRiskAversion (PowerUtility a) x = 1 - a := by
  have hpow := (Real.rpow_pos_of_pos hx (a - 1)).ne'
  have he : AbsoluteRiskAversion (PowerUtility a) x = (1 - a) / x := by
    rw [AbsoluteRiskAversion, powerUtility_second_deriv ha hx,
      (powerUtility_hasDerivAt ha hx).deriv,
      Real.rpow_sub_one hx.ne' (a - 1)]
    field_simp
    ring
  refine ⟨he, ?_⟩
  rw [RelativeRiskAversion, he]
  field_simp

/-- A positive affine utility is risk neutral in the Arrow–Pratt sense. -/
theorem absoluteRiskAversion_affine (A B x : ℝ) :
    AbsoluteRiskAversion (fun z : ℝ => A * z + B) x = 0 := by
  have h (y : ℝ) : deriv (fun z : ℝ => A * z + B) y = A := by
    simp
  rw [AbsoluteRiskAversion, funext h]
  simp

end Kreps.UtilityForMoney
