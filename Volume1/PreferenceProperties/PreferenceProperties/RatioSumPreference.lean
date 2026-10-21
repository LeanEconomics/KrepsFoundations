/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RatioSumNoConcavity
import PreferenceProperties.DiagonalRepresentation
import PreferenceProperties.Rationalization

/-!
# Continuous semi-strictly convex preferences without concave representation

Kreps I, Problem 2.8b. Every contour is a half-space cut out by a linear form
whose coefficient depends on the rank. This gives continuity and semi-strict
convexity, completing the counterexample alongside the no-representation theorem.
-/

namespace Kreps.PreferenceProperties

/-- Below the dividing line, the denominator is positive. -/
theorem ratioSum_denominator_pos {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 ≤ 1) : 0 < 2 - x.val 0 := by
  have hx₁ := x.property 1
  change 0 ≤ x.val 1 at hx₁
  linarith

/-- The fractional branch takes values at most one. -/
theorem ratioSumUtility_low_le_one {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 ≤ 1) : RatioSumUtility x ≤ 1 := by
  rw [RatioSumUtility, ite_eq_left hx]
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (ratioSum_denominator_pos hx)).mpr
  nlinarith

/-- Both branches of the utility are nonnegative. -/
theorem ratioSumUtility_nonneg (x : NonnegativeOrthant 2) : 0 ≤ RatioSumUtility x := by
  have hx₀ : 0 ≤ x.val 0 := x.property 0
  have hx₁ : 0 ≤ x.val 1 := x.property 1
  by_cases hx : x.val 0 + x.val 1 ≤ 1
  · rw [RatioSumUtility, ite_eq_left hx]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (ratioSum_denominator_pos hx)).mpr
    nlinarith
  · rw [RatioSumUtility, ite_eq_right hx]
    linarith

/-- The linear form defining an upper contour at the given nonnegative rank. -/
noncomputable def RatioRankLinearForm (c : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  min (c + 1) 2 * x.val 0 + 2 * x.val 1

/-- Above the dividing line every rank at most one is strictly exceeded. -/
theorem ratioRankLinearForm_high {x : NonnegativeOrthant 2} {c : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hx : 1 < x.val 0 + x.val 1) :
    2 * c < RatioRankLinearForm c x := by
  have hx₁ : 0 ≤ x.val 1 := x.property 1
  rw [RatioRankLinearForm, min_eq_left (by linarith)]
  have hmain := mul_pos (show 0 < c + 1 by linarith) (sub_pos.mpr hx)
  have htail := mul_nonneg (sub_nonneg.mpr hc₁) hx₁
  nlinarith

/-- A weak upper utility contour is exactly a linear half-space. -/
theorem ratioSumUtility_le_iff {x : NonnegativeOrthant 2} {c : ℝ} (hc : 0 ≤ c) :
    c ≤ RatioSumUtility x ↔ 2 * c ≤ RatioRankLinearForm c x := by
  by_cases hc₁ : c ≤ 1
  · by_cases hx : x.val 0 + x.val 1 ≤ 1
    · rw [RatioSumUtility, ite_eq_left hx, RatioRankLinearForm, min_eq_left (by linarith)]
      rw [le_sub_iff_add_le, le_div_iff₀ (ratioSum_denominator_pos hx)]
      constructor <;> intro h <;> nlinarith
    · have hform := ratioRankLinearForm_high hc hc₁ (lt_of_not_ge hx)
      rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h
      · exact hform.le
      · linarith
  · have hc₁' : 1 < c := lt_of_not_ge hc₁
    rw [RatioRankLinearForm, min_eq_right (by linarith)]
    by_cases hx : x.val 0 + x.val 1 ≤ 1
    · have hu := ratioSumUtility_low_le_one hx
      constructor <;> intro h <;> nlinarith
    · rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h <;> nlinarith

/-- A strict upper utility contour is the corresponding open half-space. -/
theorem ratioSumUtility_lt_iff {x : NonnegativeOrthant 2} {c : ℝ} (hc : 0 ≤ c) :
    c < RatioSumUtility x ↔ 2 * c < RatioRankLinearForm c x := by
  by_cases hc₁ : c ≤ 1
  · by_cases hx : x.val 0 + x.val 1 ≤ 1
    · rw [RatioSumUtility, ite_eq_left hx, RatioRankLinearForm, min_eq_left (by linarith)]
      rw [lt_sub_iff_add_lt, lt_div_iff₀ (ratioSum_denominator_pos hx)]
      constructor <;> intro h <;> nlinarith
    · have hform := ratioRankLinearForm_high hc hc₁ (lt_of_not_ge hx)
      rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h
      · exact hform
      · linarith
  · have hc₁' : 1 < c := lt_of_not_ge hc₁
    rw [RatioRankLinearForm, min_eq_right (by linarith)]
    by_cases hx : x.val 0 + x.val 1 ≤ 1
    · have hu := ratioSumUtility_low_le_one hx
      constructor <;> intro h <;> nlinarith
    · rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h <;> nlinarith

/-- The two displayed branches agree at total consumption one. -/
theorem ratioSumUtility_boundary {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 = 1) : RatioSumUtility x = 1 := by
  apply le_antisymm (ratioSumUtility_low_le_one hx.le)
  apply (ratioSumUtility_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  norm_num [RatioRankLinearForm]
  linarith

/-- At the bundle's own rank its contour equation holds with equality. -/
theorem ratioRankLinearForm_self (x : NonnegativeOrthant 2) :
    RatioRankLinearForm (RatioSumUtility x) x = 2 * RatioSumUtility x := by
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((ratioSumUtility_lt_iff (ratioSumUtility_nonneg x)).mpr h)
  · exact (ratioSumUtility_le_iff (ratioSumUtility_nonneg x)).mp le_rfl

/-- The contour form is linear in consumption mixtures. -/
theorem ratioRankLinearForm_mix (c : ℝ) (x y : NonnegativeOrthant 2)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    RatioRankLinearForm c (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ha) =
      a * RatioRankLinearForm c x + (1 - a) * RatioRankLinearForm c y := by
  dsimp [RatioRankLinearForm, Mix]
  ring

/-- The ratio-and-sum preference is convex on the full orthant. -/
theorem ratioSumPreference_convex :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref RatioSumUtility) := by
  intro x y hxy a ha
  apply (ratioSumUtility_le_iff (ratioSumUtility_nonneg y)).mpr
  have hm := ratioRankLinearForm_mix (RatioSumUtility y) x y a ha
  have hy := ratioRankLinearForm_self y
  have hx := (ratioSumUtility_le_iff (ratioSumUtility_nonneg y)).mp hxy
  have hlin : 2 * RatioSumUtility y ≤ a * RatioRankLinearForm (RatioSumUtility y) x +
      (1 - a) * RatioRankLinearForm (RatioSumUtility y) y := by
    have hyeq := congrArg (fun v : ℝ => (1 - a) * v) hy
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx)]
  exact hlin.trans_eq hm.symm

/-- Strictly better endpoints improve every interior mixture strictly over the lower rank. -/
theorem ratioSumPreference_semiStrict :
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref RatioSumUtility) := by
  refine ⟨ratioSumPreference_convex, ?_⟩
  intro x y hxy a ha
  have hu : Represents RatioSumUtility (UtilityPref RatioSumUtility) := fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ y).mpr
  apply (ratioSumUtility_lt_iff (ratioSumUtility_nonneg y)).mpr
  have hm := ratioRankLinearForm_mix (RatioSumUtility y) x y a ⟨ha.1.le, ha.2.le⟩
  have hy := ratioRankLinearForm_self y
  have hx := (ratioSumUtility_lt_iff (ratioSumUtility_nonneg y)).mp
    ((strict_iff_utility_lt hu x y).mp hxy)
  have hlin : 2 * RatioSumUtility y < a * RatioRankLinearForm (RatioSumUtility y) x +
      (1 - a) * RatioRankLinearForm (RatioSumUtility y) y := by
    nlinarith [mul_pos ha.1 (sub_pos.mpr hx)]
  exact hlin.trans_eq hm.symm

/-- Every fixed-rank contour form is continuous. -/
theorem ratioRankLinearForm_continuous (c : ℝ) : Continuous (RatioRankLinearForm c) :=
  (((continuous_apply 0).comp continuous_subtype_val).const_mul _).add
    (((continuous_apply 1).comp continuous_subtype_val).const_mul _)

/-- The weak upper and lower contours are closed linear half-spaces. -/
theorem ratioSumPreference_continuous : ContinuousPreference (UtilityPref RatioSumUtility) := by
  apply (proposition_1_14c (proposition_1_3a RatioSumUtility)).mpr
  intro x
  have hn := ratioSumUtility_nonneg x
  have hlo : NoBetterThan (UtilityPref RatioSumUtility) x =
      {y | RatioRankLinearForm (RatioSumUtility x) y ≤ 2 * RatioSumUtility x} := by
    ext y
    change RatioSumUtility y ≤ RatioSumUtility x ↔
      RatioRankLinearForm (RatioSumUtility x) y ≤ 2 * RatioSumUtility x
    constructor
    · intro h
      apply le_of_not_gt
      intro hf
      exact not_lt_of_ge h ((ratioSumUtility_lt_iff hn).mpr hf)
    · intro h
      apply le_of_not_gt
      intro hf
      exact not_lt_of_ge h ((ratioSumUtility_lt_iff hn).mp hf)
  have hhi : NoWorseThan (UtilityPref RatioSumUtility) x =
      {y | 2 * RatioSumUtility x ≤ RatioRankLinearForm (RatioSumUtility x) y} := by
    ext y
    exact ratioSumUtility_le_iff hn
  rw [hlo, hhi]
  exact ⟨isClosed_le (ratioRankLinearForm_continuous _) continuous_const,
    isClosed_le continuous_const (ratioRankLinearForm_continuous _)⟩

/-- The displayed utility itself is continuous, not merely its represented preference. -/
theorem ratioSumUtility_continuous : Continuous RatioSumUtility :=
  continuous_of_full_nonnegative_range (fun _ _ => Iff.rfl)
    ratioSumPreference_continuous ratioSumUtility_nonneg
    (fun c hc => ⟨RatioAxisBundle c, ratioSumUtility_axis hc⟩)

/-- **Problem 2.8b:** continuous semi-strictly convex preference with no concave representation. -/
theorem problem_2_8b :
    Rational (UtilityPref RatioSumUtility) ∧
      ContinuousPreference (UtilityPref RatioSumUtility) ∧
      SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref RatioSumUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref RatioSumUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _, ratioSumPreference_continuous, ratioSumPreference_semiStrict,
    problem_2_8b_no_concave_representation⟩

end Kreps.PreferenceProperties
