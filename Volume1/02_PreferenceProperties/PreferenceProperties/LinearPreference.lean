/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.HomotheticIdentification
import PreferenceProperties.ConcaveUtility
import PreferenceProperties.MonotonicityExamples
import PreferenceProperties.Rationalization

/-!
# Positive linear utility on two goods

Kreps I, Problem 2.9a, p. 47. Positive coefficients give monotone, strictly monotone,
locally insatiable, convex, semi-strictly convex and continuous preferences, but
not strictly convex preferences. Indifference curves are the feasible portions
of straight lines with slope `-α/β`.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The two-good linear utility in Problem 2.9a. -/
def TwoGoodLinearUtility (α β : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  α * x.val 0 + β * x.val 1

/-- Utility of a mixture is the mixture of utilities. -/
theorem twoGoodLinearUtility_mix (α β : ℝ) (x y : NonnegativeOrthant 2)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    TwoGoodLinearUtility α β (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ha) =
      a * TwoGoodLinearUtility α β x + (1 - a) * TwoGoodLinearUtility α β y := by
  change α * (a * x.val 0 + (1 - a) * y.val 0) +
    β * (a * x.val 1 + (1 - a) * y.val 1) =
    a * (α * x.val 0 + β * x.val 1) + (1 - a) * (α * y.val 0 + β * y.val 1)
  ring

/-- Linear utility is concave, with equality in Jensen's inequality. -/
theorem twoGoodLinearUtility_concave (α β : ℝ) :
    ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) (TwoGoodLinearUtility α β) :=
  fun x y a ha => (twoGoodLinearUtility_mix α β x y a ha).ge

/-- Linear utility is continuous on the entire closed orthant. -/
theorem twoGoodLinearUtility_continuous (α β : ℝ) : Continuous (TwoGoodLinearUtility α β) :=
  (continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)).add
    (continuous_const.mul ((continuous_apply 1).comp continuous_subtype_val))

/-- Positive coefficients make every nontrivial coordinatewise increase strictly beneficial. -/
theorem twoGoodLinearUtility_strictMono {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictMono (TwoGoodLinearUtility α β) := by
  intro x y hxy
  have h0 := mul_le_mul_of_nonneg_left (hxy.le 0) hα.le
  have h1 := mul_le_mul_of_nonneg_left (hxy.le 1) hβ.le
  by_contra h
  have hsum : α * y.val 0 + β * y.val 1 ≤ α * x.val 0 + β * x.val 1 := le_of_not_gt h
  have he0 : α * x.val 0 = α * y.val 0 := by linarith
  have he1 : β * x.val 1 = β * y.val 1 := by linarith
  apply hxy.ne
  apply Subtype.ext
  funext j
  fin_cases j
  · exact mul_left_cancel₀ (ne_of_gt hα) he0
  · exact mul_left_cancel₀ (ne_of_gt hβ) he1

/-- Two distinct bundles on the same line refute strict convexity. -/
theorem twoGoodLinearPreference_not_strictlyConvex {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) := by
  let x := PairBundle β 0 hβ.le le_rfl
  let y := PairBundle 0 α le_rfl hα.le
  have hne : x ≠ y := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant 2 => z.val 0) h
    have hβ0 : β = 0 := by simpa [x, y, PairBundle] using he
    exact (ne_of_gt hβ) hβ0
  have hx : TwoGoodLinearUtility α β x = α * β := by
    simp [x, TwoGoodLinearUtility, PairBundle]
  have hy : TwoGoodLinearUtility α β y = α * β := by
    simp [y, TwoGoodLinearUtility, PairBundle, mul_comm]
  have hxy : UtilityPref (TwoGoodLinearUtility α β) x y := by
    change TwoGoodLinearUtility α β y ≤ TwoGoodLinearUtility α β x
    rw [hx, hy]
  intro h
  have hs := h x y hne hxy (1 / 2) (by constructor <;> norm_num)
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  have hm := (strict_iff_utility_lt hu _ _).mp hs
  norm_num [TwoGoodLinearUtility, Mix, x, y, PairBundle, smul_eq_mul] at hm
  nlinarith

/-- Linear utility is degree-one homogeneous, including at the origin. -/
theorem twoGoodLinearUtility_homogeneous (α β : ℝ) :
    HomogeneousUtility (TwoGoodLinearUtility α β) := by
  intro t x
  change α * ((t : ℝ) * x.val 0) + β * ((t : ℝ) * x.val 1) =
    (t : ℝ) * (α * x.val 0 + β * x.val 1)
  ring

/-- Each indifference curve is a straight line intersected with the nonnegative orthant. -/
theorem twoGoodLinear_indifference_curve (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (p x : NonnegativeOrthant 2) :
    Indifferent (UtilityPref (TwoGoodLinearUtility α β)) x p ↔
      x.val 1 = (TwoGoodLinearUtility α β p - α * x.val 0) / β := by
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  rw [indifferent_iff_utility_eq hu, eq_div_iff hβ]
  unfold TwoGoodLinearUtility
  constructor <;> intro h <;> nlinarith

/-- **Problem 2.9a:** all seven properties, including failure of strict convexity. -/
theorem problem_2_9a {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    MonotonePreference (UtilityPref (TwoGoodLinearUtility α β)) ∧
    StrictlyMonotonePreference (UtilityPref (TwoGoodLinearUtility α β)) ∧
    LocallyInsatiable (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) ∧
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ContinuousPreference (UtilityPref (TwoGoodLinearUtility α β)) := by
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  have hs := (proposition_2_2_strict hu).mpr (twoGoodLinearUtility_strictMono hα hβ)
  have hc := twoGoodLinearUtility_concave α β
  exact ⟨strictlyMonotone_monotone (proposition_1_3a _).1 hs, hs,
    strictAllIncrease_locallyInsatiable (strictlyMonotone_strictAllIncrease (by decide) hs),
    proposition_2_8a_concave hu hc, twoGoodLinearPreference_not_strictlyConvex hα hβ,
    (proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc),
    proposition_2_9_forward hu (twoGoodLinearUtility_continuous α β)⟩

end Kreps.PreferenceProperties
