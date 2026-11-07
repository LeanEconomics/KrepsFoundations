/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ProductQuasiconcavity
import Mathlib.Analysis.Convex.Slope

/-!
# The ratio-and-sum utility in Problem 2.8b

Below the line where total consumption equals one, utility is a fractional-linear
function. Above that line it is the sum of consumption. These formulas agree on
the dividing line. The axis and mixture identities here support the proof that
no concave function represents the resulting preferences.
-/

namespace Kreps.PreferenceProperties

/-- The exact utility `u₃` in Problem 2.8b. -/
noncomputable def RatioSumUtility (x : NonnegativeOrthant 2) : ℝ :=
  if x.val 0 + x.val 1 ≤ 1 then 2 * (1 + x.val 1) / (2 - x.val 0) - 1
  else x.val 0 + x.val 1

/-- The nonnegative second-commodity axis, extended by clamping negative parameters to zero. -/
noncomputable def RatioAxisBundle (t : ℝ) : NonnegativeOrthant 2 :=
  PairBundle 0 (max t 0) (by norm_num) (le_max_right _ _)

/-- Along the nonnegative axis, the displayed utility equals its quantity parameter. -/
theorem ratioSumUtility_axis {t : ℝ} (ht : 0 ≤ t) :
    RatioSumUtility (RatioAxisBundle t) = t := by
  simp only [RatioSumUtility, RatioAxisBundle, PairBundle, max_eq_left ht]
  norm_num

/-- The axis parametrization respects nonnegative convex mixtures. -/
theorem ratioAxisBundle_mix {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {a : ℝ} (ha : a ∈ Set.Icc 0 1) :
    Mix (convex_Ici (0 : Fin 2 → ℝ)) (RatioAxisBundle s) (RatioAxisBundle t) a ha =
      RatioAxisBundle (a * s + (1 - a) * t) := by
  have hm : 0 ≤ a * s + (1 - a) * t :=
    add_nonneg (mul_nonneg ha.1 hs) (mul_nonneg (sub_nonneg.mpr ha.2) ht)
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [Mix, RatioAxisBundle, PairBundle, max_eq_left hs, max_eq_left ht,
    max_eq_left hm]

/-- Restricting a concave utility to the axis gives an ordinary concave real function. -/
theorem concaveUtility_ratioAxis {u : NonnegativeOrthant 2 → ℝ}
    (hu : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u) :
    ConcaveOn ℝ (Set.Ici 0) (fun t => u (RatioAxisBundle t)) := by
  refine ⟨convex_Ici _, ?_⟩
  intro s hs t ht a b ha hb hab
  have he : b = 1 - a := by linarith
  subst b
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
  have hj := hu (RatioAxisBundle s) (RatioAxisBundle t) a ha'
  rw [ratioAxisBundle_mix hs ht ha'] at hj
  exact hj

/-- The ordinary concave secant bound controls increments to the right of rank one half. -/
theorem concaveUtility_ratioAxis_bound {u : NonnegativeOrthant 2 → ℝ}
    (hu : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u) {δ : ℝ} (hδ : 0 < δ) :
    u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2)) ≤
      2 * δ * (u (RatioAxisBundle (1 / 2)) - u (RatioAxisBundle 0)) := by
  have hs := (concaveUtility_ratioAxis hu).slope_anti_adjacent
    (x := 0) (y := 1 / 2) (z := 1 / 2 + δ) (by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) + δ by linarith)
    (by norm_num) (by linarith)
  have hs' : (u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2))) / δ ≤
      2 * (u (RatioAxisBundle (1 / 2)) - u (RatioAxisBundle 0)) := by
    convert hs using 1 <;> ring
  have hmul := (div_le_iff₀ hδ).mp hs'
  nlinarith

/-- A higher-rank bundle on a shorter ray from the common center of the lower indifference lines. -/
noncomputable def RatioRayBundle (δ : ℝ) (hδ : 0 ≤ δ) : NonnegativeOrthant 2 :=
  PairBundle (1 / 2) (1 / 8 + (3 / 4) * δ) (by norm_num) (by positivity)

/-- The shorter-ray bundle has rank one half plus its increment. -/
theorem ratioSumUtility_ray {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    RatioSumUtility (RatioRayBundle δ hδ) = 1 / 2 + δ := by
  have hs : (1 / 2 : ℝ) + (1 / 8 + (3 / 4) * δ) ≤ 1 := by linarith
  norm_num [RatioSumUtility, RatioRayBundle, PairBundle, hs]
  ring

/-- Equal physical weights contract the rank increment by three sevenths. -/
theorem ratioSumUtility_ray_mix {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    RatioSumUtility (Mix (convex_Ici (0 : Fin 2 → ℝ))
      (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ) (1 / 2) ⟨by norm_num, by norm_num⟩) =
      1 / 2 + (3 / 7) * δ := by
  have hs : (1 / 2 : ℝ) * (1 / 2) +
      (1 / 2 * (1 / 2) + 1 / 2 * (1 / 8 + 3 / 4 * δ)) ≤ 1 := by linarith
  norm_num [RatioSumUtility, RatioAxisBundle, RatioRayBundle, PairBundle, Mix]
  norm_num at hs
  rw [ite_eq_left hs]
  ring

end Kreps.PreferenceProperties
