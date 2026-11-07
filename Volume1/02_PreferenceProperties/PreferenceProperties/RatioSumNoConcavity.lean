/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RatioSumUtility
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The nonexistence proof in Problem 2.8b

Indifference along rays forces a concave representation to retain at least half
an increment when its rank interval contracts by three sevenths. Iterating this
inequality contradicts the concave secant bound on the commodity axis: after
rescaling, the bound tends to zero at the geometric rate `(6/7)^n`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Equal values of the displayed utility give equal values in every representation. -/
theorem ratioSum_rep_eq_of_value_eq {u : NonnegativeOrthant 2 → ℝ}
    (hu : Represents u (UtilityPref RatioSumUtility)) {x y : NonnegativeOrthant 2}
    (he : RatioSumUtility x = RatioSumUtility y) : u x = u y := by
  apply le_antisymm
  · exact (hu y x).mp (by change RatioSumUtility x ≤ RatioSumUtility y; rw [he])
  · exact (hu x y).mp (by change RatioSumUtility y ≤ RatioSumUtility x; rw [he])

/-- Equal-weight physical mixing imposes an excessive lower bound on rank increments. -/
theorem ratioSum_concave_increment {u : NonnegativeOrthant 2 → ℝ}
    (hu : Represents u (UtilityPref RatioSumUtility))
    (hc : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    (1 / 2) * (u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2))) ≤
      u (RatioAxisBundle (1 / 2 + (3 / 7) * δ)) - u (RatioAxisBundle (1 / 2)) := by
  have hq : u (RatioRayBundle δ hδ) = u (RatioAxisBundle (1 / 2 + δ)) :=
    ratioSum_rep_eq_of_value_eq hu ((ratioSumUtility_ray hδ hδ').trans
      (ratioSumUtility_axis (by positivity)).symm)
  have hm : u (Mix (convex_Ici (0 : Fin 2 → ℝ))
      (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ) (1 / 2) ⟨by norm_num, by norm_num⟩) =
      u (RatioAxisBundle (1 / 2 + (3 / 7) * δ)) :=
    ratioSum_rep_eq_of_value_eq hu ((ratioSumUtility_ray_mix hδ hδ').trans
      (ratioSumUtility_axis (by positivity)).symm)
  have hj := hc (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ)
    (1 / 2) ⟨by norm_num, by norm_num⟩
  have hj' := hj.trans_eq hm
  rw [hq] at hj'
  linarith

/-- **Problem 2.8b:** no concave function can represent the ratio-and-sum preference. -/
theorem problem_2_8b_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref RatioSumUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hc⟩
  let g : ℝ → ℝ := fun t => u (RatioAxisBundle t)
  let d : ℕ → ℝ := fun n => (1 / 4) * (3 / 7 : ℝ) ^ n
  have hd (n : ℕ) : 0 < d n ∧ d n ≤ 1 / 4 := by
    have hp : 0 < (3 / 7 : ℝ) ^ n := pow_pos (by norm_num) n
    have hp' : (3 / 7 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [d]
    constructor <;> nlinarith
  have hdstep (n : ℕ) : d (n + 1) = (3 / 7) * d n := by
    dsimp [d]
    rw [pow_succ]
    ring
  have hlower (n : ℕ) : (1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2)) ≤
      g (1 / 2 + d n) - g (1 / 2) := by
    induction n with
    | zero => norm_num [d]
    | succ n ih =>
      have hr := ratioSum_concave_increment hu hc (hd n).1.le (hd n).2
      change (1 / 2) * (g (1 / 2 + d n) - g (1 / 2)) ≤
        g (1 / 2 + (3 / 7) * d n) - g (1 / 2) at hr
      rw [← hdstep n] at hr
      rw [pow_succ]
      nlinarith
  have hbound (n : ℕ) : (1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2)) ≤
      (3 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
    have hup := concaveUtility_ratioAxis_bound hc (hd n).1
    change g (1 / 2 + d n) - g (1 / 2) ≤ 2 * d n * (g (1 / 2) - g 0) at hup
    have hl := hlower n
    dsimp [d] at hup
    nlinarith
  have hscaled (n : ℕ) : g (3 / 4) - g (1 / 2) ≤
      (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
    calc
      g (3 / 4) - g (1 / 2) =
          (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2))) := by
            rw [← mul_assoc, ← mul_pow]
            norm_num
      _ ≤ (2 : ℝ) ^ n * ((3 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2)) :=
        mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (by norm_num) n)
      _ = (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
  have hlim : Filter.Tendsto
      (fun n : ℕ => (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2)) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 6 / 7)
        (by norm_num : (6 / 7 : ℝ) < 1)).mul_const ((g (1 / 2) - g 0) / 2)
  have hle : g (3 / 4) - g (1 / 2) ≤ 0 := ge_of_tendsto' hlim hscaled
  have hstrict : Strict (UtilityPref RatioSumUtility)
      (RatioAxisBundle (3 / 4)) (RatioAxisBundle (1 / 2)) := by
    change RatioSumUtility (RatioAxisBundle (1 / 2)) ≤
        RatioSumUtility (RatioAxisBundle (3 / 4)) ∧
      ¬ RatioSumUtility (RatioAxisBundle (3 / 4)) ≤ RatioSumUtility (RatioAxisBundle (1 / 2))
    rw [ratioSumUtility_axis (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ratioSumUtility_axis (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  have hlt := (strict_iff_utility_lt hu _ _).mp hstrict
  change g (1 / 2) < g (3 / 4) at hlt
  linarith

end Kreps.PreferenceProperties
