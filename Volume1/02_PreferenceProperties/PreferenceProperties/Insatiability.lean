/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Monotonicity
import PreferenceProperties.ConvexPreference

/-!
# Local improvements from convexity

Kreps I, Problem 2.3, p. 46. Global insatiability and semi-strict convexity give
local insatiability on a convex consumption domain. The proof makes an arbitrarily
small movement toward a better point. No continuity assumption is used.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- Distance along a mixture is its weight times the distance between the endpoints. -/
theorem mix_dist (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    dist (Mix hS y x a ha) x = a * dist y x := by
  change dist (a • y.val + (1 - a) • x.val) x.val = a * dist y.val x.val
  rw [dist_eq_norm, dist_eq_norm]
  have he : a • y.val + (1 - a) • x.val - x.val = a • (y.val - x.val) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]

/-- **Problem 2.3**, the positive implication, for any convex normed-space domain. -/
theorem problem_2_3_implication {hS : Convex ℝ S} {r : S → S → Prop}
    (hg : GloballyInsatiable r) (hs : SemiStrictlyConvexPreference hS r) :
    LocallyInsatiable r := by
  intro x ε hε
  obtain ⟨y, hy⟩ := hg x
  let a := min (1 / 2 : ℝ) (ε / (dist y x + 1))
  have hd : 0 < dist y x + 1 := by positivity
  have ha0 : 0 < a := lt_min (by norm_num) (div_pos hε hd)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ha : a ∈ Set.Icc 0 1 := ⟨ha0.le, ha1.le⟩
  refine ⟨Mix hS y x a ha, ?_, hs.2 y x hy a ⟨ha0, ha1⟩⟩
  rw [mix_dist]
  have hbound : a * (dist y x + 1) ≤ ε :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  nlinarith

/-- Strict convexity is a sufficient special case. -/
theorem strictlyConvex_global_local {hS : Convex ℝ S} {r : S → S → Prop}
    (hc : Complete r) (hg : GloballyInsatiable r) (hs : StrictlyConvexPreference hS r) :
    LocallyInsatiable r :=
  problem_2_3_implication hg (strictlyConvex_semiStrict hc hs)

end Kreps.PreferenceProperties
