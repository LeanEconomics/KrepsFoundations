/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex

/-!
# One-sided derivatives of a capped absolute value

The piecewise linear coordinate slices used for Problem 3.13 have finite
one-sided derivatives everywhere. Writing the cap as the difference of two
convex real functions lets Mathlib's convex one-sided derivative theorem
handle all kink locations, including coincident kinks.
-/

namespace Kreps.ConsumerDemand

open Set

/-- A capped absolute value is a difference of two convex functions. -/
theorem cappedAbs_eq_difference (b c t : ℝ) :
    min |t - b| c = |t - b| - max (|t - b| - c) 0 := by
  by_cases h : |t - b| ≤ c
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

/-- Both one-sided derivatives of a capped absolute value exist at every real point. -/
theorem cappedAbs_one_sided (b c t : ℝ) :
    DifferentiableWithinAt ℝ (fun r => min |r - b| c) (Iic t) t ∧
      DifferentiableWithinAt ℝ (fun r => min |r - b| c) (Ici t) t := by
  have hf : ConvexOn ℝ univ (fun r : ℝ => |r - b|) := by
    simpa only [Real.dist_eq] using convexOn_univ_dist b
  have hg : ConvexOn ℝ univ (fun r : ℝ => max (|r - b| - c) 0) := by
    convert! (hf.add_const (-c)).sup (convexOn_const (0 : ℝ) convex_univ) using 1
  have hmem : t ∈ interior (univ : Set ℝ) := by simp
  constructor
  · have hd := (hf.hasDerivWithinAt_leftDeriv_of_mem_interior hmem).sub
      (hg.hasDerivWithinAt_leftDeriv_of_mem_interior hmem)
    convert! hd.Iic_of_Iio.differentiableWithinAt using 1
    funext r
    exact cappedAbs_eq_difference b c r
  · have hd := (hf.hasDerivWithinAt_rightDeriv_of_mem_interior hmem).sub
      (hg.hasDerivWithinAt_rightDeriv_of_mem_interior hmem)
    convert! hd.Ici_of_Ioi.differentiableWithinAt using 1
    funext r
    exact cappedAbs_eq_difference b c r

end Kreps.ConsumerDemand
