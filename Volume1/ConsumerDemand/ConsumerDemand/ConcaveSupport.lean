/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Concave supporting inequalities within the consumption domain

Kreps I, Proposition 3.5(b), p. 57, and the proof of Proposition A5.4, p. 484.
A derivative within a convex domain bounds every secant of a concave function.
The proof restricts to the segment from the candidate to the comparison point and
uses Mathlib's one-dimensional right-hand derivative bound. No open neighborhood
of the candidate is assumed, so the result includes boundary consumption bundles.
-/

namespace Kreps.ConsumerDemand

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A concave function lies below its supporting derivative, including at domain boundaries. -/
theorem concave_support_le {u : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {x y : E}
    (hu : ConcaveOn ℝ S u) (hd : HasFDerivWithinAt u D S x)
    (hx : x ∈ S) (hy : y ∈ S) : u y - u x ≤ D (y - x) := by
  have hmap : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) S :=
    hu.1.mapsTo_lineMap hx hy
  have hline : ConcaveOn ℝ (Icc (0 : ℝ) 1) (u ∘ AffineMap.lineMap x y) :=
    (hu.comp_affineMap (AffineMap.lineMap x y)).subset hmap (convex_Icc 0 1)
  have hdline : HasDerivWithinAt (u ∘ AffineMap.lineMap x y) (D (y - x))
      (Icc (0 : ℝ) 1) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivWithinAt_lineMap hmap (by simp)
  have hbound := hline.slope_le_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_lt_one hdline
  simpa [slope_def_field] using hbound

/-- The equivalent tangent upper bound used in the proof of Proposition A5.4. -/
theorem concave_support_upper {u : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {x y : E}
    (hu : ConcaveOn ℝ S u) (hd : HasFDerivWithinAt u D S x)
    (hx : x ∈ S) (hy : y ∈ S) : u y ≤ u x + D (y - x) := by
  have h := concave_support_le hu hd hx hy
  linarith

/-- Nonpositive first-order changes toward every feasible point suffice for a concave maximum. -/
theorem concave_firstOrderSufficient {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x : E} (hu : ConcaveOn ℝ domain u)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hx : x ∈ feasible) (hfirst : ∀ y ∈ feasible, D (y - x) ≤ 0) :
    IsMaxOn u feasible x := by
  intro y hy
  have h := concave_support_le hu hd (hsub hx) (hsub hy)
  have hzero := hfirst y hy
  change u y ≤ u x
  exact sub_nonpos.mp (h.trans hzero)

end Kreps.ConsumerDemand
