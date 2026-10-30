/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Boundary-compatible first-order conditions

Kreps I, Chapter 3, pp. 57-62, and Appendix 5, pp. 479-484.
Derivatives within the consumption domain retain the one-sided boundary convention.
These preliminary directional lemmas do not yet assert the multiplier theorem.
-/

namespace Kreps.ConsumerDemand

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every feasible segment from a maximum has nonpositive first-order utility change. -/
theorem feasible_segment_derivative_nonpos {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x y : E} (hmax : IsMaxOn u feasible x)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hsegment : segment ℝ x y ⊆ feasible) : D (y - x) ≤ 0 :=
  hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hd.mono hsub)
    (sub_mem_posTangentConeAt_of_segment_subset hsegment)

/-- On a convex feasible region every feasible point gives a first-order inequality. -/
theorem convex_firstOrderNecessary {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x : E} (hmax : IsMaxOn u feasible x)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hc : Convex ℝ feasible) (hx : x ∈ feasible) :
    ∀ y ∈ feasible, D (y - x) ≤ 0 := by
  intro y hy
  exact feasible_segment_derivative_nonpos hmax hd hsub (hc.segment_subset hx hy)

end Kreps.ConsumerDemand
