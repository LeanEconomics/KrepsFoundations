/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.QuasiLinearWealth
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of finite marginal intersections

Kreps I, Problems 3.8-3.9, p. 65. A clipped marginal intersection exists exactly
when the marginal reaches or crosses the proposed height at some finite
quantity. The intermediate value theorem supplies the intersection. Applied to
the numeraire height, this gives an exact criterion for a finite wealth threshold
without imposing an unstated limiting-marginal assumption.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- A continuous marginal curve has a clipped intersection exactly when it reaches the height. -/
theorem exists_marginalGraph_iff (U : SeparableMarginals k) (p : PositivePrices k)
    (j : Fin k) (l : ℝ) :
    (∃ q, MarginalGraph U p j l q) ↔ ∃ t, 0 ≤ t ∧ U.marginal j t ≤ l * p.val j := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.1, hq.2.1⟩
  · rintro ⟨t, ht, hmt⟩
    by_cases hzero : U.marginal j 0 ≤ l * p.val j
    · exact ⟨0, le_rfl, hzero, fun h => (lt_irrefl _ h).elim⟩
    · have hc : ContinuousOn (U.marginal j) (Icc 0 t) :=
        (U.continuous_marginal j).mono (fun _ h => h.1)
      obtain ⟨q, hq, he⟩ := intermediate_value_Icc' ht hc
        ⟨hmt, (lt_of_not_ge hzero).le⟩
      exact ⟨q, hq.1, he.le, fun _ => he⟩

/-- Strictly decreasing component curves choose zero exactly above their initial marginal. -/
theorem marginalGraph_zero_iff (U : SeparableMarginals k) (p : PositivePrices k)
    (j : Fin k) (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {l q : ℝ} (hq : MarginalGraph U p j l q) : q = 0 ↔ U.perDollar p j 0 ≤ l := by
  constructor
  · intro he
    subst q
    exact (div_le_iff₀ (p.property j)).mpr hq.2.1
  · intro h
    exact marginalGraph_unique U p j hs hq ((marginalGraph_iff U p j l 0).mpr (Or.inl ⟨rfl, h⟩))

/-- The finite numeraire threshold exists exactly when every nonmoney curve reaches its height. -/
theorem numeraireTarget_exists_iff (U : SeparableMarginals k) (p : PositivePrices (k + 1)) :
    (∃ q, NumeraireTarget U p q) ↔
      ∀ j, ∃ t, 0 ≤ t ∧ U.marginal j t ≤ p.val j.castSucc / p.val (Fin.last k) := by
  constructor
  · rintro ⟨q, hq⟩ j
    refine ⟨q.val j, q.property j, ?_⟩
    convert (hq j).2.1 using 1
    simp only [NonmoneyPrices]
    ring
  · intro h
    have hg : ∀ j, ∃ q, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) q := by
      intro j
      apply (exists_marginalGraph_iff U (NonmoneyPrices p) j _).mpr
      obtain ⟨t, ht, hm⟩ := h j
      refine ⟨t, ht, ?_⟩
      convert hm using 1
      simp only [NonmoneyPrices]
      ring
    choose q hq using hg
    exact ⟨⟨q, fun j => (hq j).1⟩, hq⟩

end Kreps.ConsumerDemand
