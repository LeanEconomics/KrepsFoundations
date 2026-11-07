/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.SeparableDemand

/-!
# Quasi-linear marginal conditions, including the zero-numeraire corner

Kreps I, Problem 3.9, p. 65. Append the linear utility of the final commodity
to the strictly concave nonmoney components. The common marginal height is at
least the reciprocal of the numeraire price, with equality whenever numeraire
consumption is positive. Thus positive-numeraire choices have income-independent
nonmoney quantities. No asymptotic condition on the marginal utilities is added.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- Append the source's linear final commodity to the nonlinear component family. -/
def SeparableMarginals.withNumeraire (U : SeparableMarginals k) : SeparableMarginals (k + 1) where
  utility := Fin.lastCases (fun t => t) U.utility
  marginal := Fin.lastCases (fun _ => 1) U.marginal
  concave := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => le_rfl⟩
    · simpa only [Fin.lastCases_castSucc] using U.concave j
  increasing := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact fun _ _ _ _ h => h
    · simpa only [Fin.lastCases_castSucc] using U.increasing j
  hasDeriv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact fun t _ => (hasDerivAt_id t).hasDerivWithinAt
    · simpa only [Fin.lastCases_castSucc] using U.hasDeriv j
  continuous_marginal := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact continuousOn_const
    · simpa only [Fin.lastCases_castSucc] using U.continuous_marginal j

/-- The appended objective is exactly the source's sum plus the last commodity. -/
theorem withNumeraire_total (U : SeparableMarginals k) (x : Fin (k + 1) → ℝ) :
    U.withNumeraire.total x = U.total (fun j => x j.castSucc) + x (Fin.last k) := by
  simp [SeparableMarginals.total, SeparableMarginals.withNumeraire, Fin.sum_univ_castSucc]

/-- The first prices, excluding the linear numeraire price. -/
def NonmoneyPrices (p : PositivePrices (k + 1)) : PositivePrices k :=
  ⟨fun j => p.val j.castSucc, fun j => p.property j.castSucc⟩

/-- Nonmoney quantities of a complete consumption bundle. -/
def NonmoneyBundle (x : NonnegativeOrthant (k + 1)) : NonnegativeOrthant k :=
  ⟨fun j => x.val j.castSucc, fun j => x.property j.castSucc⟩

/-- The exact clipped marginal conditions for nonlinear goods and the linear numeraire. -/
def QuasiLinearAllocation (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (y : ℝ≥0) (l : ℝ) (x : NonnegativeOrthant (k + 1)) : Prop :=
  Expenditure p x = (y : ℝ) ∧ 1 / p.val (Fin.last k) ≤ l ∧
    (∀ j, MarginalGraph U (NonmoneyPrices p) j l (x.val j.castSucc)) ∧
    (0 < x.val (Fin.last k) → l = 1 / p.val (Fin.last k))

/-- The numeraire inequalities are exactly its specialization of the common-height graph. -/
theorem quasiLinearAllocation_iff_graphical (U : SeparableMarginals k)
    (p : PositivePrices (k + 1)) (y : ℝ≥0) (l : ℝ) (x : NonnegativeOrthant (k + 1)) :
    QuasiLinearAllocation U p y l x ↔ GraphicalAllocation U.withNumeraire p y l x := by
  have hp := p.property (Fin.last k)
  constructor
  · rintro ⟨he, hl, hn, hlast⟩
    refine ⟨(one_div_pos.mpr hp).trans_le hl, he, ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_)
    · simp only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_last]
      refine ⟨x.property _, (div_le_iff₀ hp).mp hl, ?_⟩
      intro hx
      rw [hlast hx]
      exact (div_mul_cancel₀ 1 hp.ne').symm
    · simpa only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_castSucc,
        NonmoneyPrices] using hn j
  · rintro ⟨_, he, hm⟩
    have hlast := hm (Fin.last k)
    simp only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_last] at hlast
    refine ⟨he, (div_le_iff₀ hp).mpr hlast.2.1, ?_, ?_⟩
    · intro j
      simpa only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_castSucc,
        NonmoneyPrices] using hm j.castSucc
    · intro hx
      exact ((div_eq_iff hp.ne').mpr (hlast.2.2 hx)).symm

/-- **Problem 3.9:** the full positive-income demand is exactly the quasi-linear allocation rule. -/
theorem problem_3_9 (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (x : NonnegativeOrthant (k + 1)) :
    x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y ↔
      ∃ l, QuasiLinearAllocation U p y l x := by
  rw [demand_iff_graphicalAllocation U.withNumeraire (Nat.zero_lt_succ k) p y hy x]
  exact exists_congr (fun l => (quasiLinearAllocation_iff_graphical U p y l x).symm)

/-- The quasi-linear marginal rule is sufficient at every income, including zero. -/
theorem quasiLinearAllocation_optimal (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) :
    x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y :=
  graphicalAllocation_optimal U.withNumeraire
    ((quasiLinearAllocation_iff_graphical U p y l x).mp h)

/-- A strictly larger height forces zero numeraire consumption, the low-wealth corner. -/
theorem quasiLinear_height_strict_numeraire_zero (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) (hl : 1 / p.val (Fin.last k) < l) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  apply le_of_not_gt
  intro hx
  exact hl.ne' (h.2.2.2 hx)

/-- At positive numeraire consumption, nonmoney quantities solve one income-free graph. -/
theorem quasiLinear_positive_numeraire_graph (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) (hx : 0 < x.val (Fin.last k)) :
    ∀ j, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) (x.val j.castSucc) := by
  rw [← h.2.2.2 hx]
  exact h.2.2.1

/-- Two positive-numeraire optima have identical nonmoney consumption at any two incomes. -/
theorem quasiLinear_nonmoney_independent (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {y z : ℝ≥0} {l m : ℝ}
    {x w : NonnegativeOrthant (k + 1)} (hx : QuasiLinearAllocation U p y l x)
    (hw : QuasiLinearAllocation U p z m w)
    (hxpos : 0 < x.val (Fin.last k)) (hwpos : 0 < w.val (Fin.last k)) :
    NonmoneyBundle x = NonmoneyBundle w := by
  apply Subtype.ext
  funext j
  exact marginalGraph_unique U (NonmoneyPrices p) j (hs j)
    (quasiLinear_positive_numeraire_graph U hx hxpos j)
    (quasiLinear_positive_numeraire_graph U hw hwpos j)

end Kreps.ConsumerDemand
