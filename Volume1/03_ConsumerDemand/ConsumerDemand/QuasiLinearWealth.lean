/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.QuasiLinearUniqueness

/-!
# The quasi-linear wealth threshold and its possible absence

Kreps I, Problem 3.9, p. 65. If the nonmoney marginal intersections at the
reciprocal numeraire price exist, their cost is the exact wealth threshold.
At and above it, demand buys those fixed nonmoney quantities and spends the
residual on the numeraire. Below it, numeraire demand is zero. Without such
finite intersections, numeraire demand is zero at every income; the source's
assumptions do not impose a zero limiting marginal utility.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- The income-independent nonmoney intersections at the numeraire's marginal height. -/
def NumeraireTarget (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (q : NonnegativeOrthant k) : Prop :=
  ∀ j, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) (q.val j)

/-- Buy fixed nonmoney quantities and allocate all remaining income to the last good. -/
noncomputable def NumeraireResidualBundle (p : PositivePrices (k + 1))
    (q : NonnegativeOrthant k) (y : ℝ≥0)
    (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) : NonnegativeOrthant (k + 1) :=
  ⟨Fin.lastCases (((y : ℝ) - Expenditure (NonmoneyPrices p) q) / p.val (Fin.last k)) q.val, by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last, Pi.zero_apply] using
        div_nonneg (sub_nonneg.mpr hy) (p.property (Fin.last k)).le
    · simpa only [Fin.lastCases_castSucc, Pi.zero_apply] using q.property j⟩

/-- The residual construction preserves every nonmoney quantity. -/
theorem nonmoney_residualBundle (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    NonmoneyBundle (NumeraireResidualBundle p q y hy) = q := by
  apply Subtype.ext
  ext j
  simp [NonmoneyBundle, NumeraireResidualBundle]

/-- The residual construction exhausts the stated income exactly. -/
theorem residualBundle_expenditure (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    Expenditure p (NumeraireResidualBundle p q y hy) = (y : ℝ) := by
  rw [expenditure_nonmoney_split, nonmoney_residualBundle]
  simp only [NumeraireResidualBundle, Fin.lastCases_last]
  rw [mul_div_cancel₀ _ (p.property _).ne']
  ring

/-- At and above the target cost, the source's residual-income formula is optimal. -/
theorem numeraire_target_optimal (U : SeparableMarginals k)
    (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k) (hq : NumeraireTarget U p q)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    NumeraireResidualBundle p q y hy ∈
      MarshallianDemand (fun z => U.withNumeraire.total z.val) p y := by
  apply quasiLinearAllocation_optimal U (l := 1 / p.val (Fin.last k))
  refine ⟨residualBundle_expenditure p q y hy, le_rfl, ?_, fun _ => rfl⟩
  intro j
  simpa only [NumeraireResidualBundle, Fin.lastCases_castSucc] using hq j

/-- Strict concavity makes the high-wealth formula the entire demand set. -/
theorem numeraire_target_demand (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k) (hq : NumeraireTarget U p q)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    MarshallianDemand (fun z => U.withNumeraire.total z.val) p y =
      {NumeraireResidualBundle p q y hy} := by
  have hopt := numeraire_target_optimal U p q hq y hy
  ext x
  exact ⟨fun hx => Set.mem_singleton_iff.mpr
    (quasiLinear_demand_subsingleton U hs p y hx hopt),
    fun hx => (Set.mem_singleton_iff.mp hx).symm ▸ hopt⟩

/-- Positive numeraire consumption forces a finite target and strictly exceeds its cost. -/
theorem positive_numeraire_target (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y)
    (hxpos : 0 < x.val (Fin.last k)) :
    NumeraireTarget U p (NonmoneyBundle x) ∧
      Expenditure (NonmoneyPrices p) (NonmoneyBundle x) < (y : ℝ) := by
  have hcostpos : 0 < p.val (Fin.last k) * x.val (Fin.last k) :=
    mul_pos (p.property _) hxpos
  have hy : 0 < (y : ℝ) :=
    hcostpos.trans_le ((commodity_expenditure_le p x _).trans hx.1)
  obtain ⟨l, hl⟩ := (problem_3_9 U p y hy x).mp hx
  refine ⟨quasiLinear_positive_numeraire_graph U hl hxpos, ?_⟩
  have he := hl.1
  rw [expenditure_nonmoney_split] at he
  linarith

/-- Two finite nonmoney targets coincide under the source's strict component concavity. -/
theorem numeraire_target_unique (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {q t : NonnegativeOrthant k}
    (hq : NumeraireTarget U p q) (ht : NumeraireTarget U p t) : q = t := by
  apply Subtype.ext
  funext j
  exact marginalGraph_unique U (NonmoneyPrices p) j (hs j) (hq j) (ht j)

/-- Below the target cost, the unique optimum consumes no numeraire. -/
theorem below_target_numeraire_zero (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {q : NonnegativeOrthant k} (hq : NumeraireTarget U p q)
    {y : ℝ≥0} (hy : (y : ℝ) ≤ Expenditure (NonmoneyPrices p) q)
    {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  apply le_of_not_gt
  intro hxpos
  obtain ⟨ht, hcost⟩ := positive_numeraire_target U hx hxpos
  rw [numeraire_target_unique U hs ht hq] at hcost
  exact (not_lt_of_ge hy) hcost

/-- If the finite target does not exist, the numeraire remains unconsumed at every income. -/
theorem no_target_numeraire_zero (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} (hn : ¬∃ q, NumeraireTarget U p q)
    {y : ℝ≥0} {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  exact le_of_not_gt (fun hp => hn ⟨_, (positive_numeraire_target U hx hp).1⟩)

end Kreps.ConsumerDemand
