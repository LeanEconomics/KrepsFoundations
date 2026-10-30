/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.QuasiLinearDemand

/-!
# Unique quasi-linear demand

Kreps I, Problem 3.9, p. 65. Strict concavity of the nonmoney components fixes
their quantities at any two optima. Budget exhaustion then fixes the linear
numeraire as well. The proof includes zero income and does not falsely assert
strict concavity of the total utility in the numeraire direction.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- A strictly concave component has the same quantity at any two maxima of a concave sum. -/
theorem strict_component_equal_at_maxima (U : SeparableMarginals k) (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices k} {y : ℝ≥0} {x z : NonnegativeOrthant k}
    (hx : x ∈ MarshallianDemand (fun w => U.total w.val) p y)
    (hz : z ∈ MarshallianDemand (fun w => U.total w.val) p y) : x.val j = z.val j := by
  by_contra hne
  let w := Mix (convex_Ici (0 : Fin k → ℝ)) x z (1 / 2) (by norm_num)
  have hw : w ∈ BudgetSet p y := budgetSet_convex p y x hx.1 z hz.1 (1 / 2) (by norm_num)
  have hstrict : (1 / 2) * U.total x.val + (1 / 2) * U.total z.val < U.total w.val := by
    change (1 / 2) * (∑ i, U.utility i (x.val i)) +
      (1 / 2) * (∑ i, U.utility i (z.val i)) <
      ∑ i, U.utility i ((1 / 2) * x.val i + (1 - 1 / 2) * z.val i)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro i _
      convert (U.concave i).2 (x.property i) (z.property i)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
        (by ring : (1 / 2 : ℝ) + (1 - 1 / 2) = 1) using 1
      norm_num
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      convert hs.2 (x.property j) (z.property j) hne
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 - 1 / 2)
        (by ring : (1 / 2 : ℝ) + (1 - 1 / 2) = 1) using 1
      norm_num
  have hbound := hx.2 w hw
  have hreverse := hz.2 x hx.1
  change U.total w.val ≤ U.total x.val at hbound
  change U.total x.val ≤ U.total z.val at hreverse
  linarith

/-- Expenditure separates into nonmoney expenditure and the final commodity's cost. -/
theorem expenditure_nonmoney_split (p : PositivePrices (k + 1))
    (x : NonnegativeOrthant (k + 1)) :
    Expenditure p x = Expenditure (NonmoneyPrices p) (NonmoneyBundle x) +
      p.val (Fin.last k) * x.val (Fin.last k) := by
  simp [Expenditure, NonmoneyPrices, NonmoneyBundle, Fin.sum_univ_castSucc]

/-- The quasi-linear consumer has at most one optimum, despite the linear numeraire. -/
theorem quasiLinear_demand_subsingleton (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (y : ℝ≥0) :
    (MarshallianDemand (fun z => U.withNumeraire.total z.val) p y).Subsingleton := by
  intro x hx z hz
  by_cases hy : y = 0
  · subst y
    rw [marshallianDemand_zero] at hx hz
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hz).symm
  have hyn : 0 < (y : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hy)
  have hnon (j : Fin k) : x.val j.castSucc = z.val j.castSucc :=
    strict_component_equal_at_maxima U.withNumeraire j.castSucc
      (by simpa [SeparableMarginals.withNumeraire] using hs j) hx hz
  obtain ⟨l, hl⟩ := (problem_3_9 U p y hyn x).mp hx
  obtain ⟨m, hm⟩ := (problem_3_9 U p y hyn z).mp hz
  have he : Expenditure (NonmoneyPrices p) (NonmoneyBundle x) =
      Expenditure (NonmoneyPrices p) (NonmoneyBundle z) := by
    unfold Expenditure
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun q => p.val j.castSucc * q) (hnon j))
  have hbudget : Expenditure p x = Expenditure p z := hl.1.trans hm.1.symm
  rw [expenditure_nonmoney_split, expenditure_nonmoney_split, he] at hbudget
  have hlast : x.val (Fin.last k) = z.val (Fin.last k) :=
    (mul_left_cancel₀ (p.property (Fin.last k)).ne' (add_left_cancel hbudget))
  apply Subtype.ext
  funext j
  exact Fin.lastCases hlast hnon j

/-- Existence and uniqueness in Problem 3.9 follow from its primitive hypotheses at every income. -/
theorem quasiLinear_unique_demand (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (y : ℝ≥0) :
    ∃! x, x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y := by
  obtain ⟨x, hx⟩ := proposition_3_1b U.withNumeraire.continuous_total p y
  exact ⟨x, hx, fun z hz => quasiLinear_demand_subsingleton U hs p y hz hx⟩

end Kreps.ConsumerDemand
