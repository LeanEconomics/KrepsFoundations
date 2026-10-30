/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CobbDouglasDemand
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of the shifted-product expenditure multiplier

Kreps I, Problem 3.5, p. 64. For positive income, the continuous expenditure
curve obtained by truncating negative commodity expenditures crosses income
at a strictly positive multiplier. Explicit upper and lower brackets establish
existence without assuming the desired demand or multiplier in advance.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Total spending prescribed by the marginal multiplier, with negative demands truncated. -/
noncomputable def WaterfillCost {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : ℝ := ∑ j, max (a j / l - p.val j * γ j) 0

/-- The expenditure curve is continuous on every closed interval of positive multipliers. -/
theorem waterfillCost_continuousOn {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    {lo hi : ℝ} (hlo : 0 < lo) : ContinuousOn (WaterfillCost a γ p) (Set.Icc lo hi) := by
  apply continuousOn_finsetSum
  intro j _
  have hdiv : ContinuousOn (fun l : ℝ => a j / l) (Set.Icc lo hi) :=
    continuousOn_const.div continuousOn_id (fun _ hl => ne_of_gt (hlo.trans_le hl.1))
  exact (hdiv.sub continuousOn_const).sup continuousOn_const

/-- Dropping the truncation gives a useful lower bound on prescribed expenditure. -/
theorem waterfillCost_lower_bound {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : (∑ j, a j) / l - ∑ j, p.val j * γ j ≤ WaterfillCost a γ p l := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun j _ => le_max_left _ _)

/-- Nonnegative shifts make prescribed expenditure no greater than the unshifted total. -/
theorem waterfillCost_upper_bound {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) {l : ℝ} (hl : 0 < l) :
    WaterfillCost a γ p l ≤ (∑ j, a j) / l := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  exact max_le (sub_le_self _ (mul_nonneg (p.property j).le (hγ j))) (div_pos (ha j) hl).le

/-- The multiplier equation always has a positive solution at positive income. -/
theorem exists_waterfill_multiplier {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ l : ℝ, 0 < l ∧ WaterfillCost a γ p l = (y : ℝ) := by
  let A := ∑ j, a j
  let C := ∑ j, p.val j * γ j
  have hA : 0 < A := exponent_sum_pos a ha
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j))
  let lo := A / ((y : ℝ) + C + 1)
  let hi := A / (y : ℝ)
  have hden : 0 < (y : ℝ) + C + 1 := by positivity
  have hlo : 0 < lo := div_pos hA hden
  have hhi : 0 < hi := div_pos hA hy
  have horder : lo ≤ hi := div_le_div_of_nonneg_left hA.le hy (by linarith)
  have helo : A / lo = (y : ℝ) + C + 1 := by
    dsimp only [lo]
    field_simp
  have hehi : A / hi = (y : ℝ) := by
    dsimp only [hi]
    field_simp
  have hlow : (y : ℝ) ≤ WaterfillCost a γ p lo := by
    have h := waterfillCost_lower_bound a γ p lo
    change A / lo - C ≤ _ at h
    rw [helo] at h
    linarith
  have hhigh : WaterfillCost a γ p hi ≤ (y : ℝ) := by
    have h := waterfillCost_upper_bound a γ ha hγ p hhi
    change _ ≤ A / hi at h
    rwa [hehi] at h
  obtain ⟨l, hl, hvalue⟩ := intermediate_value_Icc' horder
    (waterfillCost_continuousOn a γ p hlo) ⟨hhigh, hlow⟩
  exact ⟨l, hlo.trans_le hl.1, hvalue⟩

end Kreps.ConsumerDemand
