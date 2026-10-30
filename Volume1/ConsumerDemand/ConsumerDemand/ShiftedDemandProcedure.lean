/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.WaterfillingMultiplier

/-!
# The shifted-product demand procedure

Kreps I, Problem 3.5, p. 64. Solve the expenditure equation for a positive
multiplier, then truncate each prescribed quantity at zero. The resulting
bundle is the unique optimum for positive exponents and nonnegative shifts,
including zero shifts and corner solutions. Existence of the multiplier is
proved in `WaterfillingMultiplier`; zero income is treated separately.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The quantity formula from the shifted-product multiplier procedure. -/
noncomputable def WaterfillBundle {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : NonnegativeOrthant k :=
  ⟨fun j => max (a j / (l * p.val j) - γ j) 0, fun _ => le_max_right _ _⟩

/-- Commodity expenditure is the positive part of its untruncated expenditure. -/
theorem waterfillBundle_commodity_cost {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) (j : Fin k) :
    p.val j * (WaterfillBundle a γ p l).val j = max (a j / l - p.val j * γ j) 0 := by
  dsimp only [WaterfillBundle]
  rw [mul_max_of_nonneg _ _ (p.property j).le, mul_zero]
  congr 1
  field_simp [ne_of_gt (p.property j)]

/-- Total expenditure of the proposed bundle is the multiplier's expenditure curve. -/
theorem expenditure_waterfillBundle {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) :
    Expenditure p (WaterfillBundle a γ p l) = WaterfillCost a γ p l := by
  exact Finset.sum_congr rfl (fun j _ => waterfillBundle_commodity_cost a γ p l j)

/-- Every shifted quantity of the candidate is positive, even when some shifts are zero. -/
theorem waterfillBundle_shifted_pos {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k) :
    0 < (WaterfillBundle a γ p l).val j + γ j := by
  have hdiv := div_pos (ha j) (mul_pos hl (p.property j))
  have hmax := le_max_left (a j / (l * p.val j) - γ j) 0
  change 0 < max (a j / (l * p.val j) - γ j) 0 + γ j
  linarith

/-- Prescribed marginal utility per dollar never exceeds the multiplier. -/
theorem waterfillBundle_marginal_le {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k) :
    LogMarginals a γ (WaterfillBundle a γ p l) j ≤ l * p.val j := by
  apply (div_le_iff₀ (waterfillBundle_shifted_pos a γ ha p hl j)).mpr
  have hmax := le_max_left (a j / (l * p.val j) - γ j) 0
  have hbound : a j / (l * p.val j) ≤ (WaterfillBundle a γ p l).val j + γ j := by
    change a j / (l * p.val j) ≤ max (a j / (l * p.val j) - γ j) 0 + γ j
    linarith
  have h := (div_le_iff₀ (mul_pos hl (p.property j))).mp hbound
  simpa only [mul_comm] using h

/-- A consumed good has marginal utility per dollar exactly equal to the multiplier. -/
theorem waterfillBundle_marginal_eq {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k)
    (hj : 0 < (WaterfillBundle a γ p l).val j) :
    LogMarginals a γ (WaterfillBundle a γ p l) j = l * p.val j := by
  have hinside : 0 < a j / (l * p.val j) - γ j :=
    (lt_max_iff.mp hj).resolve_right (lt_irrefl 0)
  have hx : (WaterfillBundle a γ p l).val j = a j / (l * p.val j) - γ j :=
    max_eq_left hinside.le
  dsimp only [LogMarginals]
  rw [hx, sub_add_cancel]
  field_simp [ne_of_gt (ha j)]

/-- Solving the expenditure equation verifies all logarithmic optimality conditions. -/
theorem waterfillBundle_optimality {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) {l : ℝ} (hl : 0 < l)
    (he : WaterfillCost a γ p l = (y : ℝ)) :
    CombinedOptimality p y (WaterfillBundle a γ p l)
      (LogMarginals a γ (WaterfillBundle a γ p l)) := by
  have hcost : Expenditure p (WaterfillBundle a γ p l) = (y : ℝ) :=
    (expenditure_waterfillBundle a γ p l).trans he
  refine ⟨hcost.le, l, hl.le, waterfillBundle_marginal_le a γ ha p hl,
    waterfillBundle_marginal_eq a γ ha p hl, ?_⟩
  rw [hcost]
  exact fun h => False.elim (lt_irrefl _ h)

/-- Any positive root of the expenditure equation gives the entire demand singleton. -/
theorem shiftedProduct_demand_of_waterfill {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0)
    {l : ℝ} (hl : 0 < l) (he : WaterfillCost a γ p l = (y : ℝ)) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y = {WaterfillBundle a γ p l} :=
  shiftedCobbDouglas_demand_of_optimality a γ ha hγ
    (waterfillBundle_shifted_pos a γ ha p hl)
    (waterfillBundle_optimality a γ ha p y hl he)

/-- **Problem 3.5:** the multiplier procedure exists and yields the unique demand. -/
theorem problem_3_5 {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) : ∃ l : ℝ, 0 < l ∧ WaterfillCost a γ p l = (y : ℝ) ∧
      MarshallianDemand (ShiftedCobbDouglas a γ) p y = {WaterfillBundle a γ p l} := by
  obtain ⟨l, hl, he⟩ := exists_waterfill_multiplier a γ ha hγ p y hy
  exact ⟨l, hl, he, shiftedProduct_demand_of_waterfill a γ ha hγ p y hl he⟩

/-- At zero income the shifted-product problem retains the unique feasible origin. -/
theorem problem_3_5_zero {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p 0 = {ZeroBundle k} :=
  marshallianDemand_zero _ p

end Kreps.ConsumerDemand
