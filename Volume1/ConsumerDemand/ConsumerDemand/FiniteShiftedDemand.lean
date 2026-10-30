/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ShiftedDemandProcedure

/-!
# A finite algebraic procedure for shifted-product demand

Kreps I, Problem 3.5, p. 64. For each nonempty subset of goods, compute the
ratio of its total exponents to income plus its shifted expenditure. Keep the
candidate exactly when its strict positive-demand set is that subset. At least
one of these finitely many candidates passes, and every passing candidate gives
the unique demand. Equality at a threshold correctly leaves a good unconsumed.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The goods with strictly positive prescribed consumption. -/
noncomputable def WaterfillActiveSet {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun j => p.val j * γ j < a j / l)

/-- The algebraic candidate multiplier for a proposed active set. -/
noncomputable def ActiveSetMultiplier {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (A : Finset (Fin k)) : ℝ :=
  (∑ j ∈ A, a j) / ((y : ℝ) + ∑ j ∈ A, p.val j * γ j)

/-- The expenditure curve is the sum of untruncated expenditures over its active set. -/
theorem waterfillCost_eq_active_sum {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) :
    WaterfillCost a γ p l =
      (∑ j ∈ WaterfillActiveSet a γ p l, a j) / l -
        ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold WaterfillActiveSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p.val j * γ j < a j / l
  · simp only [hj, ite_true, max_eq_left (sub_pos.mpr hj).le]
  · simp only [hj, ite_false, max_eq_right (sub_nonpos.mpr (le_of_not_gt hj))]

/-- A positive-income solution has at least one strictly consumed good. -/
theorem waterfillActiveSet_nonempty {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) {l : ℝ}
    (he : WaterfillCost a γ p l = (y : ℝ)) : (WaterfillActiveSet a γ p l).Nonempty := by
  by_contra h
  have hempty := Finset.not_nonempty_iff_eq_empty.mp h
  have hcost := waterfillCost_eq_active_sum a γ p l
  rw [hempty] at hcost
  simp only [Finset.sum_empty, zero_div, sub_zero] at hcost
  linarith

/-- Every positive root is exactly the algebraic candidate of its active set. -/
theorem waterfill_multiplier_eq_active_candidate {k : ℕ} (a γ : Fin k → ℝ)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {l : ℝ} (hl : 0 < l) (he : WaterfillCost a γ p l = (y : ℝ)) :
    l = ActiveSetMultiplier a γ p y (WaterfillActiveSet a γ p l) := by
  have hC : 0 ≤ ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j))
  have hden : 0 < (y : ℝ) + ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j :=
    add_pos_of_pos_of_nonneg hy hC
  have hc := waterfillCost_eq_active_sum a γ p l
  rw [he] at hc
  have hsum : (∑ j ∈ WaterfillActiveSet a γ p l, a j) / l =
      (y : ℝ) + ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j := by linarith
  have heq := (div_eq_iff (ne_of_gt hl)).mp hsum
  apply Eq.symm
  apply (div_eq_iff (ne_of_gt hden)).mpr
  nlinarith

/-- A nonempty proposed active set yields a positive candidate multiplier. -/
theorem activeSetMultiplier_pos {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (A : Finset (Fin k)) (hA : A.Nonempty) : 0 < ActiveSetMultiplier a γ p y A := by
  apply div_pos (Finset.sum_pos (fun j _ => ha j) hA)
  exact add_pos_of_pos_of_nonneg hy
    (Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j)))

/-- A candidate passing the active-set test solves the expenditure equation. -/
theorem active_candidate_solves_expenditure {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k)
    (y : ℝ≥0) (A : Finset (Fin k)) (hA : A.Nonempty)
    (htest : WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A) :
    WaterfillCost a γ p (ActiveSetMultiplier a γ p y A) = (y : ℝ) := by
  rw [waterfillCost_eq_active_sum, htest]
  have hsum : 0 < ∑ j ∈ A, a j := Finset.sum_pos (fun j _ => ha j) hA
  unfold ActiveSetMultiplier
  field_simp
  ring

/-- **Problem 3.5, finite procedure:** a nonempty subset always passes the algebraic test. -/
theorem problem_3_5_finite_candidates {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ A : Finset (Fin k), A.Nonempty ∧
      WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A ∧
      MarshallianDemand (ShiftedCobbDouglas a γ) p y =
        {WaterfillBundle a γ p (ActiveSetMultiplier a γ p y A)} := by
  obtain ⟨l, hl, he⟩ := exists_waterfill_multiplier a γ ha hγ p y hy
  have heq := waterfill_multiplier_eq_active_candidate a γ hγ p y hy hl he
  refine ⟨WaterfillActiveSet a γ p l, waterfillActiveSet_nonempty a γ p y hy he, ?_, ?_⟩
  · rw [← heq]
  · rw [← heq]
    exact shiftedProduct_demand_of_waterfill a γ ha hγ p y hl he

/-- Every nonempty subset that passes the finite test returns the unique correct demand. -/
theorem problem_3_5_finite_candidate_sound {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (A : Finset (Fin k)) (hA : A.Nonempty)
    (htest : WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y =
      {WaterfillBundle a γ p (ActiveSetMultiplier a γ p y A)} :=
  shiftedProduct_demand_of_waterfill a γ ha hγ p y
    (activeSetMultiplier_pos a γ ha hγ p y hy A hA)
    (active_candidate_solves_expenditure a γ ha p y A hA htest)

end Kreps.ConsumerDemand
