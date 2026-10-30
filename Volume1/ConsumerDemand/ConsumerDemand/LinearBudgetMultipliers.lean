/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Multipliers for a linear budget

Kreps I, Proposition 3.5a, pp. 57-58. The first-order directional condition reduces
necessity to this finite-dimensional linear problem. Positive income is essential
to the explicit multiplier construction; zero income is handled separately by the
singleton budget result.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators

/-- A maximizer of a linear functional on a positive-price budget has nonnegative
budget and commodity multipliers, including complementary slackness. -/
theorem linear_budget_multipliers {k : ℕ} (p m x : Fin k → ℝ) (y : ℝ)
    (hp : ∀ i, 0 < p i) (hy : 0 < y) (hx : ∀ i, 0 ≤ x i)
    (hbudget : ∑ i, p i * x i ≤ y)
    (hmax : ∀ z : Fin k → ℝ, (∀ i, 0 ≤ z i) → (∑ i, p i * z i ≤ y) →
      ∑ i, m i * z i ≤ ∑ i, m i * x i) :
    ∃ l : ℝ, 0 ≤ l ∧ (∀ i, m i ≤ l * p i) ∧
      (∀ i, (l * p i - m i) * x i = 0) ∧ l * (y - ∑ i, p i * x i) = 0 := by
  classical
  let v := ∑ i, m i * x i
  have hv : 0 ≤ v := by
    simpa [v] using hmax (fun _ => 0) (fun _ => le_rfl) (by simpa using hy.le)
  let l := v / y
  have hl : 0 ≤ l := div_nonneg hv hy.le
  have hly : l * y = v := div_mul_cancel₀ v (ne_of_gt hy)
  have hcoeff (i : Fin k) : m i ≤ l * p i := by
    have hvertex := hmax (Pi.single i (y / p i))
      (fun j => by by_cases h : j = i <;> simp [h, div_nonneg hy.le (hp i).le])
      (by simp [Pi.single_apply, mul_div_cancel₀ _ (ne_of_gt (hp i))])
    have hratio : m i * (y / p i) ≤ v := by
      simpa [Pi.single_apply, v] using hvertex
    have h := (div_le_iff₀ (hp i)).mp (show m i * y / p i ≤ v by
      simpa [mul_div_assoc] using hratio)
    nlinarith [hp i]
  have hsum : v ≤ l * ∑ i, p i * x i := by
    calc
      v ≤ ∑ i, (l * p i) * x i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcoeff i) (hx i))
      _ = l * ∑ i, p i * x i := by simp [Finset.mul_sum, mul_assoc]
  have hslack : l * (y - ∑ i, p i * x i) = 0 := by nlinarith
  have hgap : ∑ i, (l * p i - m i) * x i = 0 := by
    rw [show (∑ i, (l * p i - m i) * x i) =
        l * (∑ i, p i * x i) - v by
      simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, v]]
    nlinarith
  refine ⟨l, hl, hcoeff, ?_, hslack⟩
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (sub_nonneg.mpr (hcoeff i)) (hx i))).mp hgap i (Finset.mem_univ i)

end Kreps.ConsumerDemand
