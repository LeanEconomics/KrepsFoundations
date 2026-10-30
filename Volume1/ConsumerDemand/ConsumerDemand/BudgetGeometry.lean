/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BudgetSets

/-!
# Budget vertices and positive bundles

Kreps I, Section 3.1 and Figure 3.1, pp. 50-51. The single-good vertices spend
the entire budget on one commodity. Positive income also makes a strictly
positive bundle affordable, which is useful when boundary utility is zero.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Spending the entire income on commodity `j`, including the zero-income case. -/
noncomputable def SingleGoodBundle {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    NonnegativeOrthant k :=
  ⟨Pi.single j ((y : ℝ) / p.val j), fun i => by
    by_cases h : i = j
    · subst i
      simpa using div_nonneg y.property (p.property j).le
    · simp [h]⟩

/-- A single-good vertex exhausts the budget. -/
theorem expenditure_singleGoodBundle {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (j : Fin k) : Expenditure p (SingleGoodBundle p y j) = (y : ℝ) := by
  simp [Expenditure, SingleGoodBundle, Pi.single_apply,
    mul_div_cancel₀ _ (ne_of_gt (p.property j))]

/-- All single-good vertices are feasible. -/
theorem singleGoodBundle_mem_budgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (j : Fin k) : SingleGoodBundle p y j ∈ BudgetSet p y :=
  (expenditure_singleGoodBundle p y j).le

/-- Dividing positive income equally across expenditures gives a positive feasible bundle. -/
theorem budgetSet_exists_positive {k : ℕ} [NeZero k] (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ x ∈ BudgetSet p y, ∀ j, 0 < x.val j := by
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  let x : NonnegativeOrthant k :=
    ⟨fun j => (y : ℝ) / ((k : ℝ) * p.val j), fun j => by
      exact (div_pos hy (mul_pos hk (p.property j))).le⟩
  refine ⟨x, ?_, fun j => div_pos hy (mul_pos hk (p.property j))⟩
  change (∑ j, p.val j * ((y : ℝ) / ((k : ℝ) * p.val j))) ≤ (y : ℝ)
  have hterm (j : Fin k) :
      p.val j * ((y : ℝ) / ((k : ℝ) * p.val j)) = (y : ℝ) / k := by
    field_simp [ne_of_gt (p.property j)]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (mul_div_cancel₀ _ (ne_of_gt hk)).le

end Kreps.ConsumerDemand
