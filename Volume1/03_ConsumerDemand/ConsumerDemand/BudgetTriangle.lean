/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import ConsumerDemand.BudgetGeometry
import Mathlib.Analysis.Convex.Combination

/-!
# The two-good budget triangle

Kreps I, Figure 3.1, p. 51. The nonnegative two-good budget region is exactly
the convex hull of the origin and the two single-good intercepts. The statement
includes the degenerate zero-income triangle.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The three vertices of the two-good budget triangle. -/
noncomputable def BudgetTriangleVertices (p : PositivePrices 2) (y : ℝ≥0) :
    Set (Fin 2 → ℝ) :=
  {0, (SingleGoodBundle p y 0).val, (SingleGoodBundle p y 1).val}

/-- Every vertex belongs to the corresponding budget. -/
theorem budgetTriangleVertices_subset (p : PositivePrices 2) (y : ℝ≥0) :
    BudgetTriangleVertices p y ⊆ BudgetVectors p y := by
  intro x hx
  rcases hx with rfl | rfl | h
  · exact ⟨le_rfl, by simp⟩
  · exact ⟨(SingleGoodBundle p y 0).property, (expenditure_singleGoodBundle p y 0).le⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨(SingleGoodBundle p y 1).property, (expenditure_singleGoodBundle p y 1).le⟩

/-- **Figure 3.1:** the full budget region is precisely the triangle with the printed intercepts. -/
theorem budgetVectors_eq_triangle (p : PositivePrices 2) (y : ℝ≥0) :
    BudgetVectors p y = convexHull ℝ (BudgetTriangleVertices p y) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hy : 0 < (y : ℝ)
    · let w : Fin 3 → ℝ :=
        ![1 - (p.val 0 * x 0 + p.val 1 * x 1) / y,
          p.val 0 * x 0 / y, p.val 1 * x 1 / y]
      let z : Fin 3 → Fin 2 → ℝ :=
        ![0, (SingleGoodBundle p y 0).val, (SingleGoodBundle p y 1).val]
      have hbudget : p.val 0 * x 0 + p.val 1 * x 1 ≤ (y : ℝ) := by
        simpa [Fin.sum_univ_succ] using hx.2
      apply mem_convexHull_of_exists_fintype w z
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr ((div_le_one hy).mpr hbudget)
        · exact div_nonneg (mul_nonneg (p.property 0).le (hx.1 0)) hy.le
        · exact div_nonneg (mul_nonneg (p.property 1).le (hx.1 1)) hy.le
      · simp only [w, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one]
        ring
      · intro i
        fin_cases i <;> simp [z, BudgetTriangleVertices]
      · funext i
        fin_cases i <;>
          norm_num [w, z, SingleGoodBundle, Fin.sum_univ_succ] <;>
          field_simp [ne_of_gt (p.property 0), ne_of_gt (p.property 1), ne_of_gt hy]
    · have hy0 : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
      subst y
      have hzero : x = 0 := by
        have hmem : (⟨x, hx.1⟩ : NonnegativeOrthant 2) ∈ BudgetSet p 0 := hx.2
        rw [budgetSet_zero, Set.mem_singleton_iff] at hmem
        exact congrArg Subtype.val hmem
      rw [hzero]
      exact subset_convexHull ℝ _ (by simp [BudgetTriangleVertices])
  · exact convexHull_min (budgetTriangleVertices_subset p y) (budgetVectors_convex p y)

end Kreps.ConsumerDemand
