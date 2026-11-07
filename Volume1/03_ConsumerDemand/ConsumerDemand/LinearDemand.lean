/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem
import ConsumerDemand.BudgetGeometry
import Mathlib.Data.Fintype.Lattice

/-!
# Linear utility and its complete demand correspondence

Kreps I, Problem 3.6(a), p. 64. Every optimal bundle spends the entire income
on goods with maximal utility per unit of expenditure. The characterization
retains the whole face of solutions when several goods tie, and includes zero
income. No differentiability or previously assumed maximizer is needed.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Linear utility with a separate coefficient for each commodity. -/
def LinearUtility {k : ℕ} (a : Fin k → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  ∑ j, a j * x.val j

/-- Linear utility is continuous, including on the boundary of the orthant. -/
theorem linearUtility_continuous {k : ℕ} (a : Fin k → ℝ) :
    Continuous (LinearUtility a) := by
  unfold LinearUtility
  exact continuous_finsetSum _ (fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_subtype_val))

/-- A single-good vertex has the corresponding utility per dollar times income. -/
theorem linearUtility_singleGoodBundle {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    LinearUtility a (SingleGoodBundle p y j) = (a j / p.val j) * (y : ℝ) := by
  simp only [LinearUtility, SingleGoodBundle, Pi.single_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- An upper bound on all utility-price ratios bounds every bundle's utility by its cost. -/
theorem linearUtility_le_ratio_expenditure {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (M : ℝ) (hM : ∀ j, a j / p.val j ≤ M)
    (x : NonnegativeOrthant k) : LinearUtility a x ≤ M * Expenditure p x := by
  calc
    LinearUtility a x ≤ ∑ j, (M * p.val j) * x.val j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (p.property j)).mp (hM j))
        (x.property j)
    _ = M * Expenditure p x := by simp [Expenditure, Finset.mul_sum, mul_assoc]

/-- A maximizing utility-price ratio exists because there are finitely many goods. -/
theorem exists_maximal_utility_price_ratio {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (p : PositivePrices k) : ∃ j, ∀ i, a i / p.val i ≤ a j / p.val j :=
  Finite.exists_max (fun j => a j / p.val j)

/-- Spending on a maximal-ratio good is optimal. -/
theorem singleGoodBundle_mem_linearDemand {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : ∀ i, a i / p.val i ≤ a j / p.val j) :
    SingleGoodBundle p y j ∈ MarshallianDemand (LinearUtility a) p y := by
  refine ⟨singleGoodBundle_mem_budgetSet p y j, fun x hx => ?_⟩
  change LinearUtility a x ≤ LinearUtility a (SingleGoodBundle p y j)
  rw [linearUtility_singleGoodBundle]
  exact (linearUtility_le_ratio_expenditure a p _ hj x).trans
    (mul_le_mul_of_nonneg_left hx (div_pos (ha j) (p.property j)).le)

/-- **Problem 3.6(a):** the full demand face, including ties and zero income. -/
theorem problem_3_6a {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand (LinearUtility a) p y ↔
      Expenditure p x = (y : ℝ) ∧
        ∀ i, 0 < x.val i → ∀ j, a j / p.val j ≤ a i / p.val i := by
  obtain ⟨b, hb⟩ := exists_maximal_utility_price_ratio a p
  let M := a b / p.val b
  have hM : 0 < M := div_pos (ha b) (p.property b)
  have hcoeff (j : Fin k) : a j ≤ M * p.val j :=
    (div_le_iff₀ (p.property j)).mp (hb j)
  constructor
  · intro hx
    have hlow : M * (y : ℝ) ≤ LinearUtility a x := by
      simpa only [UtilityPref, linearUtility_singleGoodBundle] using
        hx.2 _ (singleGoodBundle_mem_budgetSet p y b)
    have hupp := linearUtility_le_ratio_expenditure a p M hb x
    have hcost : Expenditure p x = (y : ℝ) := by
      apply le_antisymm hx.1
      exact (mul_le_mul_iff_right₀ hM).mp (hlow.trans hupp)
    have hvalue : LinearUtility a x = M * (y : ℝ) :=
      le_antisymm (by rwa [hcost] at hupp) hlow
    have hgap : ∑ j, (M * p.val j - a j) * x.val j = 0 := by
      calc
        _ = M * Expenditure p x - LinearUtility a x := by
          simp [Expenditure, LinearUtility, sub_mul, Finset.sum_sub_distrib,
            Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [hcost, hvalue]; ring
    refine ⟨hcost, fun i hi j => ?_⟩
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => mul_nonneg (sub_nonneg.mpr (hcoeff l)) (x.property l))).mp
        hgap i (Finset.mem_univ i)
    have heq : a i / p.val i = M := by
      apply (div_eq_iff (ne_of_gt (p.property i))).mpr
      have := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hi)
      linarith
    rw [heq]
    exact hb j
  · rintro ⟨hcost, hsupp⟩
    have hvalue : LinearUtility a x = M * Expenditure p x := by
      rw [LinearUtility, Expenditure, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 < x.val i
      · have heq : a i / p.val i = M := le_antisymm (hb i) (hsupp i hi b)
        have hcoeffeq := (div_eq_iff (ne_of_gt (p.property i))).mp heq
        rw [hcoeffeq]
        ring
      · have hzero : x.val i = 0 := le_antisymm (le_of_not_gt hi) (x.property i)
        simp only [hzero, mul_zero]
    refine ⟨hcost.le, fun z hz => ?_⟩
    change LinearUtility a z ≤ LinearUtility a x
    rw [hvalue, hcost]
    exact (linearUtility_le_ratio_expenditure a p M hb z).trans
      (mul_le_mul_of_nonneg_left hz hM.le)

end Kreps.ConsumerDemand
