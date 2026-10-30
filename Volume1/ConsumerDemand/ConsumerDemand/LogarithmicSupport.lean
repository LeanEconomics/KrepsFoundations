/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Strict logarithmic supporting inequalities

Kreps I, Problems 3.3-3.5, p. 64. Logarithmic utility is compared only where
every logarithm has a strictly positive argument. This avoids treating Lean's
total-function value `Real.log 0` as an economic utility at zero consumption.
Positive shifts make the results applicable to the full nonnegative orthant.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Weighted logarithmic utility, interpreted economically only at positive arguments. -/
noncomputable def ShiftedLogUtility {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∑ j, a j * Real.log (x.val j + γ j)

/-- The marginal coefficients at a bundle where all logarithm arguments are positive. -/
noncomputable def LogMarginals {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) : ℝ := a j / (x.val j + γ j)

/-- The scalar logarithm lies below its tangent on the positive half-line. -/
theorem log_sub_log_le_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log z - Real.log x ≤ (z - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz hx)
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

/-- At different positive points, the logarithmic supporting inequality is strict. -/
theorem log_sub_log_lt_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (hne : z ≠ x) :
    Real.log z - Real.log x < (z - x) / x := by
  have hne' : z / x ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq (ne_of_gt hx)).mp h)
  have h := Real.log_lt_sub_one_of_pos (div_pos hz hx) hne'
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

/-- Positive weights give a strict supporting inequality whenever the bundles differ. -/
theorem shiftedLog_strict_support {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (x z : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j)
    (hz : ∀ j, 0 < z.val j + γ j) (hne : z ≠ x) :
    ShiftedLogUtility a γ z - ShiftedLogUtility a γ x <
      ∑ j, LogMarginals a γ x j * (z.val j - x.val j) := by
  have hex : ∃ j, z.val j ≠ x.val j := by
    by_contra! h
    exact hne (Subtype.ext (funext h))
  obtain ⟨j, hj⟩ := hex
  rw [ShiftedLogUtility, ShiftedLogUtility, ← Finset.sum_sub_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    have h := mul_le_mul_of_nonneg_left (log_sub_log_le_tangent (hx i) (hz i)) (ha i).le
    dsimp only [LogMarginals]
    convert h using 1 <;> ring
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    have hneq : z.val j + γ j ≠ x.val j + γ j := fun h => hj (add_right_cancel h)
    have h := mul_lt_mul_of_pos_left (log_sub_log_lt_tangent (hx j) (hz j) hneq) (ha j)
    dsimp only [LogMarginals]
    convert h using 1 <;> ring

/-- Combined optimality bounds the corresponding linear marginal objective over the budget. -/
theorem combinedOptimality_linear_bound {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y) :
    (∑ j, m j * (z.val j - x.val j)) ≤ 0 := by
  obtain ⟨_, l, hl, hm, hg, hs⟩ :=
    (combinedOptimality_iff_complementarity p y x m).mp ho
  have hprod (j) : m j * x.val j = (l * p.val j) * x.val j := by
    have h := hg j
    nlinarith
  have hsum : (∑ j, m j * x.val j) = l * Expenditure p x := by
    simp_rw [hprod]
    simp [Expenditure, Finset.mul_sum, mul_assoc]
  have hzsum : (∑ j, m j * z.val j) ≤ l * Expenditure p z := by
    calc
      _ ≤ ∑ j, (l * p.val j) * z.val j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (z.property j))
      _ = _ := by simp [Expenditure, Finset.mul_sum, mul_assoc]
  have hbudget : l * Expenditure p z ≤ l * (y : ℝ) :=
    mul_le_mul_of_nonneg_left hz hl
  simp only [mul_sub, Finset.sum_sub_distrib, hsum]
  nlinarith

/-- The logarithmic conditions imply strict optimality among positive-argument feasible bundles. -/
theorem shiftedLog_strict_optimality {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hzpos : ∀ j, 0 < z.val j + γ j) (hne : z ≠ x) :
    ShiftedLogUtility a γ z < ShiftedLogUtility a γ x := by
  have hstrict := shiftedLog_strict_support a γ ha x z hx hzpos hne
  have hlinear := combinedOptimality_linear_bound ho hz
  linarith

/-- With strictly positive shifts, the logarithmic conditions give the full singleton demand. -/
theorem shiftedLog_demand_of_positive_shifts {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 < γ j) {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} (ho : CombinedOptimality p y x (LogMarginals a γ x)) :
    MarshallianDemand (ShiftedLogUtility a γ) p y = {x} := by
  have hpos (z : NonnegativeOrthant k) (j) : 0 < z.val j + γ j :=
    add_pos_of_nonneg_of_pos (z.property j) (hγ j)
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (not_lt_of_ge (hz.2 x ho.1))
      (shiftedLog_strict_optimality a γ ha (hpos x) ho hz.1 (hpos z) hne)
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨ho.1, fun w hw => ?_⟩
    change ShiftedLogUtility a γ w ≤ ShiftedLogUtility a γ x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedLog_strict_optimality a γ ha (hpos x) ho hw (hpos w) he).le

end Kreps.ConsumerDemand
