/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem
import Mathlib.Data.Fintype.Lattice

/-!
# Leontief demand without differentiability

Kreps I, Problem 3.6(b), p. 64. For positive coefficients, the utility minimum
has a unique optimal bundle: every effective quantity equals income divided by
the cost of one unit of utility. The proof compares costs directly and applies
at zero income as well as positive income.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The smallest effective quantity among the finitely many commodities. -/
noncomputable def LeontiefUtility {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => a j * x.val j)

/-- Leontief utility is no larger than any effective commodity quantity. -/
theorem leontiefUtility_le {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) : LeontiefUtility a x ≤ a j * x.val j :=
  Finset.inf'_le _ (Finset.mem_univ j)

/-- A common lower bound for the effective quantities is a lower bound for utility. -/
theorem le_leontiefUtility {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) (t : ℝ) (ht : ∀ j, t ≤ a j * x.val j) :
    t ≤ LeontiefUtility a x :=
  Finset.le_inf' _ _ (fun j _ => ht j)

/-- The expenditure needed for one unit of utility. -/
noncomputable def LeontiefUnitCost {k : ℕ} (a : Fin k → ℝ) (p : PositivePrices k) : ℝ :=
  ∑ j, p.val j / a j

/-- With at least one good and strictly positive coefficients, unit cost is positive. -/
theorem leontiefUnitCost_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) : 0 < LeontiefUnitCost a p := by
  exact Finset.sum_pos (fun j _ => div_pos (p.property j) (ha j)) Finset.univ_nonempty

/-- The proportional bundle prescribed by Problem 3.6(b). -/
noncomputable def LeontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) : NonnegativeOrthant k :=
  ⟨fun j => ((y : ℝ) / LeontiefUnitCost a p) / a j,
    fun j => div_nonneg (div_nonneg y.property (leontiefUnitCost_pos a ha p).le) (ha j).le⟩

/-- All effective quantities at the proposed demand equal its utility level. -/
theorem leontiefBundle_effective_quantity {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    a j * (LeontiefBundle a ha p y).val j = (y : ℝ) / LeontiefUnitCost a p := by
  exact mul_div_cancel₀ _ (ne_of_gt (ha j))

/-- The proposed Leontief bundle spends exactly the available income. -/
theorem expenditure_leontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (LeontiefBundle a ha p y) = (y : ℝ) := by
  calc
    _ = ((y : ℝ) / LeontiefUnitCost a p) * LeontiefUnitCost a p := by
      simp only [Expenditure, LeontiefBundle, LeontiefUnitCost, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (y : ℝ) := div_mul_cancel₀ _ (ne_of_gt (leontiefUnitCost_pos a ha p))

/-- The utility attained by the proportional bundle. -/
theorem leontiefUtility_leontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    LeontiefUtility a (LeontiefBundle a ha p y) = (y : ℝ) / LeontiefUnitCost a p := by
  apply le_antisymm
  · obtain ⟨j⟩ := (inferInstance : Nonempty (Fin k))
    exact (leontiefUtility_le a _ j).trans (leontiefBundle_effective_quantity a ha p y j).le
  · exact le_leontiefUtility a _ _ (fun j =>
      (leontiefBundle_effective_quantity a ha p y j).ge)

/-- Achieving utility `t` requires at least `t` times the unit cost. -/
theorem leontiefUtility_cost_bound {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (x : NonnegativeOrthant k) :
    LeontiefUtility a x * LeontiefUnitCost a p ≤ Expenditure p x := by
  rw [LeontiefUnitCost, Expenditure, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (leontiefUtility_le a x j)
    (div_pos (p.property j) (ha j)).le
  convert h using 1 <;> field_simp [ne_of_gt (ha j)]

/-- The proportional bundle is a global optimum on the full nonnegative budget. -/
theorem leontiefBundle_mem_demand {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    LeontiefBundle a ha p y ∈ MarshallianDemand (LeontiefUtility a) p y := by
  refine ⟨(expenditure_leontiefBundle a ha p y).le, fun x hx => ?_⟩
  change LeontiefUtility a x ≤ LeontiefUtility a (LeontiefBundle a ha p y)
  rw [leontiefUtility_leontiefBundle]
  exact (le_div_iff₀ (leontiefUnitCost_pos a ha p)).mpr
    ((leontiefUtility_cost_bound a ha p x).trans hx)

/-- **Problem 3.6(b):** the entire demand correspondence is the proposed singleton. -/
theorem problem_3_6b {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (LeontiefUtility a) p y = {LeontiefBundle a ha p y} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hlevel : (y : ℝ) / LeontiefUnitCost a p ≤ LeontiefUtility a x := by
      simpa only [UtilityPref, leontiefUtility_leontiefBundle] using
        hx.2 _ (leontiefBundle_mem_demand a ha p y).1
    have hcoord (j : Fin k) : (LeontiefBundle a ha p y).val j ≤ x.val j :=
      (div_le_iff₀ (ha j)).mpr (by
        simpa only [mul_comm] using hlevel.trans (leontiefUtility_le a x j))
    have hsum : ∑ j, p.val j * (x.val j - (LeontiefBundle a ha p y).val j) ≤ 0 := by
      calc
        _ = Expenditure p x - Expenditure p (LeontiefBundle a ha p y) := by
          simp [Expenditure, mul_sub, Finset.sum_sub_distrib]
        _ ≤ 0 := by rw [expenditure_leontiefBundle]; exact sub_nonpos.mpr hx.1
    have hzero : ∑ j, p.val j * (x.val j - (LeontiefBundle a ha p y).val j) = 0 :=
      le_antisymm hsum (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (p.property j).le (sub_nonneg.mpr (hcoord j))))
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (p.property j).le (sub_nonneg.mpr (hcoord j)))).mp hzero j
        (Finset.mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (ne_of_gt (p.property j)))
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact leontiefBundle_mem_demand a ha p y

end Kreps.ConsumerDemand
