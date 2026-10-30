/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CobbDouglasDemand
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The positive-domain logarithmic problem

Kreps I, Problem 3.3(a-c), p. 64. Ordinary logarithms require strictly positive
consumption, so the logarithmic problem uses the positive part of the budget.
At positive income its unique solution agrees with full-domain Cobb-Douglas
demand. At zero income its menu is empty; the Cobb-Douglas problem still has
the unique feasible origin. Weighted-log concavity needs no normalization of
the positive weights.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The budget menu on which ordinary, unshifted logarithms are defined. -/
def PositiveBudgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    Set (NonnegativeOrthant k) := {x | x ∈ BudgetSet p y ∧ ∀ j, 0 < x.val j}

/-- Logarithmic demand uses only feasible bundles with positive consumption in every good. -/
noncomputable def LogarithmicDemand {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  PrefChoice (UtilityPref (ShiftedLogUtility a 0)) (PositiveBudgetSet p y)

/-- The logarithmic transform identity is asserted only at positive consumption. -/
theorem log_cobbDouglas {k : ℕ} (a : Fin k → ℝ) (x : NonnegativeOrthant k)
    (hx : ∀ j, 0 < x.val j) : Real.log (CobbDouglas a x) = ShiftedLogUtility a 0 x :=
  log_shiftedCobbDouglas a 0 x (fun j => by simpa using hx j)

/-- **Problem 3.3(a):** weighted logarithms have the expenditure-share demand at positive income. -/
theorem problem_3_3a {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    LogarithmicDemand a p y = {CobbDouglasBundle a ha p y} := by
  let x := CobbDouglasBundle a ha p y
  have ho := cobbDouglasBundle_optimality a ha p y hy
  have hxpos : ∀ j, 0 < x.val j + (0 : Fin k → ℝ) j :=
    fun j => by simpa [x] using cobbDouglasBundle_pos a ha p y hy j
  have hx : x ∈ PositiveBudgetSet p y :=
    ⟨ho.1, cobbDouglasBundle_pos a ha p y hy⟩
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hstrict := shiftedLog_strict_optimality a 0 ha hxpos ho hz.1.1
      (fun j => by simpa using hz.1.2 j) hne
    exact (not_lt_of_ge (hz.2 x hx)) hstrict
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨hx, fun w hw => ?_⟩
    change ShiftedLogUtility a 0 w ≤ ShiftedLogUtility a 0 x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedLog_strict_optimality a 0 ha hxpos ho hw.1
        (fun j => by simpa using hw.2 j) he).le

/-- **Problem 3.3(b):** log and Cobb-Douglas demand coincide at every positive income. -/
theorem problem_3_3b {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    LogarithmicDemand a p y = MarshallianDemand (CobbDouglas a) p y := by
  rw [problem_3_3a a ha p y hy, cobbDouglas_demand a ha p y]

/-- At zero income the ordinary logarithmic problem has no feasible positive bundle. -/
theorem logarithmicDemand_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (p : PositivePrices k) : LogarithmicDemand a p 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hzero : x = ZeroBundle k := by
    have hbudget := hx.1.1
    rwa [budgetSet_zero, Set.mem_singleton_iff] at hbudget
  obtain ⟨j⟩ := (inferInstance : Nonempty (Fin k))
  have hpos := hx.1.2 j
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **Problem 3.3(c):** arbitrary positive weighted logarithms are concave on their true domain. -/
theorem problem_3_3c {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    ConcaveOn ℝ {x : Fin k → ℝ | ∀ j, 0 < x j} (fun x => ∑ j, a j * Real.log (x j)) := by
  refine ⟨?_, ?_⟩
  · intro x hx z hz s t hs ht hst j
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hx j) (hz j) hs ht hst
  · intro x hx z hz s t hs ht hst
    change s * (∑ j, a j * Real.log (x j)) + t * (∑ j, a j * Real.log (z j)) ≤ _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left
      (strictConcaveOn_log_Ioi.concaveOn.2 (hx j) (hz j) hs ht hst) (ha j).le
    convert h using 1
    simp only [smul_eq_mul]
    ring

end Kreps.ConsumerDemand
