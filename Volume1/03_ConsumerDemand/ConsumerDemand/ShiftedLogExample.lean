/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.LogarithmicSupport

/-!
# The three numerical demands in Problem 3.4

Kreps I, Problem 3.4, p. 64. The utility and prices below are exactly the
printed example. Income 16.4 is the exact rational number 82/5. Each answer is
proved to be the entire singleton demand set, including comparison with all
boundary bundles, rather than merely a solution of first-order equations.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- The exact logarithmic utility in Problem 3.4. -/
noncomputable def Problem34Utility (x : NonnegativeOrthant 3) : ℝ :=
  Real.log (x.val 0 + 2) + 2 * Real.log (x.val 1 + 3) + 4 * Real.log (x.val 2 + 2)

/-- The exact prices in Problem 3.4, in the same commodity order. -/
def Problem34Prices : PositivePrices 3 :=
  ⟨![2, 3, 1], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at income 5. -/
def Problem34BundleFive : NonnegativeOrthant 3 :=
  ⟨![0, 0, 5], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at the exact decimal income 16.4. -/
noncomputable def Problem34BundleSixteenPointFour : NonnegativeOrthant 3 :=
  ⟨![6 / 25, 0, 398 / 25], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at income 100. -/
noncomputable def Problem34BundleHundred : NonnegativeOrthant 3 :=
  ⟨![87 / 14, 167 / 21, 446 / 7], fun j => by fin_cases j <;> norm_num⟩

/-- The printed expression is a specialization of weighted shifted logarithms. -/
theorem problem34Utility_eq : Problem34Utility = ShiftedLogUtility ![1, 2, 4] ![2, 3, 2] := by
  funext x
  simp [Problem34Utility, ShiftedLogUtility, Fin.sum_univ_succ, add_assoc]

/-- **Problem 3.4, income 5:** only the third good is consumed. -/
theorem problem_3_4_five :
    MarshallianDemand Problem34Utility Problem34Prices 5 = {Problem34BundleFive} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 4 / 7, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleFive, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleFive]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleFive]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleFive, Fin.sum_univ_succ]

/-- **Problem 3.4, income 16.4:** the first and third goods are consumed. -/
theorem problem_3_4_sixteenPointFour :
    MarshallianDemand Problem34Utility Problem34Prices (82 / 5) =
      {Problem34BundleSixteenPointFour} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 25 / 112, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleSixteenPointFour,
      Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleSixteenPointFour]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleSixteenPointFour]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleSixteenPointFour, Fin.sum_univ_succ]

/-- **Problem 3.4, income 100:** all three goods are consumed. -/
theorem problem_3_4_hundred :
    MarshallianDemand Problem34Utility Problem34Prices 100 = {Problem34BundleHundred} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 7 / 115, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleHundred, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleHundred]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleHundred]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleHundred, Fin.sum_univ_succ]

end Kreps.ConsumerDemand
