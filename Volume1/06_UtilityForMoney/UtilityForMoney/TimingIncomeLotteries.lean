/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.TimingValueBounds
import UtilityForMoney.LotterySimpleLottery

/-!
# Why income lotteries fail the expected-utility test under precommitment

Kreps I, Problem 6.7, pp. 142–143. The three-state income lottery is a mixture of
the two-state lottery and the sure income. Their respective optimal commitments
differ. The mixed optimal value is strictly below both component optima, even
though every fixed commitment is evaluated by expected utility of final bundles.
-/

namespace Kreps.UtilityForMoney

/-- The printed binary lottery over incomes. -/
noncomputable def TimingIncomeTwo : SimpleLottery ℝ :=
  BinaryLottery 98 178 (1 / 2) (by norm_num)

/-- The printed certain income. -/
noncomputable def TimingIncomeSure : SimpleLottery ℝ := Convexity.StdSimplex.single 126.948391819

/-- The two-thirds/one-third mixture gives probability one third to each income. -/
noncomputable def TimingIncomeThree : SimpleLottery ℝ :=
  LotteryTheory.Mix ⟨2 / 3, by norm_num⟩ TimingIncomeTwo TimingIncomeSure

/-- Holding the first choice fixed gives the bundle utility in the realized income state. -/
noncomputable def TimingBundleIndex (w y : ℝ) : ℝ := Real.log w + Real.log (y + 2 - w)

/-- Any income index evaluates the ternary lottery as the specified mixture of components. -/
theorem timing_income_mixture_value (U : ℝ → ℝ) :
    ExpectedUtility U TimingIncomeThree =
      (2 * ExpectedUtility U TimingIncomeTwo + ExpectedUtility U TimingIncomeSure) / 3 := by
  have he := LotteryTheory.expectedUtility_affine U
    (⟨2 / 3, by norm_num⟩ : LotteryTheory.Weight) TimingIncomeTwo TimingIncomeSure
  change ExpectedUtility U TimingIncomeThree =
    2 / 3 * ExpectedUtility U TimingIncomeTwo +
      (1 - 2 / 3) * ExpectedUtility U TimingIncomeSure at he
  rw [he]
  ring

/-- Each committed-consumption objective is exactly expected utility over realized bundles. -/
theorem timing_values_as_expectations (w : ℝ) :
    ExpectedUtility (TimingBundleIndex w) TimingIncomeTwo = TimingValue TimingTwo w ∧
    ExpectedUtility (TimingBundleIndex w) TimingIncomeSure = TimingValue TimingSure w ∧
    ExpectedUtility (TimingBundleIndex w) TimingIncomeThree = TimingValue TimingThree w := by
  have h₂ : ExpectedUtility (TimingBundleIndex w) TimingIncomeTwo = TimingValue TimingTwo w := by
    rw [TimingIncomeTwo, expectedUtility_binary]
    norm_num [TimingBundleIndex, TimingValue, TimingTwo, Fin.sum_univ_two]
    ring
  have h₁ : ExpectedUtility (TimingBundleIndex w) TimingIncomeSure = TimingValue TimingSure w := by
    rw [TimingIncomeSure, expectedUtility_single]
    norm_num [TimingBundleIndex, TimingValue, TimingSure]
  refine ⟨h₂, h₁, ?_⟩
  rw [timing_income_mixture_value, h₂, h₁]
  norm_num [TimingValue, TimingThree, TimingTwo, TimingSure, Fin.sum_univ_succ]
  ring

/-- The ternary optimum is below both component optima when first consumption is committed. -/
theorem timing_optimized_mixture_worse :
    ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610, w ∈ TimingMenu TimingThree ∧
      (∀ z ∈ TimingMenu TimingThree, z ≠ w →
        TimingValue TimingThree z < TimingValue TimingThree w) ∧
      TimingValue TimingThree w < TimingValue TimingTwo 60 ∧
      TimingValue TimingThree w < TimingValue TimingSure 64.4741959095 := by
  obtain ⟨w, hI, hm, hw⟩ := timing_three_optimum
  have he := (timing_three_value_bounds hI hm).2
  exact ⟨w, hI, hm, hw, by linarith [timing_two_value_bounds.1],
    by linarith [timing_sure_value_bounds.1]⟩

/-- **Problem 6.7:** no expected-utility index over incomes can have both optimized comparisons. -/
theorem problem_6_7_no_income_index : ¬∃ U : ℝ → ℝ,
    ExpectedUtility U TimingIncomeThree < ExpectedUtility U TimingIncomeTwo ∧
    ExpectedUtility U TimingIncomeThree < ExpectedUtility U TimingIncomeSure := by
  rintro ⟨U, h₂, h₁⟩
  linarith [timing_income_mixture_value U]

end Kreps.UtilityForMoney
