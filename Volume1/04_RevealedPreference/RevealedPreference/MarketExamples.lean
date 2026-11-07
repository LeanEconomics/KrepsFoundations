/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.AfriatTheorem

/-!
# The literal market datasets

Kreps I, Table 4.1 and the modified third observation, pp. 67-70, and Table 4.2,
Problem 4.1, p. 78. All prices, incomes, bundles and cross-expenditure entries
are exact rational numbers. GARP certificates control arbitrary revealed chains;
the positive conclusions rationalize complete budget sets on the full orthant.
-/

namespace Kreps.RevealedPreference

/-- The three chosen bundles in Table 4.1, retained in the modified example. -/
noncomputable def InitialBundles (i : Fin 3) : NonnegativeOrthant 3 :=
  ⟨![![10, 10, 10], ![9, 25, 15 / 2], ![15, 5, 9]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩

/-- The original three observations from pp. 67-68. -/
noncomputable def InitialData : MarketData (Fin 3) 3 where
  price := ![![10, 10, 10], ![10, 1, 2], ![1, 1, 10]]
  income := ![300, 130, 110]
  bundle := InitialBundles
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, InitialBundles, Fin.sum_univ_succ]

/-- Every literal entry of Table 4.1, with its printed rows of bundles and columns of prices. -/
theorem table_4_1_costs (i j : Fin 3) :
    Expenditure (InitialData.price j) (InitialData.bundle i).val =
      ![![300, 130, 120], ![415, 130, 109], ![290, 173, 110]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [InitialData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- All original observations use their entire stated income. -/
theorem initialData_exhausts (i : Fin 3) :
    Expenditure (InitialData.price i) (InitialData.bundle i).val = InitialData.income i := by
  fin_cases i <;>
    norm_num [InitialData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The original three observations contain the source's strict revealed cycle. -/
theorem initialData_not_garp : ¬GARP InitialData := by
  intro hG
  apply hG 0
  apply revealedStrict_weak_trans (directStrict_revealedStrict (j := 2) ?_)
    ((directWeak_revealedWeak (j := 1) ?_).trans (directWeak_revealedWeak ?_))
  all_goals norm_num [DirectStrict, DirectWeak, MarketData.cost, InitialData,
    InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The original example cannot be rationalized by primitive rational insatiable preferences. -/
theorem initialData_not_rationalizable :
    ¬∃ r, Rational r ∧ LocallyInsatiable r ∧ Rationalizes InitialData r :=
  fun ⟨_, hr, hl, hR⟩ => initialData_not_garp (rationalizes_garp hr hl hR)

/-- The modified third price vector and income from p. 69. -/
noncomputable def ModifiedData : MarketData (Fin 3) 3 where
  price := ![![10, 10, 10], ![10, 1, 2], ![1, 2, 10]]
  income := ![300, 130, 115]
  bundle := InitialBundles
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, InitialBundles, Fin.sum_univ_succ]

/-- At the modified third prices, the other bundles cost 130 and 134, both above 115. -/
theorem modifiedData_third_costs (i : Fin 3) :
    Expenditure (ModifiedData.price 2) (ModifiedData.bundle i).val = ![130, 134, 115] i := by
  fin_cases i <;>
    norm_num [ModifiedData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The modified observations have no strict revealed cycle. -/
theorem modifiedData_garp : GARP ModifiedData := by
  apply matrixGARP_of_scores ![1, 2, 0]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectWeak, MarketData.cost, ModifiedData, InitialBundles,
        Expenditure, Fin.sum_univ_succ] at *
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectStrict, MarketData.cost, ModifiedData, InitialBundles,
        Expenditure, Fin.sum_univ_succ] at *

/-- The modified example has a regular utility rationalizer on the entire commodity space. -/
theorem modifiedData_rationalizable :
    ∃ u : (Fin 3 → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧ ConcaveOn ℝ Set.univ u ∧
      Rationalizes ModifiedData (UtilityPref (fun x : NonnegativeOrthant 3 => u x.val)) :=
  garp_exists_concave_utility modifiedData_garp

/-- The four observations stated in Table 4.2, Problem 4.1. -/
noncomputable def Problem41Data : MarketData (Fin 4) 3 where
  price := ![![1, 1, 1], ![3, 1, 1], ![1, 2, 2], ![1, 1, 2]]
  income := ![20, 20, 25, 20]
  bundle := fun i => ⟨![![10, 5, 5], ![3, 5, 6], ![13, 3, 3], ![15, 3, 1]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, Fin.sum_univ_succ]

/-- Exact cross-expenditures for Table 4.2, with rows of prices and columns of bundles. -/
theorem table_4_2_costs (i j : Fin 4) :
    Expenditure (Problem41Data.price i) (Problem41Data.bundle j).val =
      ![![20, 14, 19, 19], ![40, 20, 45, 49], ![30, 25, 25, 23], ![25, 20, 22, 20]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Problem41Data, Expenditure, Fin.sum_univ_succ]

/-- **Problem 4.1:** the order of revealed comparisons is first, third, fourth, second. -/
theorem problem_4_1_garp : GARP Problem41Data := by
  apply matrixGARP_of_scores ![3, 0, 2, 1]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectWeak, MarketData.cost, Problem41Data, Expenditure, Fin.sum_univ_succ] at *
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectStrict, MarketData.cost, Problem41Data, Expenditure, Fin.sum_univ_succ] at *

/-- **Problem 4.1:** the literal four observations admit the full regular consumer model. -/
theorem problem_4_1 :
    ∃ u : (Fin 3 → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧ ConcaveOn ℝ Set.univ u ∧
      Rationalizes Problem41Data (UtilityPref (fun x : NonnegativeOrthant 3 => u x.val)) :=
  garp_exists_concave_utility problem_4_1_garp

end Kreps.RevealedPreference
