/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.IncomeChoice
import UtilityForMoney.StochasticDominance

/-!
# The two-stage monetary lottery in Figure 6.2

Kreps I, pp. 133–135. The six terminal branch probabilities are the products
of the first-stage probabilities and the conditional probabilities. Pushing the
common branch law forward recovers all three marginal distributions.
-/

namespace Kreps.UtilityForMoney

/-- Joint weights of the six terminal branches, ordered in pairs by initial prize. -/
noncomputable def Figure62States : SimpleLottery (Fin 6) where
  weights := Finsupp.equivFunOnFinite.symm ![1/5, 1/5, 3/20, 1/20, 1/5, 1/5]
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_fintype, Fin.sum_univ_succ]

/-- First-stage prize on each of the six joint branches. -/
def Figure62Initial : Fin 6 → ℝ := ![0, 0, 5, 5, 10, 10]

/-- Conditional supplement, in the same branch order. -/
def Figure62Supplement : Fin 6 → ℝ := ![-3, 3, -2, 3, -2, 2]

/-- The net final prize adds the supplement on the same branch. -/
def Figure62Final (i : Fin 6) : ℝ := Figure62Initial i + Figure62Supplement i

/-- Evaluation on the common state law before collecting repeated prizes. -/
theorem figure62_states_value (f : Fin 6 → ℝ) :
    ExpectedUtility f Figure62States =
      f 0 / 5 + f 1 / 5 + 3 * f 2 / 20 + f 3 / 20 + f 4 / 5 + f 5 / 5 := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  norm_num [Figure62States, Fin.sum_univ_succ]
  ring

/-- **Figure 6.2(a):** the initial distribution has masses 0.4, 0.2 and 0.4. -/
theorem figure62_initial_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Initial) =
      2/5 * U 0 + 1/5 * U 5 + 2/5 * U 10 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Initial]
  ring

/-- **Figure 6.2(c):** the reduced final law has masses 0.2, 0.35, 0.25 and 0.2. -/
theorem figure62_final_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Final) =
      1/5 * U (-3) + 7/20 * U 3 + 1/4 * U 8 + 1/5 * U 12 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Final, Figure62Initial, Figure62Supplement]
  ring

/-- Footnote 10: the marginal law of the supplement, collected across the three rows. -/
theorem figure62_supplement_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Supplement) =
      1/5 * U (-3) + 7/20 * U (-2) + 1/5 * U 2 + 1/4 * U 3 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Supplement]
  ring

/-- The three conditional supplement distributions all have nonpositive mean. -/
theorem figure62_conditional_means :
    (1/2 : ℝ) * (-3) + 1/2 * 3 = 0 ∧
      (3/4 : ℝ) * (-2) + 1/4 * 3 = -(3/4) ∧
      (1/2 : ℝ) * (-2) + 1/2 * 2 = 0 := by norm_num

/-- The initial three-outcome lottery second-order dominates the final four-outcome lottery. -/
theorem figure62_secondOrder :
    SecondOrderDominates (Figure62States.map Figure62Initial)
      (Figure62States.map Figure62Final) := by
  intro U hi hc
  rw [figure62_final_law, figure62_initial_law]
  have h (x y a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b = 1) (hz : a*x+b*y ≤ z) :
      a * U x + b * U y ≤ U z :=
    (hc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hs).trans (hi hz)
  linarith [h (-3) 3 (1/2) (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 3 8 (3/4) (1/4) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 8 12 (1/2) (1/2) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

end Kreps.UtilityForMoney
