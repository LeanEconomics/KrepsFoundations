/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.FiniteLotteryTables
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The five calculations in Problem 5.1

Kreps I, pp. 116–117, Figures 5.10–5.11. The horse-race acts return actual
finitely supported roulette lotteries. Rational inequalities for the square
roots certify the comparisons involving fourth powers without rounding a value.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The three monetary lotteries in Problem 5.1(a), in their printed order. -/
noncomputable def Problem51Money : Fin 3 → Convexity.StdSimplex ℝ ℝ :=
  ![CertainBranch.lottery (fun _ => 10000),
    (TwoBranches (1 / 3) (by constructor <;> norm_num)).lottery ![3600, 14400],
    (ThreeBranches (1 / 5) (1 / 5) (3 / 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![0, 10000, 22500]]

/-- The square-root expected utility of the `i`th printed money lottery. -/
noncomputable def Problem51MoneyValue (i : Fin 3) : ℝ :=
  (Problem51Money i).weights.sum (fun x t => t * Real.sqrt x)

/-- **Problem 5.1(a):** the third lottery is preferred, and the first two tie at 100. -/
theorem problem_5_1a : Problem51MoneyValue 0 = 100 ∧ Problem51MoneyValue 1 = 100 ∧
    Problem51MoneyValue 2 = 110 := by
  norm_num [Problem51MoneyValue, Problem51Money, BranchTable.lottery_value, certainBranch_value,
    twoBranches_value, threeBranches_value]

/-- The two-good bundles in the three acts of Figure 5.10, indexed by act and state. -/
def Figure510Act : Fin 3 → Fin 3 → ℝ × ℝ :=
  ![![(1, 4), (3, 12), (7, 7)], ![(4, 4), (2, 20), (10, 0)], fun _ => (5, 5)]

/-- The three state-dependent utilities used in parts (b) and (d). -/
noncomputable def Figure510Utility : Fin 3 → (ℝ × ℝ) → ℝ :=
  ![fun x => Real.sqrt (x.1 * x.2), fun x => 3 / 5 * min x.1 x.2,
    fun x => 2 / 5 * (x.1 + x.2)]

/-- The probabilities one-half, three-tenths and one-fifth in parts (c) and (e). -/
noncomputable def Figure510Prob : BranchTable 3 :=
  ThreeBranches (1 / 2) (3 / 10) (1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The state-independent geometric fourth root, evaluated on the nonnegative prizes. -/
noncomputable def Figure510CommonUtility (x : ℝ × ℝ) : ℝ := Real.sqrt (Real.sqrt (x.1 * x.2))

/-- On these prizes the nested square root is exactly the printed exponent `0.25`. -/
theorem figure510CommonUtility_eq_rpow {x : ℝ × ℝ} (hx : 0 ≤ x.1 * x.2) :
    Figure510CommonUtility x = (x.1 * x.2) ^ (1 / 4 : ℝ) := by
  unfold Figure510CommonUtility
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- The state-additive value of each Figure 5.10 act in part (b). -/
noncomputable def Figure510AdditiveValue (a : Fin 3) : ℝ :=
  ∑ s, Figure510Utility s (Figure510Act a s)

/-- **Problem 5.1(b):** the third act is best, the first second and the second last. -/
theorem problem_5_1b : Figure510AdditiveValue 0 = 47 / 5 ∧
    Figure510AdditiveValue 1 = 46 / 5 ∧ Figure510AdditiveValue 2 = 12 := by
  norm_num [Figure510AdditiveValue, Figure510Utility, Figure510Act, Fin.sum_univ_succ]

/-- The subjective expected utility in part (c), with a common prize utility across states. -/
noncomputable def Figure510SubjectiveValue (a : Fin 3) : ℝ :=
  Figure510Prob.value (Figure510Act a) Figure510CommonUtility

/-- Exact radical values of the three acts under subjective expected utility. -/
theorem figure510_subjective_values :
    Figure510SubjectiveValue 0 = Real.sqrt 2 / 2 + 3 * Real.sqrt 6 / 10 + Real.sqrt 7 / 5 ∧
    Figure510SubjectiveValue 1 = 1 + 3 * Real.sqrt (Real.sqrt 40) / 10 ∧
    Figure510SubjectiveValue 2 = Real.sqrt 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Figure510SubjectiveValue, Figure510Prob, BranchTable.value,
    ThreeBranches,
    Figure510Act, Figure510CommonUtility, Fin.sum_univ_succ] <;> ring

/-- Small rational enclosures used to certify the strict numerical rankings. -/
theorem figure510_root_bounds :
    (14 / 10 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 142 / 100 ∧
    (24 / 10 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < 245 / 100 ∧
    (26 / 10 : ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < 265 / 100 ∧
    (223 / 100 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 12 < 347 / 100 ∧
    Real.sqrt (Real.sqrt 40) < 26 / 10 := by
  have hs : Real.sqrt 40 < 676 / 100 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rw [Real.lt_sqrt (by norm_num)]; norm_num
          | rw [Real.sqrt_lt' (by norm_num)]; norm_num <;> linarith

/-- **Problem 5.1(c):** the strict ranking is again third, first, second. -/
theorem problem_5_1c : Figure510SubjectiveValue 2 > Figure510SubjectiveValue 0 ∧
    Figure510SubjectiveValue 0 > Figure510SubjectiveValue 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := figure510_subjective_values
  obtain ⟨a, b, c, d, e, f, g, _, i⟩ := figure510_root_bounds
  constructor <;> linarith

/-- The left act in Figure 5.11 gives a roulette lottery conditional on each state. -/
noncomputable def Figure511Left : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ) :=
  ![(TwoBranches (1 / 5) (by constructor <;> norm_num)).lottery ![(1, 4), (3, 12)],
    CertainBranch.lottery (fun _ => (7, 7)),
    (ThreeBranches (1 / 5) (7 / 20) (9 / 20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![(2, 2), (6, 24), (0, 0)]]

/-- The right act in Figure 5.11 gives the sure bundle `(5,5)` in every state. -/
noncomputable def Figure511Right : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ) :=
  fun _ => CertainBranch.lottery (fun _ => (5, 5))

/-- Sum of the three conditional expected utilities of a horse-race lottery. -/
noncomputable def Figure511Value (U : Fin 3 → (ℝ × ℝ) → ℝ)
    (h : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ)) : ℝ :=
  ∑ s, (h s).weights.sum (fun x a => a * U s x)

/-- **Problem 5.1(d):** the left horse-race lottery has strictly higher additive utility. -/
theorem problem_5_1d : Figure511Value Figure510Utility Figure511Left = 348 / 25 ∧
    Figure511Value Figure510Utility Figure511Right = 12 := by
  norm_num [Figure511Value, Figure510Utility, Figure511Left, Figure511Right,
    Fin.sum_univ_succ, BranchTable.lottery_value, certainBranch_value, twoBranches_value,
    threeBranches_value]

/-- Weight each state's common prize utilities by its subjective probability. -/
noncomputable def Figure511WeightedUtility (s : Fin 3) (x : ℝ × ℝ) : ℝ :=
  Figure510Prob.mass s * Figure510CommonUtility x

/-- Exact radical values of both horse-race lotteries under subjective expected utility. -/
theorem figure511_subjective_values :
    Figure511Value Figure511WeightedUtility Figure511Left =
      (Real.sqrt 2 / 5 + 4 * Real.sqrt 6 / 5) / 2 + 3 * Real.sqrt 7 / 10 +
        (Real.sqrt 2 / 5 + 7 * Real.sqrt 12 / 20) / 5 ∧
    Figure511Value Figure511WeightedUtility Figure511Right = Real.sqrt 5 := by
  constructor <;> norm_num [Figure511Value, Figure511WeightedUtility, Figure510Prob, ThreeBranches,
    Figure510CommonUtility, Figure511Left, Figure511Right, BranchTable.value, TwoBranches,
    CertainBranch, Fin.sum_univ_succ, BranchTable.lottery_value] <;> ring

/-- **Problem 5.1(e):** with common fourth-root utility the right lottery is strictly preferred. -/
theorem problem_5_1e : Figure511Value Figure511WeightedUtility Figure511Right >
    Figure511Value Figure511WeightedUtility Figure511Left := by
  obtain ⟨hl, hr⟩ := figure511_subjective_values
  obtain ⟨_, a, _, b, _, c, d, e, _⟩ := figure510_root_bounds
  linarith

end Kreps.ChoiceUnderUncertainty
