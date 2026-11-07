/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EmpiricalCritiques
import ChoiceUnderUncertainty.HorseLotteries

/-!
# Compound lotteries and the order of randomization

Kreps I, Figures 5.5–5.7, pp. 87, 102–103, and the steak/chicken comparison
on p. 106. The numerical reductions are proved as equalities of probability
distributions on prizes. Distributions on entire acts retain their correlations.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- An indicator payoff recovers the mass of the corresponding prize. -/
theorem expectedUtility_indicator {X : Type*} [DecidableEq X] (p : SimpleLottery X) (x : X) :
    ExpectedUtility (fun y => if y = x then 1 else 0) p = p.weights x := by
  classical
  unfold ExpectedUtility
  rw [Finsupp.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- Equality of all expected utilities separates actual prize distributions. -/
theorem lottery_eq_of_all_values {X : Type*} {p q : SimpleLottery X}
    (h : ∀ U : X → ℝ, ExpectedUtility U p = ExpectedUtility U q) : p = q := by
  classical
  apply Convexity.StdSimplex.ext
  ext x
  simpa only [expectedUtility_indicator] using h (fun y => if y = x then 1 else 0)

/-- Four explicit masses for the reduced lottery in Figure 5.5. -/
noncomputable def Figure55Reduced : BranchTable 4 :=
  ⟨![1 / 2, 1 / 30, 1 / 5, 4 / 15], by intro i; fin_cases i <;> norm_num,
    by norm_num [Fin.sum_univ_succ]⟩

/-- Figure 5.5 combines two lottery diagrams, merging their common prize. -/
theorem figure55_reduction :
    Mix ⟨1 / 3, by constructor <;> norm_num⟩
        ((ThreeBranches (3 / 10) (1 / 10) (6 / 10) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).lottery (![0, 1, 2] : Fin 3 → Fin 4))
        ((TwoBranches (3 / 5) (by constructor <;> norm_num)).lottery ![0, 3]) =
      Figure55Reduced.distribution := by
  apply lottery_eq_of_all_values
  intro U
  rw [expectedUtility_affine U, expectedUtility_branchLottery, expectedUtility_branchLottery,
    expectedUtility_eq_sum]
  norm_num [Figure55Reduced, BranchTable.distribution, ThreeBranches, TwoBranches,
    BranchTable.value, Fin.sum_univ_succ]
  ring

/-- Figure 5.6(a,c): the same deterministic act as statewise sure roulette prizes. -/
theorem figure56_deterministic (U : ℝ → ℝ) (s : Fin 3) :
    ExpectedUtility U (PureLottery ((![1, -2, 0] : Fin 3 → ℝ) s)) =
      U ((![1, -2, 0] : Fin 3 → ℝ) s) := expectedUtility_pure _ _

/-- Figure 5.6(b), also the first lottery in Figure 5.7. -/
noncomputable def Figure57First : HorseLottery (Fin 3) ℝ :=
  ![PureLottery (-2), BinaryCash (1 / 2) (by constructor <;> norm_num) 3 1,
    BinaryCash (1 / 3) (by constructor <;> norm_num) 6 (-4)]

/-- The second Figure 5.7 lottery. -/
noncomputable def Figure57Second : HorseLottery (Fin 3) ℝ :=
  ![BinaryCash (1 / 2) (by constructor <;> norm_num) (-2) 5, PureLottery 5,
    BinaryCash (1 / 2) (by constructor <;> norm_num) 6 3]

/-- Statewise reduced probabilities printed in the final panel of Figure 5.7. -/
noncomputable def Figure57Reduced : HorseLottery (Fin 3) ℝ :=
  ![BinaryCash (7 / 8) (by constructor <;> norm_num) (-2) 5,
    (ThreeBranches (3 / 8) (3 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![3, 1, 5],
    (ThreeBranches (3 / 8) (1 / 2) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![6, -4, 3]]

/-- Figure 5.7 is an equality of horse-race lotteries, including repeated prizes in each state. -/
theorem figure57_reduction :
    Mix ⟨3 / 4, by constructor <;> norm_num⟩ Figure57First Figure57Second = Figure57Reduced := by
  funext s
  rw [mix_act_apply]
  apply lottery_eq_of_all_values
  intro U
  rw [expectedUtility_affine U]
  fin_cases s <;> norm_num [Figure57First, Figure57Second, Figure57Reduced, expectedUtility_pure,
    binaryCash_expectedUtility, expectedUtility_branchLottery, threeBranches_value] <;> ring

/-- A deterministic steak/chicken menu across two states, with true denoting steak. -/
noncomputable def DinnerAct (a b : Bool) : HorseLottery (Fin 2) Bool := ![PureLottery a,
  PureLottery b]

/-- Mixtures of matching dinners and mixtures of opposite dinners coincide state by state. -/
theorem dinner_horses_first :
    Mix ⟨1 / 2, by constructor <;> norm_num⟩ (DinnerAct true true) (DinnerAct false false) =
      Mix ⟨1 / 2, by constructor <;> norm_num⟩ (DinnerAct true false) (DinnerAct false true) := by
  funext s
  simp only [mix_act_apply]
  fin_cases s
  · rfl
  · apply lottery_eq_of_all_values
    intro U
    rw [expectedUtility_affine U, expectedUtility_affine U]
    simp [DinnerAct, expectedUtility_pure]
    ring

/-- A state-complementary prize value on an entire deterministic dinner plan. -/
def MatchingDinnerValue (h : Fin 2 → Bool) : ℝ := if h 0 = h 1 then 1 else 0

/-- Roulette first can distinguish the two joint laws that horses-first mixing identifies. -/
theorem dinner_roulette_first :
    ExpectedUtility MatchingDinnerValue
      ((TwoBranches (1 / 2) (by constructor <;> norm_num)).lottery
        ![(![true, true] : Fin 2 → Bool), ![false, false]]) = 1 ∧
    ExpectedUtility MatchingDinnerValue
      ((TwoBranches (1 / 2) (by constructor <;> norm_num)).lottery
        ![(![true, false] : Fin 2 → Bool), ![false, true]]) = 0 := by
  norm_num [expectedUtility_branchLottery, twoBranches_value, MatchingDinnerValue]

/-- The joint dinner-plan payoff cannot be expressed by a sum of two single-state payoffs. -/
theorem dinner_not_stateAdditive :
    ¬∃ U : Fin 2 → Bool → ℝ, ∀ h, MatchingDinnerValue h = StateAdditiveValue U h := by
  rintro ⟨U, h⟩
  have a := h ![true, true]
  have b := h ![false, false]
  have c := h ![true, false]
  have d := h ![false, true]
  norm_num [MatchingDinnerValue, StateAdditiveValue, Fin.sum_univ_two] at a b c d
  linarith

end Kreps.ChoiceUnderUncertainty
