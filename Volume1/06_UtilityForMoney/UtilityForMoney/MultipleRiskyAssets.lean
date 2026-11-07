/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CARAPortfolio

/-!
# Hedging and dominated risky assets

Kreps I, Problem 6.12, p. 145. These constructed two-state examples use unit
initial wealth, equal state probabilities, safe gross return two, and no short
sales of any asset. An asset with low mean can hedge exposure to another asset.
A strictly dominated asset with mean above the safe rate need never be held.
-/

namespace Kreps.UtilityForMoney

/-- No short sales: two risky positions and the remaining safe position are nonnegative. -/
def RiskyPairMenu : Set (ℝ × ℝ) :=
  Set.Icc (0, 0) (1, 1) ∩ {q | q.1 + q.2 ≤ 1}

/-- The second risky asset hedges the first. Their gross returns are (0,12) and (3,0). -/
noncomputable def HedgeValue (q : ℝ × ℝ) : ℝ :=
  (ExponentialUtility 5 (3 * q.2 + 2 * (1 - q.1 - q.2)) +
    ExponentialUtility 5 (12 * q.1 + 2 * (1 - q.1 - q.2))) / 2

/-- The no-short-sale portfolio menu is compact and includes all-safe investment. -/
theorem riskyPairMenu_compact : IsCompact RiskyPairMenu ∧ (0, 0) ∈ RiskyPairMenu := by
  refine ⟨isCompact_Icc.inter_right (isClosed_le (continuous_fst.add continuous_snd)
    continuous_const), ?_⟩
  norm_num [RiskyPairMenu, Set.mem_Icc, Prod.le_def]

/-- The negative-correlation witness has an attained expected-utility optimum. -/
theorem hedgeValue_attains : ∃ q ∈ RiskyPairMenu, IsMaxOn HedgeValue RiskyPairMenu q := by
  have hc : Continuous HedgeValue := by unfold HedgeValue ExponentialUtility; fun_prop
  exact riskyPairMenu_compact.1.exists_isMaxOn ⟨_, riskyPairMenu_compact.2⟩ hc.continuousOn

/-- **Problem 6.12:** every optimum demands the hedge despite its mean 3/2 being below 2. -/
theorem problem_6_12_hedge {q : ℝ × ℝ} (hq : q ∈ RiskyPairMenu)
    (ho : IsMaxOn HedgeValue RiskyPairMenu q) : 0 < q.2 := by
  by_contra! hn
  have hzero : q.2 = 0 := le_antisymm hn hq.1.1.2
  let z : ℝ × ℝ := (1 / 5, 4 / 5)
  have hz : z ∈ RiskyPairMenu := by norm_num [z, RiskyPairMenu, Set.mem_Icc, Prod.le_def]
  have hbest : HedgeValue z ≤ HedgeValue q := ho hz
  have heq : HedgeValue z = -Real.exp (-12) := by norm_num [HedgeValue, z, ExponentialUtility]
  rw [heq] at hbest
  have hc₁ : 3 * q.2 + 2 * (1 - q.1 - q.2) ≤ 2 := by
    rw [hzero]
    linarith [hq.1.1.1]
  have h₁ := (exponentialUtility_strictMono (by norm_num : (0 : ℝ) < 5)).monotone hc₁
  have h₂ : ExponentialUtility 5 (12 * q.1 + 2 * (1 - q.1 - q.2)) < 0 :=
    neg_lt_zero.mpr (Real.exp_pos _)
  have he : Real.exp (-10) = Real.exp (-12) * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  unfold HedgeValue at hbest
  have hv : ExponentialUtility 5 2 = -Real.exp (-10) := by norm_num [ExponentialUtility]
  rw [hv, he] at h₁
  nlinarith [Real.exp_pos (-12), Real.add_one_le_exp (2 : ℝ),
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 : ℝ)) (Real.exp_pos (-12)).le]

/-- The two risky assets have gross returns (3,4) and (4,5), respectively. -/
noncomputable def DominatedValue (U : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (U (3 * q.1 + 4 * q.2 + 2 * (1 - q.1 - q.2)) +
    U (4 * q.1 + 5 * q.2 + 2 * (1 - q.1 - q.2))) / 2

/-- **Problem 6.12:** all wealth goes to the dominating asset though both means exceed two. -/
theorem problem_6_12_dominated (U : ℝ → ℝ) (hU : StrictMono U) :
    (0, 1) ∈ RiskyPairMenu ∧ ∀ q ∈ RiskyPairMenu, q ≠ (0, 1) →
      DominatedValue U q < DominatedValue U (0, 1) := by
  refine ⟨by norm_num [RiskyPairMenu, Set.mem_Icc, Prod.le_def], fun q hq hn => ?_⟩
  have hpos : 0 < q.1 ∨ q.2 < 1 := by
    by_contra! hw
    exact hn (Prod.ext (le_antisymm hw.1 hq.1.1.1) (le_antisymm hq.1.2.2 hw.2))
  have hs : q.1 + q.2 ≤ 1 := hq.2
  have h₁ : 3 * q.1 + 4 * q.2 + 2 * (1 - q.1 - q.2) < 4 := by
    rcases hpos with h | h <;> linarith
  have h₂ : 4 * q.1 + 5 * q.2 + 2 * (1 - q.1 - q.2) < 5 := by
    rcases hpos with h | h <;> linarith
  unfold DominatedValue
  norm_num
  linarith [hU h₁, hU h₂]

end Kreps.UtilityForMoney
