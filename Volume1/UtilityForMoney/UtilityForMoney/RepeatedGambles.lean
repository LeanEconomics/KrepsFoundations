/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CARAPortfolio
import UtilityForMoney.LotterySimpleLottery

/-!
# Independent repetitions of the favorable-mean gamble

Kreps I, Problem 6.14, pp. 146–147. Every fresh trial pays 1,000 with
probability 2/5 and costs 500 with probability 3/5. The finite-horizon law
branches independently of past wealth. Exponential utility with coefficient
log(2)/500 gives an exact expected-utility multiplier of 13/10 per trial.
-/

namespace Kreps.UtilityForMoney

/-- An independent fresh branch with the printed win probability. -/
noncomputable def TrialBranch {X : Type*} (win lose : SimpleLottery X) : SimpleLottery X :=
  LotteryTheory.Mix ⟨2 / 5, by norm_num⟩ win lose

/-- Evaluation of a fresh trial averages its two continuation lotteries. -/
theorem trialBranch_value {X : Type*} (u : X → ℝ) (win lose : SimpleLottery X) :
    ExpectedUtility u (TrialBranch win lose) =
      (2 * ExpectedUtility u win + 3 * ExpectedUtility u lose) / 5 := by
  have he := LotteryTheory.expectedUtility_affine u (⟨2 / 5, by norm_num⟩ : LotteryTheory.Weight)
    win lose
  change ExpectedUtility u (TrialBranch win lose) =
    2 / 5 * ExpectedUtility u win + (1 - 2 / 5) * ExpectedUtility u lose at he
  rw [he]
  ring

/-- Terminal-wealth lottery with a fixed number of independent trials and no bankruptcy stop. -/
noncomputable def RepeatedLaw : ℕ → ℝ → SimpleLottery ℝ
  | 0, w => Convexity.StdSimplex.single w
  | n + 1, w => TrialBranch (RepeatedLaw n (w + 1000)) (RepeatedLaw n (w - 500))

/-- The source gamble has positive expected monetary gain of exactly 100 per trial. -/
theorem repeatedLaw_mean (n : ℕ) (w : ℝ) : ExpectedUtility id (RepeatedLaw n w) = w + 100 * n := by
  induction n generalizing w with
  | zero => simp [RepeatedLaw, expectedUtility_single]
  | succ n ih =>
    rw [RepeatedLaw, trialBranch_value, ih, ih]
    push_cast
    ring

/-- A win divides this negative exponential utility by four; a loss doubles it. -/
theorem repeated_exponential_steps (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    V (w + 1000) = V w / 4 ∧ V (w - 500) = 2 * V w := by
  dsimp only [ExponentialUtility]
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  constructor
  · rw [show -(Real.log 2 / 500) * (w + 1000) =
      -(Real.log 2 / 500) * w + -(Real.log 2 + Real.log 2) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_add, he]
    ring
  · rw [show -(Real.log 2 / 500) * (w - 500) =
      -(Real.log 2 / 500) * w + Real.log 2 by ring, Real.exp_add, he]
    ring

/-- Exact expected utility for all finite numbers of independent copies. -/
theorem repeatedLaw_exponential (n : ℕ) (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    ExpectedUtility V (RepeatedLaw n w) = (13 / 10 : ℝ) ^ n * V w := by
  intro V
  induction n generalizing w with
  | zero => simp [RepeatedLaw, expectedUtility_single]
  | succ n ih =>
    have he : V (w + 1000) = V w / 4 ∧ V (w - 500) = 2 * V w := repeated_exponential_steps w
    rw [RepeatedLaw, trialBranch_value, ih, ih, he.1, he.2, pow_succ]
    ring

/-- **Problem 6.14, interpretation 1:** a rational risk-averse consumer rejects every horizon. -/
theorem problem_6_14_unrestricted {n : ℕ} (hn : 0 < n) (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    StrictMono V ∧ StrictConcaveOn ℝ Set.univ V ∧ ExpectedUtility V (RepeatedLaw n w) < V w := by
  intro V
  have h : 0 < Real.log 2 / 500 := by positivity
  refine ⟨exponentialUtility_strictMono h, exponentialUtility_strictConcave h, ?_⟩
  rw [repeatedLaw_exponential]
  have hz : V w < 0 := neg_lt_zero.mpr (Real.exp_pos _)
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr (one_lt_pow₀ (by norm_num : (1 : ℝ) < 13 / 10)
    hn.ne')) hz]

end Kreps.UtilityForMoney
