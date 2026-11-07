/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ConstantAbsoluteRisk
import UtilityForMoney.PortfolioCases

/-!
# Investment under constant absolute risk aversion

Kreps I, Problem 6.11, p. 145. The wealth term factors out of exponential
expected utility and the risk-aversion parameter rescales the risky position.
A loss return with positive probability bounds the optimizer in a compact
interval even though borrowing at the safe rate is permitted.
-/

namespace Kreps.UtilityForMoney

/-- The normalized portfolio value is minus the expected exponential loss. -/
theorem cara_unit_value (p : SimpleLottery ℝ) (r a : ℝ) :
    PortfolioValue (ExponentialUtility 1) p r 0 a =
      -∑ t ∈ p.weights.support, p.weights t * Real.exp (a * (r - t)) := by
  unfold PortfolioValue ExpectedUtility Finsupp.sum ExponentialUtility PortfolioWealth
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [show -1 * (a * (t - r) + r * 0) = a * (r - t) by ring, mul_neg]

/-- Exponential expected utility factors into a positive wealth term and a scaled-risk value. -/
theorem cara_portfolio_factor (p : SimpleLottery ℝ) (r w k a : ℝ) :
    PortfolioValue (ExponentialUtility k) p r w a =
      Real.exp (-k * (r * w)) * PortfolioValue (ExponentialUtility 1) p r 0 (k * a) := by
  rw [cara_unit_value]
  unfold PortfolioValue ExpectedUtility Finsupp.sum ExponentialUtility PortfolioWealth
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [show -k * (a * (t - r) + r * w) = -k * (r * w) + k * a * (r - t) by ring, Real.exp_add]
  ring

/-- Strictly positive loss probability makes the normalized problem attain a finite maximum. -/
theorem cara_unit_attains (p : SimpleLottery ℝ) (r : ℝ)
    (hbad : ∃ t ∈ p.weights.support, t < r) :
    (PortfolioOptima (ExponentialUtility 1) p r 0).Nonempty := by
  obtain ⟨t, ht, htr⟩ := hbad
  have hp : 0 < p.weights t :=
    lt_of_le_of_ne (p.nonneg t) (Ne.symm (Finsupp.mem_support_iff.mp ht))
  let A := 1 / (p.weights t * (r - t))
  have hA : 0 < A := div_pos zero_lt_one (mul_pos hp (sub_pos.mpr htr))
  let F := PortfolioValue (ExponentialUtility 1) p r 0
  have hc : Continuous F := by
    unfold F
    simp_rw [funext (cara_unit_value p r)]
    fun_prop
  obtain ⟨a, ha, haopt⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hA.le) hc.continuousOn
  refine ⟨a, ha.1, fun b hb => ?_⟩
  by_cases hle : b ≤ A
  · exact haopt ⟨hb, hle⟩
  · have hbig : 1 < b * (p.weights t * (r - t)) :=
      (div_lt_iff₀ (mul_pos hp (sub_pos.mpr htr))).mp (lt_of_not_ge hle)
    have hl := Finset.single_le_sum (fun i (_ : i ∈ p.weights.support) =>
      mul_nonneg (p.nonneg i) (Real.exp_pos (b * (r - i))).le) ht
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b * (r - t))) hp.le
    have hf : F b < F 0 := by
      rw [show F b = _ from cara_unit_value p r b, show F 0 = _ from portfolioValue_zero _ _ _ _]
      simp only [ExponentialUtility, mul_zero, Real.exp_zero]
      linarith only [hl, he, hp, hbig]
    exact hf.le.trans (haopt (show (0 : ℝ) ∈ Set.Icc 0 A from ⟨le_rfl, hA.le⟩))

/-- The optimum set at any wealth and positive risk coefficient rescales the unit optimum. -/
theorem cara_optima_scale (p : SimpleLottery ℝ) (r w : ℝ) {k : ℝ} (hk : 0 < k) (a : ℝ) :
    a ∈ PortfolioOptima (ExponentialUtility k) p r w ↔
      k * a ∈ PortfolioOptima (ExponentialUtility 1) p r 0 := by
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨mul_nonneg hk.le ha, fun b hb => ?_⟩
    have h := hm (b / k) (div_nonneg hb hk.le)
    rw [cara_portfolio_factor p r w k (b / k), cara_portfolio_factor p r w k a,
      mul_comm k (b / k),
      div_mul_cancel₀ _ hk.ne', mul_le_mul_iff_right₀ (Real.exp_pos _)] at h
    exact h
  · rintro ⟨ha, hm⟩
    refine ⟨(mul_nonneg_iff_of_pos_left hk).mp ha, fun b hb => ?_⟩
    rw [cara_portfolio_factor p r w k b, cara_portfolio_factor p r w k a]
    exact mul_le_mul_of_nonneg_left (hm (k * b) (mul_nonneg hk.le hb)) (Real.exp_pos _).le

/-- **Problem 6.11(a–c):** the optimum equals a constant divided by the risk coefficient. -/
theorem problem_6_11 (p : SimpleLottery ℝ) {r : ℝ} (hmean : r < ExpectedUtility id p)
    (hbad : ∃ t ∈ p.weights.support, t < r) :
    ∃ A > 0, ∀ w k : ℝ, 0 < k → PortfolioOptima (ExponentialUtility k) p r w = {A / k} := by
  obtain ⟨A, hA⟩ := cara_unit_attains p r hbad
  have hsp := portfolioValue_strictConcave (exponentialUtility_strictConcave zero_lt_one) p r 0
    (hbad.imp fun t ⟨ht, hlt⟩ => ⟨ht, hlt.ne⟩)
  have hApos : 0 < A := proposition_6_18c
    (exponentialUtility_strictConcave zero_lt_one).concaveOn
    (exponentialUtility_strictMono zero_lt_one)
    (exponentialUtility_hasDerivAt 1 _).differentiableAt hmean hA
  refine ⟨A, hApos, fun w k hk => ?_⟩
  ext a
  rw [Set.mem_singleton_iff, cara_optima_scale p r w hk]
  constructor
  · intro ha
    have he := hsp.eq_of_isMaxOn ha.2 hA.2 ha.1 hA.1
    exact (eq_div_iff hk.ne').mpr ((mul_comm _ _).trans he)
  · rintro rfl
    rwa [mul_comm k, div_mul_cancel₀ _ hk.ne']

/-- The inverse risk-aversion formula decreases as the coefficient increases. -/
theorem cara_position_antitone {A : ℝ} (hA : 0 ≤ A) {k l : ℝ} (hk : 0 < k) (hkl : k ≤ l) :
    A / l ≤ A / k := div_le_div_of_nonneg_left hA hk hkl

end Kreps.UtilityForMoney
