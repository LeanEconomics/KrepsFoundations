/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries
import UtilityForMoney.Insurance
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Demand for a risky asset

Kreps I, Problem 6.10 and Proposition 6.18, pp. 144–145. The investor chooses
any nonnegative amount of the risky asset. Leveraged positions are permitted.
The return distribution is simple with arbitrary finite support.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Taking expectations commutes with any affine change of the payoffs. -/
theorem expectedUtility_affine_payoff {X : Type*} (p : SimpleLottery X) (f : X → ℝ)
    (a b : ℝ) : ExpectedUtility (fun x => a * f x + b) p = a * ExpectedUtility f p + b := by
  classical
  have ht : ∑ x ∈ p.weights.support, p.weights x = 1 := p.total
  unfold ExpectedUtility Finsupp.sum
  simp_rw [mul_add, show ∀ x, p.weights x * (a * f x) = a * (p.weights x * f x) by
    intro x; ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ht, one_mul]

/-- A constant payoff has its own value as expectation. -/
theorem expectedUtility_const {X : Type*} (p : SimpleLottery X) (c : ℝ) :
    ExpectedUtility (fun _ : X => c) p = c := by
  simpa using expectedUtility_affine_payoff p (fun _ => (0 : ℝ)) 0 c

/-- Terminal wealth in a state with risky gross return `t`. -/
def PortfolioWealth (r w a t : ℝ) : ℝ := a * (t - r) + r * w

/-- The objective in equation (6.3), with no upper bound on the risky position. -/
noncomputable def PortfolioValue (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w a : ℝ) : ℝ :=
  ExpectedUtility (fun t => V (PortfolioWealth r w a t)) p

/-- The entire portfolio solution set includes the no-short-sale constraint. -/
def PortfolioOptima (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w : ℝ) : Set ℝ :=
  {a | 0 ≤ a ∧ ∀ b, 0 ≤ b → PortfolioValue V p r w b ≤ PortfolioValue V p r w a}

/-- Expected terminal wealth as a function of the risky investment. -/
theorem expected_portfolioWealth (p : SimpleLottery ℝ) (r w a : ℝ) :
    ExpectedUtility (PortfolioWealth r w a) p = a * (ExpectedUtility id p - r) + r * w := by
  have he : PortfolioWealth r w a = fun t => a * id t + (r * w - a * r) := by
    funext t
    simp only [PortfolioWealth, id_eq]
    ring
  rw [he, expectedUtility_affine_payoff]
  ring

/-- The zero position is riskless. -/
theorem portfolioValue_zero (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w : ℝ) :
    PortfolioValue V p r w 0 = V (r * w) := by
  simp [PortfolioValue, PortfolioWealth, expectedUtility_const]

/-- Jensen's bound for a risky portfolio. -/
theorem portfolioValue_le_mean {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (p : SimpleLottery ℝ) (r w a : ℝ) :
    PortfolioValue V p r w a ≤ V (a * (ExpectedUtility id p - r) + r * w) := by
  rw [← expected_portfolioWealth]
  exact expectedUtility_jensen hc _ (fun _ => Set.mem_univ _) p

/-- **Proposition 6.18(b):** a zero excess expected return makes zero investment optimal. -/
theorem proposition_6_18b {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : SimpleLottery ℝ} {r : ℝ} (w : ℝ) (he : ExpectedUtility id p = r) :
    0 ∈ PortfolioOptima V p r w := by
  refine ⟨le_rfl, fun a _ => ?_⟩
  simpa [he, portfolioValue_zero] using portfolioValue_le_mean hc p r w a

/-- **Proposition 6.18(a):** a negative excess expected return makes zero uniquely optimal. -/
theorem proposition_6_18a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    {p : SimpleLottery ℝ} {r : ℝ} (w : ℝ) (he : ExpectedUtility id p < r) :
    PortfolioOptima V p r w = {0} := by
  have hless (a : ℝ) (ha : 0 < a) : PortfolioValue V p r w a < PortfolioValue V p r w 0 := by
    rw [portfolioValue_zero]
    apply (portfolioValue_le_mean hc p r w a).trans_lt
    apply hi
    have hneg := mul_neg_of_pos_of_neg ha (sub_neg.mpr he)
    linarith
  ext a
  change (0 ≤ a ∧ _) ↔ a = 0
  constructor
  · intro h
    by_contra hne
    exact (not_lt_of_ge (h.2 0 le_rfl)) (hless a (lt_of_le_of_ne h.1 (Ne.symm hne)))
  · rintro rfl
    refine ⟨le_rfl, fun b hb => ?_⟩
    rcases hb.eq_or_lt with heq | hpos
    · rw [← heq]
    · exact (hless b hpos).le

/-- The marginal value at zero is fixed marginal utility times the expected excess return. -/
theorem portfolioValue_hasDerivAt_zero {V : ℝ → ℝ} (p : SimpleLottery ℝ) (r w : ℝ)
    (hd : DifferentiableAt ℝ V (r * w)) :
    HasDerivAt (PortfolioValue V p r w) (deriv V (r * w) * (ExpectedUtility id p - r)) 0 := by
  classical
  have h (t : ℝ) : HasDerivAt (fun a => p.weights t * V (PortfolioWealth r w a t))
      (p.weights t * (deriv V (r * w) * (t - r))) 0 := by
    have hg : HasDerivAt (fun a : ℝ => PortfolioWealth r w a t) (t - r) 0 := by
      simpa [PortfolioWealth] using
        (((hasDerivAt_id' (0 : ℝ)).mul_const (t - r)).add_const (r * w))
    have hv : HasDerivAt V (deriv V (r * w)) (PortfolioWealth r w 0 t) := by
      simpa [PortfolioWealth] using hd.hasDerivAt
    exact ((hv.comp 0 hg).const_mul (p.weights t))
  have hsum := HasDerivAt.fun_sum (u := p.weights.support) (fun t _ => h t)
  change HasDerivAt (PortfolioValue V p r w)
    (ExpectedUtility (fun t => deriv V (r * w) * (t - r)) p) 0 at hsum
  convert hsum using 1
  rw [show (fun t => deriv V (r * w) * (t - r)) =
    (fun t => deriv V (r * w) * id t + (-(deriv V (r * w) * r))) by
    funext t; dsimp; ring, expectedUtility_affine_payoff]
  ring

/-- A positive derivative at zero gives strictly higher values for all small positive positions. -/
theorem improves_small_positive {f : ℝ → ℝ} {m : ℝ} (hd : HasDerivAt f m 0) (hm : 0 < m) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), f 0 < f a := by
  have hs : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := fun _ ha => ne_of_gt ha
  have h := hd.tendsto_slope.mono_left (nhdsWithin_mono _ hs)
  filter_upwards [h.eventually (isOpen_Ioi.mem_nhds hm), self_mem_nhdsWithin] with a hs ha
  change 0 < a at ha
  rw [slope_def_field] at hs
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr ha)).mp hs)

/-- **Proposition 6.18(c):** positive expected excess return excludes the zero position. -/
theorem proposition_6_18c {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    {p : SimpleLottery ℝ} {r w a : ℝ} (hd : DifferentiableAt ℝ V (r * w))
    (he : r < ExpectedUtility id p) (ha : a ∈ PortfolioOptima V p r w) : 0 < a := by
  apply lt_of_le_of_ne ha.1
  rintro rfl
  have hpos : ∀ᶠ b in 𝓝[>] (0 : ℝ), 0 < b := self_mem_nhdsWithin
  obtain ⟨b, hb, hv⟩ := (hpos.and (improves_small_positive
    (portfolioValue_hasDerivAt_zero p r w hd)
    (mul_pos (deriv_pos_of_concave_strictMono hc hi hd) (sub_pos.mpr he)))).exists
  exact (not_lt_of_ge (ha.2 b (le_of_lt hb))) hv

end Kreps.UtilityForMoney
