/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.RiskyAssets

/-!
# Risk-neutral portfolios, arbitrage and uniqueness

Kreps I, Proposition 6.18(d–f), pp. 144–145. The return distribution may have
any finite support. An actually positive-probability strict gain gives a strict
expected improvement. Strict utility concavity at one state with a nonzero
excess return gives strict concavity of the full portfolio objective.
-/

namespace Kreps.UtilityForMoney

/-- Linear monetary utility evaluates a portfolio at its mean net return. -/
theorem portfolioValue_affine (p : SimpleLottery ℝ) (r w a A B : ℝ) :
    PortfolioValue (fun x => A * x + B) p r w a =
      A * (a * (ExpectedUtility id p - r) + r * w) + B := by
  rw [PortfolioValue, expectedUtility_affine_payoff, expected_portfolioWealth]

/-- **Proposition 6.18(d):** with linear utility all three possible solution sets are explicit. -/
theorem proposition_6_18d (p : SimpleLottery ℝ) (r w A B : ℝ) (hA : 0 < A) :
    (r < ExpectedUtility id p → PortfolioOptima (fun x => A * x + B) p r w = ∅) ∧
      (r = ExpectedUtility id p → PortfolioOptima (fun x => A * x + B) p r w = Set.Ici 0) ∧
      (ExpectedUtility id p < r → PortfolioOptima (fun x => A * x + B) p r w = {0}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha.2 (a + 1) (by linarith [ha.1])
    rw [portfolioValue_affine, portfolioValue_affine] at h
    nlinarith [mul_pos hA (sub_pos.mpr he)]
  · rintro rfl
    ext a
    exact ⟨And.left, fun ha => ⟨ha, fun b _ => by simp [portfolioValue_affine]⟩⟩
  · intro he
    apply proposition_6_18a _ _ w he
    · refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b _ _ hab
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t * B) hab]
    · exact fun _ _ h => add_lt_add_left (mul_lt_mul_of_pos_left h hA) _

/-- A weak improvement everywhere, strict on the support in one state, improves expected utility. -/
theorem expectedUtility_lt_of_support {X : Type*} (p : SimpleLottery X) {f g : X → ℝ}
    (hle : ∀ x ∈ p.weights.support, f x ≤ g x)
    (hlt : ∃ x ∈ p.weights.support, f x < g x) : ExpectedUtility f p < ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum
  · intro x hx
    exact mul_le_mul_of_nonneg_left (hle x hx) (p.nonneg x)
  · obtain ⟨x, hx, h⟩ := hlt
    exact ⟨x, hx, mul_lt_mul_of_pos_left h
      (lt_of_le_of_ne (p.nonneg x) (Ne.symm (Finsupp.mem_support_iff.mp hx)))⟩

/-- **Proposition 6.18(e):** an arbitrage strictly improves every finite risky position. -/
theorem proposition_6_18e {V : ℝ → ℝ} (hi : StrictMono V) (p : SimpleLottery ℝ) (r w : ℝ)
    (hle : ∀ t ∈ p.weights.support, r ≤ t) (hlt : ∃ t ∈ p.weights.support, r < t) :
    PortfolioOptima V p r w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  refine (not_lt_of_ge (ha.2 (a + 1) (by linarith [ha.1]))) ?_
  apply expectedUtility_lt_of_support p
  · intro t ht
    apply hi.monotone
    unfold PortfolioWealth
    nlinarith [hle t ht]
  · obtain ⟨t, ht, h⟩ := hlt
    refine ⟨t, ht, hi ?_⟩
    unfold PortfolioWealth
    nlinarith

/-- Expected utility is linear in a fixed weighted sum of state-dependent payoffs. -/
theorem expectedUtility_linear_combination {X : Type*} (p : SimpleLottery X) (f g : X → ℝ)
    (a b : ℝ) :
    ExpectedUtility (fun x => a * f x + b * g x) p =
      a * ExpectedUtility f p + b * ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Nonconstant portfolio returns preserve strict concavity of the objective in the investment. -/
theorem portfolioValue_strictConcave {V : ℝ → ℝ} (hc : StrictConcaveOn ℝ Set.univ V)
    (p : SimpleLottery ℝ) (r w : ℝ) (hn : ∃ t ∈ p.weights.support, t ≠ r) :
    StrictConcaveOn ℝ (Set.Ici 0) (PortfolioValue V p r w) := by
  refine ⟨convex_Ici _, ?_⟩
  intro a _ b _ hab c d hc' hd hsum
  simp only [smul_eq_mul]
  rw [PortfolioValue, PortfolioValue, PortfolioValue, ← expectedUtility_linear_combination]
  have he (t : ℝ) : PortfolioWealth r w (c * a + d * b) t =
      c * PortfolioWealth r w a t + d * PortfolioWealth r w b t := by
    unfold PortfolioWealth
    linear_combination -(r * w) * hsum
  apply expectedUtility_lt_of_support
  · intro t _
    rw [he]
    exact hc.concaveOn.2 (Set.mem_univ _) (Set.mem_univ _) hc'.le hd.le hsum
  · obtain ⟨t, ht, htr⟩ := hn
    refine ⟨t, ht, ?_⟩
    rw [he]
    apply hc.2 (Set.mem_univ _) (Set.mem_univ _) _ hc' hd hsum
    intro h
    apply hab
    apply (mul_right_cancel₀ (sub_ne_zero.mpr htr))
    exact add_right_cancel h

/-- **Proposition 6.18(f):** strict risk aversion and two distinct returns give uniqueness
whenever the objective attains its maximum. -/
theorem proposition_6_18f {V : ℝ → ℝ} (hd : Differentiable ℝ V)
    (hanti : StrictAnti (deriv V)) (p : SimpleLottery ℝ) (r w : ℝ)
    (hn : ∃ t ∈ p.weights.support, ∃ u ∈ p.weights.support, t ≠ u) :
    (PortfolioOptima V p r w).Subsingleton := by
  obtain ⟨t, ht, u, hu, htu⟩ := hn
  have hne : ∃ v ∈ p.weights.support, v ≠ r := by
    by_cases htr : t = r
    · exact ⟨u, hu, fun hur => htu (htr.trans hur.symm)⟩
    · exact ⟨t, ht, htr⟩
  have hc := portfolioValue_strictConcave (hanti.strictConcaveOn_univ_of_deriv hd.continuous)
    p r w hne
  intro a ha b hb
  exact hc.eq_of_isMaxOn ha.2 hb.2 ha.1 hb.1

end Kreps.UtilityForMoney
