/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ComparativeRisk
import UtilityForMoney.RiskMeasures
import UtilityForMoney.RiskyAssets

/-!
# Marginal utility ratios and comparison of risk aversion

Kreps I, Proposition 6.8, p. 129. The derivative of the ratio of two marginal
utilities has the opposite sign to the difference between their Arrow–Pratt
coefficients. Applying Cauchy's mean value theorem on the segment between two
prizes gives a supporting affine comparison on the second utility scale.
-/

namespace Kreps.UtilityForMoney

/-- The ratio of marginal prize utilities at a common wealth. -/
noncomputable def MarginalRatio (W V : ℝ → ℝ) (x : ℝ) : ℝ := deriv W x / deriv V x

/-- Comparison of Arrow–Pratt coefficients makes the ratio of marginal utilities nonincreasing. -/
theorem antitoneOn_marginalRatio {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, DifferentiableAt ℝ (deriv W) x)
    (hV : ∀ x ∈ S, DifferentiableAt ℝ (deriv V) x)
    (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hA : ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x) :
    AntitoneOn (MarginalRatio W V) S := by
  have hd (x : ℝ) (hx : x ∈ S) := ((hW x hx).hasDerivAt.div (hV x hx).hasDerivAt (hpV x hx).ne')
  apply antitoneOn_of_deriv_nonpos hS
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxs := interior_subset hx
    change deriv (deriv W / deriv V) x ≤ 0
    rw [(hd x hxs).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := (div_le_div_iff₀ (hpV x hxs) (hpW x hxs)).mp (hA x hxs)
    nlinarith

/-- Ordered marginal ratios give the global supporting comparison between any two prizes. -/
theorem utility_le_marginalRatio_support {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, DifferentiableAt ℝ W x) (hV : ∀ x ∈ S, DifferentiableAt ℝ V x)
    (hVi : StrictMonoOn V S) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hR : AntitoneOn (MarginalRatio W V) S) {x z : ℝ} (hx : x ∈ S) (hz : z ∈ S) :
    W z ≤ W x + MarginalRatio W V x * (V z - V x) := by
  have key {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      ∃ c ∈ Set.Ioo a b, c ∈ S ∧ W b - W a = (V b - V a) * MarginalRatio W V c := by
    have hs := hS.ordConnected.out ha hb
    obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope W (deriv W) hab
      (fun t ht => (hW t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hW t (hs ⟨ht.1.le, ht.2.le⟩)).hasDerivAt) V (deriv V)
      (fun t ht => (hV t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hV t (hs ⟨ht.1.le, ht.2.le⟩)).hasDerivAt)
    have hcS := hs ⟨hc.1.le, hc.2.le⟩
    refine ⟨c, hc, hcS, ?_⟩
    unfold MarginalRatio
    field_simp [(hpV c hcS).ne']
    linarith
  rcases lt_trichotomy x z with h | rfl | h
  · obtain ⟨c, hc, hcs, he⟩ := key hx hz h
    have := mul_le_mul_of_nonneg_left (hR hx hcs hc.1.le) (sub_nonneg.mpr (hVi hx hz h).le)
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs, he⟩ := key hz hx h
    have := mul_le_mul_of_nonneg_left (hR hcs hx hc.2.le) (sub_nonneg.mpr (hVi hz hx h).le)
    nlinarith

/-- **Proposition 6.8, sufficient direction:** coefficient comparison suffices for every
lottery, on any interval of common prizes. -/
theorem moreRiskAverse_of_arrowPratt {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, ContDiffAt ℝ 2 W x) (hV : ∀ x ∈ S, ContDiffAt ℝ 2 V x)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hA : ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x) :
    MoreRiskAverse S W V := by
  have hR := antitoneOn_marginalRatio hS
    (fun x hx => ((hW x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one)
    (fun x hx => ((hV x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one) hpW hpV hA
  intro p x hx
  let R := MarginalRatio W V x
  have hpos : 0 < R := div_pos (hpW x x.property) (hpV x x.property)
  have hpt (z : S) : W z ≤ R * V z + (W x - R * V x) := by
    have h := utility_le_marginalRatio_support hS
      (fun t ht => (hW t ht).differentiableAt (by norm_num))
      (fun t ht => (hV t ht).differentiableAt (by norm_num)) hVi hpV hR x.property z.property
    dsimp [R]
    linarith
  have he : ExpectedUtility (fun z : S => W z) p ≤
      ExpectedUtility (fun z : S => R * V z + (W x - R * V x)) p := by
    apply Finset.sum_le_sum
    exact fun z _ => mul_le_mul_of_nonneg_left (hpt z) (p.nonneg z)
  rw [expectedUtility_affine_payoff] at he
  by_contra! hn
  nlinarith [mul_lt_mul_of_pos_left hn hpos]

end Kreps.UtilityForMoney
