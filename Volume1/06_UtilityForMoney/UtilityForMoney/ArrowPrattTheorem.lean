/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ArrowPrattComparison
import UtilityForMoney.LocalRiskPremium

/-!
# Necessity of the Arrow–Pratt coefficient comparison

Kreps I, Proposition 6.8, p. 129. Local symmetric gambles compare the risk
premia at interior points of the common interval. Continuity extends the
coefficient inequality to included endpoints of a nondegenerate interval.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Acceptance comparisons of all simple lotteries order Arrow–Pratt coefficients at an
interior wealth, with only local twice-continuous differentiability needed there. -/
theorem arrowPratt_le_of_moreRiskAverse_interior {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interior S) (hVi : StrictMonoOn V S) (hR : MoreRiskAverse S W V)
    (hW : ContDiffAt ℝ 2 W x) (hV : ContDiffAt ℝ 2 V x)
    (hpW : 0 < deriv W x) (hpV : 0 < deriv V x) :
    AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x := by
  obtain ⟨w, hw, hwe, hwlim⟩ := proposition_6_9 hW hpW
  obtain ⟨v, hv, hve, hvlim⟩ := proposition_6_9 hV hpV
  have hs := mem_interior_iff_mem_nhds.mp hx
  have hplus : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
  have hminus : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have horder : ∀ᶠ e in 𝓝 (0 : ℝ), w e ≤ v e := by
    filter_upwards [hw hs, hv hs, hplus hs, hminus hs, hwe, hve]
      with e hwS hvS hpS hmS hwe' hve'
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
    let p := BinaryLottery (⟨x + e, hpS⟩ : S) ⟨x - e, hmS⟩ (1 / 2) hhalf
    have hcalc (U : ℝ → ℝ) : ExpectedUtility (fun t : S => U t) p = SymmetricUtility U x e := by
      dsimp only [p]
      rw [expectedUtility_binary (fun t : S => U t) _ _ _ hhalf]
      unfold SymmetricUtility
      ring
    have he := hR p ⟨w e, hwS⟩ (by rw [hcalc]; exact hwe'.le)
    rw [hcalc, ← hve'] at he
    exact (hVi.le_iff_le hwS hvS).mp he
  have he : ∀ᶠ e in 𝓝[≠] (0 : ℝ), (x - v e) / e ^ 2 ≤ (x - w e) / e ^ 2 := by
    filter_upwards [horder.filter_mono nhdsWithin_le_nhds] with e he
    exact div_le_div_of_nonneg_right (sub_le_sub_left he x) (sq_nonneg e)
  linarith [le_of_tendsto_of_tendsto hvlim hwlim he]

/-- **Proposition 6.8:** the comparative risk criterion equals pointwise comparison of
absolute risk coefficients throughout the common nondegenerate interval. -/
theorem proposition_6_8 {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {W V : ℝ → ℝ} (hW : ∀ x ∈ S, ContDiffAt ℝ 2 W x) (hV : ∀ x ∈ S, ContDiffAt ℝ 2 V x)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x) :
    MoreRiskAverse S W V ↔ ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x := by
  refine ⟨?_, moreRiskAverse_of_arrowPratt hS hW hV hVi hpW hpV⟩
  intro h x hx
  have hc {U : ℝ → ℝ} (hs : ContDiffAt ℝ 2 U x) (hp : 0 < deriv U x) :
      ContinuousAt (AbsoluteRiskAversion U) x := by
    have hd := hs.derivWithin (m := 1) (by norm_num)
    have hdd := hd.derivWithin (m := 0) (by norm_num)
    exact hdd.continuousAt.neg.div hd.continuousAt hp.ne'
  have hxcl : x ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  apply le_of_tendsto_of_tendsto
    ((hc (hV x hx) (hpV x hx)).continuousWithinAt (s := interior S))
    ((hc (hW x hx) (hpW x hx)).continuousWithinAt (s := interior S))
  filter_upwards [self_mem_nhdsWithin (a := x) (s := interior S)] with y hy
  exact arrowPratt_le_of_moreRiskAverse_interior hy hVi h (hW y (interior_subset hy))
    (hV y (interior_subset hy)) (hpW y (interior_subset hy)) (hpV y (interior_subset hy))

end Kreps.UtilityForMoney
