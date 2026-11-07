/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.RiskMeasures
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Risk premium of a small symmetric gamble

Kreps I, Proposition 6.9 and Problem 6.3, pp. 130, 141. Taylor expansion on a
neighborhood of the base wealth cancels the two linear terms. A local inverse
constructs a certainty equivalent from positive marginal utility. The continuous
divided difference then converts the utility expansion to a monetary risk premium.
-/

namespace Kreps.UtilityForMoney

open Filter Topology Asymptotics

/-- Second-order Taylor remainder from smoothness at the one point where it is used. -/
theorem local_second_order_remainder {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    (fun y => U y - (U x + (y - x) * deriv U x + (y - x) ^ 2 / 2 * deriv (deriv U) x))
      =o[𝓝 x] (fun y => (y - x) ^ 2) := by
  obtain ⟨s, hs, hcs⟩ := hu.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hs
  have hx := Metric.mem_ball_self hr (x := x)
  have ht := taylor_isLittleO (convex_ball x r) hx (hcs.mono hsub)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] at ht
  apply ht.congr_left
  intro y
  have he (n : ℕ) := iteratedDerivWithin_of_isOpen (f := U) (n := n) Metric.isOpen_ball hx
  simp only [show (2 : ℕ) = 1 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval,
    he, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
  norm_num
  ring_nf
  simp

/-- Expected utility of an equal-chance gain and loss of magnitude `e` about wealth `x`. -/
noncomputable def SymmetricUtility (U : ℝ → ℝ) (x e : ℝ) : ℝ := (U (x + e) + U (x - e)) / 2

/-- The equal-probability utility average cancels its first-order term. -/
theorem symmetricUtility_remainder {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    (fun e => SymmetricUtility U x e - U x - deriv (deriv U) x / 2 * e ^ 2)
      =o[𝓝 0] (fun e : ℝ => e ^ 2) := by
  have h := local_second_order_remainder hu
  have hp : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
  have hm : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have h₁ := (h.comp_tendsto hp).congr_right (g₂ := fun e : ℝ => e ^ 2) (fun e => by
    dsimp; ring)
  have h₂ := (h.comp_tendsto hm).congr_right (g₂ := fun e : ℝ => e ^ 2) (fun e => by
    dsimp; ring)
  apply ((h₁.add h₂).const_mul_left (1 / 2 : ℝ)).congr_left
  intro e
  dsimp [SymmetricUtility]
  ring

/-- The second-order limit of the difference in expected utility. -/
theorem symmetricUtility_quotient {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    Tendsto (fun e : ℝ => (SymmetricUtility U x e - U x) / e ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv U) x / 2)) := by
  have h := symmetricUtility_remainder hu
  have hzero : ∀ e : ℝ, e ^ 2 = 0 →
      SymmetricUtility U x e - U x - deriv (deriv U) x / 2 * e ^ 2 = 0 := by
    intro e he
    obtain rfl : e = 0 := by nlinarith [sq_nonneg e]
    simp [SymmetricUtility]
  have hlim := ((isLittleO_iff_tendsto hzero).mp h).mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hm : ∀ᶠ e : ℝ in 𝓝[≠] 0, e ≠ 0 := self_mem_nhdsWithin
  have hsum := hlim.add_const (deriv (deriv U) x / 2)
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hm] with e he
  field_simp
  ring

/-- The actual local risk premium of any convergent certainty-equivalent selection. -/
theorem symmetric_premium_of_certainty_equivalent {U c : ℝ → ℝ} {x : ℝ}
    (hu : ContDiffAt ℝ 2 U x) (hp : 0 < deriv U x)
    (hc : Tendsto c (𝓝[≠] 0) (𝓝 x))
    (he : ∀ᶠ e in 𝓝[≠] (0 : ℝ), U (c e) = SymmetricUtility U x e) :
    Tendsto (fun e : ℝ => (x - c e) / e ^ 2) (𝓝[≠] 0) (𝓝 (AbsoluteRiskAversion U x / 2)) := by
  have hD : Tendsto (fun e => dslope U x (c e)) (𝓝[≠] 0) (𝓝 (deriv U x)) := by
    simpa only [dslope_same, Function.comp_def] using
      ((continuousAt_dslope_same.mpr (hu.differentiableAt (by norm_num))).tendsto.comp hc)
  have hlim := (symmetricUtility_quotient hu).neg.div hD hp.ne'
  have hh : -(deriv (deriv U) x / 2) / deriv U x = AbsoluteRiskAversion U x / 2 := by
    unfold AbsoluteRiskAversion
    ring
  rw [hh] at hlim
  apply hlim.congr'
  filter_upwards [he, hD.eventually_ne hp.ne'] with e he hne
  have h := sub_smul_dslope U x (c e)
  change (c e - x) * dslope U x (c e) = U (c e) - U x at h
  dsimp
  rw [← he, ← h]
  field_simp
  ring

/-- **Proposition 6.9 and Problem 6.3:** the symmetric gamble has an actual local certainty
equivalent, and its premium divided by the squared stake tends to half the Arrow–Pratt index. -/
theorem proposition_6_9 {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x)
    (hp : 0 < deriv U x) :
    ∃ c : ℝ → ℝ, Tendsto c (𝓝 0) (𝓝 x) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), U (c e) = SymmetricUtility U x e) ∧
      Tendsto (fun e : ℝ => (x - c e) / e ^ 2) (𝓝[≠] 0)
        (𝓝 (AbsoluteRiskAversion U x / 2)) := by
  have hd := hu.hasStrictDerivAt (by norm_num)
  let g := hd.localInverse U (deriv U x) x hp.ne'
  have hleft : g (U x) = x := (hd.eventually_left_inverse hp.ne').self_of_nhds
  have hval : Tendsto (SymmetricUtility U x) (𝓝 0) (𝓝 (U x)) := by
    have hc := hu.continuousAt.tendsto
    have hp' : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
    have hm' : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
    have ht := ((hc.comp hp').add (hc.comp hm')).div_const 2
    rw [show (U x + U x) / 2 = U x by ring] at ht
    exact ht
  have hct : Tendsto (g ∘ SymmetricUtility U x) (𝓝 0) (𝓝 x) := by
    have hct' : Tendsto (g ∘ SymmetricUtility U x) (𝓝 0) (𝓝 (g (U x))) :=
      (hd.to_localInverse hp.ne').hasDerivAt.continuousAt.tendsto.comp hval
    rwa [hleft] at hct'
  have he := hval.eventually (hd.eventually_right_inverse hp.ne')
  exact ⟨_, hct, he, symmetric_premium_of_certainty_equivalent hu hp
    (hct.mono_left nhdsWithin_le_nhds) (he.filter_mono nhdsWithin_le_nhds)⟩

end Kreps.UtilityForMoney
