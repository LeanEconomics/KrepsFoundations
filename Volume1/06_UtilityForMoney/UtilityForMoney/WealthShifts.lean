/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ArrowPrattTheorem
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Wealth shifts and absolute risk aversion

Kreps I, Definition 6.11 and Proposition 6.12, pp. 130–131. For each pair of
wealth shifts we quantify over simple lotteries whose shifted prizes remain in
the common interval. A larger risk premium corresponds to a lower certainty
equivalent once the deterministic wealth shift has been removed.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Every risk premium under `W` is at least its counterpart under `V`, since the mean is shared. -/
def PremiumOrder (S : Set ℝ) (W V : ℝ → ℝ) : Prop :=
  ∀ (p : SimpleLottery S) (w v : S),
    IsCertaintyEquivalent (fun x : S => W x) p w →
    IsCertaintyEquivalent (fun x : S => V x) p v → RiskPremium p v ≤ RiskPremium p w

/-- Ranking all premia is equivalent to the acceptance ordering in Definition 6.6. -/
theorem premiumOrder_iff_moreRiskAverse {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hWi : StrictMonoOn W S) (hVi : StrictMonoOn V S)
    (hW : ContinuousOn W S) (hV : ContinuousOn V S) :
    PremiumOrder S W V ↔ MoreRiskAverse S W V := by
  constructor
  · intro h p x hx
    obtain ⟨w, hw⟩ := proposition_6_5_exists hS hW p
    obtain ⟨v, hv⟩ := proposition_6_5_exists hS hV p
    have hp := h p w v hw hv
    have hxw := (hWi.le_iff_le x.property w.property).mp (hx.trans hw.ge)
    have hwv : (w : ℝ) ≤ v := by
      unfold RiskPremium at hp
      linarith
    exact (hVi.monotoneOn x.property v.property (hxw.trans hwv)).trans hv.le
  · intro h p w v hw hv
    have hvw := h p w hw.le
    have he := (hVi.le_iff_le w.property v.property).mp (hvw.trans hv.ge)
    unfold RiskPremium
    exact sub_le_sub_left he _

/-- The unshifted prizes for which both wealth shifts stay in the original monetary interval. -/
def ShiftDomain (S : Set ℝ) (u v : ℝ) : Set ℝ := {x | x + u ∈ S ∧ x + v ∈ S}

/-- The overlapping shifted domain is convex, including empty and singleton overlaps. -/
theorem shiftDomain_convex {S : Set ℝ} (hS : Convex ℝ S) (u v : ℝ) :
    Convex ℝ (ShiftDomain S u v) := by
  intro x hx y hy a b ha hb hab
  have h (t : ℝ) (hxt : x + t ∈ S) (hyt : y + t ∈ S) :
      a • x + b • y + t ∈ S := by
    convert hS hxt hyt ha hb hab using 1
    simp only [smul_eq_mul]
    linear_combination -t * hab
  exact ⟨h u hx.1 hy.1, h v hx.2 hy.2⟩

/-- An absolute risk comparison after two shifts uses each utility on exactly its shared domain. -/
def ShiftPremiumOrder (S : Set ℝ) (U : ℝ → ℝ) (u v : ℝ) : Prop :=
  PremiumOrder (ShiftDomain S u v) (fun t => U (t + u)) (fun t => U (t + v))

/-- The local coefficient at a shifted prize is the original coefficient at final wealth. -/
theorem absoluteRiskAversion_shift (U : ℝ → ℝ) (u x : ℝ) :
    AbsoluteRiskAversion (fun t => U (t + u)) x = AbsoluteRiskAversion U (x + u) := by
  simp only [AbsoluteRiskAversion, funext (deriv_comp_add_const U u),
    deriv_comp_add_const]

/-- The shifted premium relation can be evaluated using acceptance comparisons. -/
theorem shiftPremiumOrder_iff {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hc : ContinuousOn U S) (u v : ℝ) :
    ShiftPremiumOrder S U u v ↔
      MoreRiskAverse (ShiftDomain S u v) (fun t => U (t + u)) (fun t => U (t + v)) := by
  apply premiumOrder_iff_moreRiskAverse (shiftDomain_convex hS u v)
  · intro x hx y hy hxy
    exact hi hx.1 hy.1 (by linarith)
  · intro x hx y hy hxy
    exact hi hx.2 hy.2 (by linarith)
  · exact hc.comp (continuous_id.add_const u).continuousOn (fun _ hx => hx.1)
  · exact hc.comp (continuous_id.add_const v).continuousOn (fun _ hx => hx.2)

/-- Coefficient comparisons in the entire overlap imply ordering of every shifted premium. -/
theorem shiftPremiumOrder_of_coefficient {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) (u v : ℝ)
    (hA : ∀ x ∈ ShiftDomain S u v,
      AbsoluteRiskAversion U (x + v) ≤ AbsoluteRiskAversion U (x + u)) :
    ShiftPremiumOrder S U u v := by
  have hc : ContinuousOn U S := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  apply (shiftPremiumOrder_iff hS hi hc u v).mpr
  apply moreRiskAverse_of_arrowPratt (shiftDomain_convex hS u v)
  · exact fun x hx => (hU _ hx.1).comp x (contDiffAt_id.add contDiffAt_const)
  · exact fun x hx => (hU _ hx.2).comp x (contDiffAt_id.add contDiffAt_const)
  · exact fun _ hx _ hy h => hi hx.2 hy.2 (by linarith)
  · intro x hx
    rw [deriv_comp_add_const]
    exact hp _ hx.1
  · intro x hx
    rw [deriv_comp_add_const]
    exact hp _ hx.2
  · simpa only [absoluteRiskAversion_shift] using hA

/-- At any two interior wealth levels, ordering the shifted premia orders the coefficients. -/
theorem coefficient_le_of_shiftPremiumOrder {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) {u v : ℝ} (hu : u ∈ interior S) (hv : v ∈ interior S)
    (h : ShiftPremiumOrder S U u v) : AbsoluteRiskAversion U v ≤ AbsoluteRiskAversion U u := by
  have hc : ContinuousOn U S := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  have hn (t : ℝ) (ht : t ∈ interior S) : ∀ᶠ e : ℝ in 𝓝 0, e + t ∈ S := by
    have he : Tendsto (fun e : ℝ => e + t) (𝓝 0) (𝓝 t) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add_const t
    exact he (mem_interior_iff_mem_nhds.mp ht)
  have hx : 0 ∈ interior (ShiftDomain S u v) :=
    mem_interior_iff_mem_nhds.mpr ((hn u hu).and (hn v hv))
  have hcu : ContDiffAt ℝ 2 (fun e : ℝ => U (e + u)) 0 := by
    apply ContDiffAt.comp (g := U) (f := fun e : ℝ => e + u)
    · simpa using hU u (interior_subset hu)
    · fun_prop
  have hcv : ContDiffAt ℝ 2 (fun e : ℝ => U (e + v)) 0 := by
    apply ContDiffAt.comp (g := U) (f := fun e : ℝ => e + v)
    · simpa using hU v (interior_subset hv)
    · fun_prop
  have hVi : StrictMonoOn (fun e : ℝ => U (e + v)) (ShiftDomain S u v) :=
    fun _ ha _ hb hab => hi ha.2 hb.2 (by linarith)
  have hp' (t : ℝ) (ht : t ∈ S) : 0 < deriv (fun e : ℝ => U (e + t)) 0 := by
    simpa [deriv_comp_add_const] using hp t ht
  have he := arrowPratt_le_of_moreRiskAverse_interior hx hVi
    ((shiftPremiumOrder_iff hS hi hc u v).mp h) hcu hcv
      (hp' u (interior_subset hu)) (hp' v (interior_subset hv))
  simpa only [absoluteRiskAversion_shift, zero_add] using he

end Kreps.UtilityForMoney
