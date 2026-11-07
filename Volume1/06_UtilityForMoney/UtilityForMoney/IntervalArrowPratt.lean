/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ArrowPrattTheorem

/-!
# Arrow–Pratt comparison with derivatives within the prize interval

Kreps I, Proposition 6.8, p. 129. Every hypothesis below concerns values and
derivatives within the monetary domain. At an included endpoint the relative
derivatives are one-sided. No smooth extension outside the interval is needed.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Absolute curvature using first and second derivatives within the prize interval. -/
noncomputable def IntervalRiskAversion (S : Set ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(derivWithin (derivWithin U S) S x) / derivWithin U S x

/-- The relative coefficient agrees with ordinary wealth risk at every interior point. -/
theorem intervalRiskAversion_eq_of_interior {S : Set ℝ} (U : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ interior S) : IntervalRiskAversion S U x = AbsoluteRiskAversion U x := by
  have he : derivWithin U S =ᶠ[𝓝 x] deriv U := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  rw [IntervalRiskAversion, AbsoluteRiskAversion,
    derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx), he.deriv_eq, he.self_of_nhds]

/-- Relative smoothness makes the coefficient continuous all the way to included endpoints. -/
theorem intervalRiskAversion_continuousOn {S : Set ℝ} (hS : UniqueDiffOn ℝ S) {U : ℝ → ℝ}
    (hU : ContDiffOn ℝ 2 U S) (hp : ∀ x ∈ S, 0 < derivWithin U S x) :
    ContinuousOn (IntervalRiskAversion S U) S := by
  have hd := hU.derivWithin hS (m := 1) (by norm_num)
  exact (hd.continuousOn_derivWithin hS (by norm_num)).neg.div
    (hU.continuousOn_derivWithin hS (by norm_num)) fun x hx => (hp x hx).ne'

/-- Supporting-line comparison from continuous utility and ordered marginal ratios within the
monetary interval. Derivatives are used only inside each nondegenerate secant segment. -/
theorem interval_marginal_support {S : Set ℝ} (hS : Convex ℝ S) {W V DW DV : ℝ → ℝ}
    (hcW : ContinuousOn W S) (hcV : ContinuousOn V S)
    (hdW : ∀ x ∈ interior S, HasDerivAt W (DW x) x)
    (hdV : ∀ x ∈ interior S, HasDerivAt V (DV x) x)
    (hVi : StrictMonoOn V S) (hpV : ∀ x ∈ S, 0 < DV x)
    (hR : AntitoneOn (fun x => DW x / DV x) S) {x z : ℝ} (hx : x ∈ S) (hz : z ∈ S) :
    W z ≤ W x + (DW x / DV x) * (V z - V x) := by
  have key {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      ∃ c ∈ Set.Ioo a b, c ∈ S ∧ W b - W a = (V b - V a) * (DW c / DV c) := by
    have hs := hS.ordConnected.out ha hb
    have ho : Set.Ioo a b ⊆ interior S := isOpen_Ioo.subset_interior_iff.mpr
      (Set.Ioo_subset_Icc_self.trans hs)
    obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope W DW hab (hcW.mono hs)
      (fun t ht => hdW t (ho ht)) V DV (hcV.mono hs) (fun t ht => hdV t (ho ht))
    have hcS := interior_subset (ho hc)
    refine ⟨c, hc, hcS, ?_⟩
    field_simp [(hpV c hcS).ne']
    linarith
  rcases lt_trichotomy x z with h | rfl | h
  · obtain ⟨c, hc, hcs, he⟩ := key hx hz h
    have hh := mul_le_mul_of_nonneg_left (hR hx hcs hc.1.le) (sub_nonneg.mpr (hVi hx hz h).le)
    change (V z - V x) * (DW c / DV c) ≤ (V z - V x) * (DW x / DV x) at hh
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs, he⟩ := key hz hx h
    have hh := mul_le_mul_of_nonneg_left (hR hcs hx hc.2.le) (sub_nonneg.mpr (hVi hz hx h).le)
    change (V x - V z) * (DW x / DV x) ≤ (V x - V z) * (DW c / DV c) at hh
    nlinarith

/-- **Proposition 6.8 on the original interval:** the coefficient inequality at every prize
characterizes the comparison of all simple lotteries, under purely relative smoothness. -/
theorem proposition_6_8_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {W V : ℝ → ℝ} (hW : ContDiffOn ℝ 2 W S) (hV : ContDiffOn ℝ 2 V S)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < derivWithin W S x)
    (hpV : ∀ x ∈ S, 0 < derivWithin V S x) :
    MoreRiskAverse S W V ↔ ∀ x ∈ S, IntervalRiskAversion S V x ≤ IntervalRiskAversion S W x := by
  have hD := uniqueDiffOn_convex hS hI
  have dW := hW.derivWithin hD (m := 1) (by norm_num)
  have dV := hV.derivWithin hD (m := 1) (by norm_num)
  constructor
  · intro h x hx
    have hxcl : x ∈ closure (interior S) := by
      rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
      exact subset_closure hx
    have := mem_closure_iff_nhdsWithin_neBot.mp hxcl
    apply le_of_tendsto_of_tendsto
      ((intervalRiskAversion_continuousOn hD hV hpV x hx).mono interior_subset)
      ((intervalRiskAversion_continuousOn hD hW hpW x hx).mono interior_subset)
    filter_upwards [self_mem_nhdsWithin (a := x) (s := interior S)] with y hy
    have hn := mem_interior_iff_mem_nhds.mp hy
    have hym := interior_subset hy
    rw [intervalRiskAversion_eq_of_interior V hy, intervalRiskAversion_eq_of_interior W hy]
    apply arrowPratt_le_of_moreRiskAverse_interior hy hVi h
      ((hW y hym).contDiffAt hn) ((hV y hym).contDiffAt hn)
    · simpa only [← derivWithin_of_mem_nhds (f := W) hn] using hpW y hym
    · simpa only [← derivWithin_of_mem_nhds (f := V) hn] using hpV y hym
  · intro h
    let R := fun x => derivWithin W S x / derivWithin V S x
    have ha : AntitoneOn R S := by
      have hd (x : ℝ) (hx : x ∈ S) := ((dW.differentiableOn_one x hx).hasDerivWithinAt.div
        (dV.differentiableOn_one x hx).hasDerivWithinAt (hpV x hx).ne')
      apply antitoneOn_of_hasDerivWithinAt_nonpos hS
        (dW.continuousOn.div dV.continuousOn (fun x hx => (hpV x hx).ne'))
        (fun x hx => (hd x (interior_subset hx)).mono interior_subset)
      intro x hx
      have hxs := interior_subset hx
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have he := (div_le_div_iff₀ (hpV x hxs) (hpW x hxs)).mp (h x hxs)
      nlinarith
    intro p x hx
    have hpt (z : S) : W z ≤ R x * V z + (W x - R x * V x) := by
      have hh := interval_marginal_support hS hW.continuousOn hV.continuousOn
        (fun y hy => ((hW.differentiableOn (by norm_num) y (interior_subset hy)).hasDerivWithinAt
          |>.hasDerivAt (mem_interior_iff_mem_nhds.mp hy)))
        (fun y hy => ((hV.differentiableOn (by norm_num) y (interior_subset hy)).hasDerivWithinAt
          |>.hasDerivAt (mem_interior_iff_mem_nhds.mp hy)))
        hVi hpV ha x.property z.property
      dsimp [R]
      linarith
    have he : ExpectedUtility (fun z : S => W z) p ≤
        ExpectedUtility (fun z : S => R x * V z + (W x - R x * V x)) p :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (p.nonneg z)
    rw [expectedUtility_affine_payoff] at he
    by_contra! hn
    have hpos : 0 < R x := div_pos (hpW x x.property) (hpV x x.property)
    nlinarith [mul_lt_mul_of_pos_left hn hpos]

end Kreps.UtilityForMoney
