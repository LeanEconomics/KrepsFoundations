/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.IntervalArrowPratt
import UtilityForMoney.WealthRiskClassification

/-!
# Wealth comparisons at one-sided endpoints

Kreps I, Proposition 6.12, pp. 130–131. The relative derivative formulation
uses a separate feasible domain for each pair of shifted lotteries. When the
overlap has only one prize, every pair of certainty equivalents there agrees.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Translating the utility and restricting to any admissible nondegenerate overlap preserves
its first within-domain derivative at the translated wealth. -/
theorem derivWithin_wealth_shift {D S : Set ℝ} (hD : UniqueDiffOn ℝ D) (u : ℝ)
    (hm : Set.MapsTo (fun x : ℝ => x + u) D S) {U : ℝ → ℝ} (hd : DifferentiableOn ℝ U S)
    {x : ℝ} (hx : x ∈ D) :
    derivWithin (fun t => U (t + u)) D x = derivWithin U S (x + u) := by
  have h := ((hd (x + u) (hm hx)).hasDerivWithinAt.comp x
    ((hasDerivAt_id' x).add_const u).hasDerivWithinAt hm).derivWithin (hD x hx)
  simpa only [mul_one, Function.comp_def] using h

/-- The coefficient computed within a translated overlap is the coefficient in the original
interval, including all included endpoints. -/
theorem intervalRiskAversion_shift {D S : Set ℝ} (hD : UniqueDiffOn ℝ D)
    (hS : UniqueDiffOn ℝ S) (u : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + u) D S)
    {U : ℝ → ℝ} (hs : ContDiffOn ℝ 2 U S) {x : ℝ} (hx : x ∈ D) :
    IntervalRiskAversion D (fun t => U (t + u)) x = IntervalRiskAversion S U (x + u) := by
  have he : D.EqOn (derivWithin (fun t => U (t + u)) D) (fun t => derivWithin U S (t + u)) :=
    fun _ ht => derivWithin_wealth_shift hD u hm (hs.differentiableOn (by norm_num)) ht
  rw [IntervalRiskAversion, IntervalRiskAversion, derivWithin_congr he (he hx), he hx,
    derivWithin_wealth_shift hD u hm
      ((hs.derivWithin hS (m := 1) (by norm_num)).differentiableOn_one) hx]

/-- On an overlap with more than one prize, the premium comparison tests the original
within-domain coefficients at every shifted wealth. -/
theorem shiftPremiumOrder_iff_within_coefficients {S : Set ℝ} (hS : Convex ℝ S)
    (hI : (interior S).Nonempty) {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) (u v : ℝ) (hO : (interior (ShiftDomain S u v)).Nonempty) :
    ShiftPremiumOrder S U u v ↔ ∀ x ∈ ShiftDomain S u v,
      IntervalRiskAversion S U (x + v) ≤ IntervalRiskAversion S U (x + u) := by
  let D := ShiftDomain S u v
  have hcD : Convex ℝ D := shiftDomain_convex hS u v
  have hD := uniqueDiffOn_convex hcD hO
  have hSD := uniqueDiffOn_convex hS hI
  have hu : Set.MapsTo (fun x : ℝ => x + u) D S := fun _ hx => hx.1
  have hv : Set.MapsTo (fun x : ℝ => x + v) D S := fun _ hx => hx.2
  have hsm (t : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + t) D S) :
      ContDiffOn ℝ 2 (fun x => U (x + t)) D :=
    hU.comp ((contDiff_id.add contDiff_const).contDiffOn) hm
  have hpos (t : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + t) D S) (x : ℝ) (hx : x ∈ D) :
      0 < derivWithin (fun y => U (y + t)) D x := by
    rw [derivWithin_wealth_shift hD t hm (hU.differentiableOn (by norm_num)) hx]
    exact hp _ (hm hx)
  rw [shiftPremiumOrder_iff hS hi hU.continuousOn, proposition_6_8_within hcD hO
    (hsm u hu) (hsm v hv) (fun _ hx _ hy h => hi (hv hx) (hv hy) (by linarith))
    (hpos u hu) (hpos v hv)]
  exact forall_congr' fun x => forall_congr' fun hx => by
    rw [intervalRiskAversion_shift hD hSD v hv hU hx, intervalRiskAversion_shift hD hSD u hu hU hx]

/-- Even with an empty or single-prize overlap, ordering the feasible coefficients orders premia. -/
theorem shiftPremiumOrder_of_within_coefficients {S : Set ℝ} (hS : Convex ℝ S)
    (hI : (interior S).Nonempty) {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) (u v : ℝ)
    (h : ∀ x ∈ ShiftDomain S u v, IntervalRiskAversion S U (x + v) ≤
      IntervalRiskAversion S U (x + u)) : ShiftPremiumOrder S U u v := by
  by_cases ho : (interior (ShiftDomain S u v)).Nonempty
  · exact (shiftPremiumOrder_iff_within_coefficients hS hI hi hU hp u v ho).mpr h
  · have hs := Set.not_nontrivial_iff.mp
        (ho ∘ (shiftDomain_convex hS u v).nontrivial_iff_nonempty_interior.mp)
    intro p x y _ _
    have he : x = y := Subtype.ext (hs x.property y.property)
    rw [he]

/-- When both shifted base wealth levels are interior, zero lies inside their common overlap. -/
theorem zero_mem_interior_shiftDomain {S : Set ℝ} {u v : ℝ} (hu : u ∈ interior S)
    (hv : v ∈ interior S) : 0 ∈ interior (ShiftDomain S u v) := by
  have hn (t : ℝ) (ht : t ∈ interior S) : ∀ᶠ e : ℝ in 𝓝 0, e + t ∈ S := by
    have he : Tendsto (fun e : ℝ => e + t) (𝓝 0) (𝓝 t) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add_const t
    exact he (mem_interior_iff_mem_nhds.mp ht)
  exact mem_interior_iff_mem_nhds.mpr ((hn u hu).and (hn v hv))

/-- **Proposition 6.12 on the original interval:** increasing, decreasing and constant
behavior of all premia corresponds to the same behavior of within-interval absolute curvature. -/
theorem proposition_6_12_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) :
    (NondecreasingRiskAversion S U ↔ MonotoneOn (IntervalRiskAversion S U) S) ∧
    (NonincreasingRiskAversion S U ↔ AntitoneOn (IntervalRiskAversion S U) S) ∧
    (ConstantRiskAversion S U ↔ ∃ k : ℝ, ∀ x ∈ S, IntervalRiskAversion S U x = k) := by
  have hc := intervalRiskAversion_continuousOn (uniqueDiffOn_convex hS hI) hU hp
  have hcompare {u v : ℝ} (hu : u ∈ interior S) (hv : v ∈ interior S)
      (h : ShiftPremiumOrder S U u v) :
      IntervalRiskAversion S U v ≤ IntervalRiskAversion S U u := by
    have hz := zero_mem_interior_shiftDomain hu hv
    simpa only [zero_add] using ((shiftPremiumOrder_iff_within_coefficients hS hI hi hU hp u v
      ⟨0, hz⟩).mp h 0 (interior_subset hz))
  have hinc : NondecreasingRiskAversion S U ↔ MonotoneOn (IntervalRiskAversion S U) S := by
    constructor
    · intro h
      exact monotoneOn_interval_of_interior hS hI hc fun _ hx _ hy hxy => hcompare hy hx (h _ _ hxy)
    · exact fun h u v huv => shiftPremiumOrder_of_within_coefficients hS hI hi hU hp v u
        fun _ hx => h hx.2 hx.1 (by linarith)
  have hdec : NonincreasingRiskAversion S U ↔ AntitoneOn (IntervalRiskAversion S U) S := by
    constructor
    · intro h
      have hm := monotoneOn_interval_of_interior hS hI hc.neg
        (fun _ hx _ hy hxy => neg_le_neg (hcompare hx hy (h _ _ hxy)))
      exact fun _ hx _ hy hxy => neg_le_neg_iff.mp (hm hx hy hxy)
    · exact fun h u v huv => shiftPremiumOrder_of_within_coefficients hS hI hi hU hp u v
        fun _ hx => h hx.1 hx.2 (by linarith)
  refine ⟨hinc, hdec, ?_⟩
  rw [ConstantRiskAversion, hdec, hinc]
  constructor
  · rintro ⟨ha, hm⟩
    obtain ⟨x, hx⟩ := hI
    refine ⟨IntervalRiskAversion S U x, fun y hy => ?_⟩
    rcases le_total x y with h | h
    · exact (ha (interior_subset hx) hy h).antisymm (hm (interior_subset hx) hy h)
    · exact (hm hy (interior_subset hx) h).antisymm (ha hy (interior_subset hx) h)
  · rintro ⟨k, hk⟩
    constructor <;> intro x hx y hy _ <;> rw [hk x hx, hk y hy]

end Kreps.UtilityForMoney
