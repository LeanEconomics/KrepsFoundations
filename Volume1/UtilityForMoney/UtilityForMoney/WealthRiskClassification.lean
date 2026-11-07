/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.WealthShifts

/-!
# Monotone and constant absolute risk aversion

Kreps I, Definition 6.11 and Proposition 6.12, pp. 130–131. The interval
proof treats both possible endpoints and allows singleton overlaps of shifted
domains. The strictly increasing, decreasing and constant cases use the same
acceptance comparison on the overlap.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- A continuous scalar function that is nondecreasing in the interior is nondecreasing
on the entire nondegenerate real interval. -/
theorem monotoneOn_interval_of_interior {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {f : ℝ → ℝ} (hf : ContinuousOn f S) (hm : MonotoneOn f (interior S)) : MonotoneOn f S := by
  have hd (x : ℝ) (hx : x ∈ S) : NeBot (𝓝[interior S] x) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have hright {x y : ℝ} (hx : x ∈ interior S) (hy : y ∈ S) (hxy : x < y) : f x ≤ f y := by
    have := hd y hy
    apply ge_of_tendsto ((hf y hy).mono interior_subset)
    have he : ∀ᶠ t in 𝓝[interior S] y, x < t :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hxy)
    filter_upwards [he, self_mem_nhdsWithin] with t hxt ht
    exact hm hx ht hxt.le
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  have := hd x hx
  apply le_of_tendsto ((hf x hx).mono interior_subset)
  have he : ∀ᶠ t in 𝓝[interior S] x, t < y :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds h)
  filter_upwards [he, self_mem_nhdsWithin] with t hty ht
  exact hright ht hy hty

/-- With smooth utility and nonzero marginal utility, the Arrow–Pratt ratio is continuous. -/
theorem absoluteRiskAversion_continuousOn {S : Set ℝ} {U : ℝ → ℝ}
    (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x) (hp : ∀ x ∈ S, 0 < deriv U x) :
    ContinuousOn (AbsoluteRiskAversion U) S := by
  intro x hx
  have hd := (hU x hx).derivWithin (m := 1) (by norm_num)
  have hdd := hd.derivWithin (m := 0) (by norm_num)
  exact (hdd.continuousAt.neg.div hd.continuousAt (hp x hx).ne').continuousWithinAt

/-- **Definition 6.11:** deterministic increases in wealth weakly decrease every risk premium. -/
def NonincreasingRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, u ≤ v → ShiftPremiumOrder S U u v

/-- **Definition 6.11:** deterministic increases in wealth weakly increase every risk premium. -/
def NondecreasingRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, u ≤ v → ShiftPremiumOrder S U v u

/-- **Definition 6.11:** all feasible deterministic shifts preserve every risk premium. -/
def ConstantRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  NonincreasingRiskAversion S U ∧ NondecreasingRiskAversion S U

/-- **Proposition 6.12:** nondecreasing risk aversion iff the coefficient is nondecreasing. -/
theorem proposition_6_12_nondecreasing {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    NondecreasingRiskAversion S U ↔ MonotoneOn (AbsoluteRiskAversion U) S := by
  constructor
  · intro h
    apply monotoneOn_interval_of_interior hS hI (absoluteRiskAversion_continuousOn hU hp)
    exact fun _ hx _ hy hxy => coefficient_le_of_shiftPremiumOrder hS hi hU hp hy hx (h _ _ hxy)
  · intro h u v huv
    apply shiftPremiumOrder_of_coefficient hS hi hU hp
    exact fun _ hx => h hx.2 hx.1 (by linarith)

/-- **Proposition 6.12:** nonincreasing risk aversion iff the coefficient is nonincreasing. -/
theorem proposition_6_12_nonincreasing {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    NonincreasingRiskAversion S U ↔ AntitoneOn (AbsoluteRiskAversion U) S := by
  constructor
  · intro h
    have hm : MonotoneOn (fun x => -AbsoluteRiskAversion U x) S := by
      apply monotoneOn_interval_of_interior hS hI (absoluteRiskAversion_continuousOn hU hp).neg
      intro x hx y hy hxy
      exact neg_le_neg (coefficient_le_of_shiftPremiumOrder hS hi hU hp hx hy (h _ _ hxy))
    exact fun _ hx _ hy hxy => neg_le_neg_iff.mp (hm hx hy hxy)
  · intro h u v huv
    apply shiftPremiumOrder_of_coefficient hS hi hU hp
    exact fun _ hx => h hx.1 hx.2 (by linarith)

/-- **Proposition 6.12:** shift-invariant premia iff the coefficient has one common value. -/
theorem proposition_6_12_constant {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    ConstantRiskAversion S U ↔ ∃ k : ℝ, ∀ x ∈ S, AbsoluteRiskAversion U x = k := by
  rw [ConstantRiskAversion, proposition_6_12_nonincreasing hS hI hi hU hp,
    proposition_6_12_nondecreasing hS hI hi hU hp]
  constructor
  · rintro ⟨ha, hm⟩
    obtain ⟨x, hx⟩ := hI
    refine ⟨AbsoluteRiskAversion U x, fun y hy => ?_⟩
    rcases le_total x y with h | h
    · exact (ha (interior_subset hx) hy h).antisymm (hm (interior_subset hx) hy h)
    · exact (hm hy (interior_subset hx) h).antisymm (ha hy (interior_subset hx) h)
  · rintro ⟨k, hk⟩
    constructor <;> intro x hx y hy _ <;> rw [hk x hx, hk y hy]

end Kreps.UtilityForMoney
