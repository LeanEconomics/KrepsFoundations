/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ArrowPrattTheorem
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Derivatives on the inverse utility scale

Kreps I, p. 129. The inverse used in the comparison theorem is the actual inverse
of utility on the common prize interval. Near an interior wealth with nonzero
marginal utility, it agrees with the smooth inverse supplied by the inverse
function theorem.
-/

namespace Kreps.UtilityForMoney

open Filter Topology
open scoped ContDiff

/-- The interval inverse has the same smoothness as the utility and the reciprocal derivative
at every interior wealth where marginal utility is nonzero. -/
theorem inverse_utility_regularity {S : Set ℝ} {V : ℝ → ℝ} {x : ℝ} {n : ℕ∞ω}
    (hx : x ∈ interior S) (hi : Set.InjOn V S) (hs : ContDiffAt ℝ n V x) (hn : n ≠ 0)
    (hp : deriv V x ≠ 0) :
    ContDiffAt ℝ n (Function.invFunOn V S) (V x) ∧
      HasDerivAt (Function.invFunOn V S) (deriv V x)⁻¹ (V x) ∧
      (∀ᶠ t in 𝓝 (V x), V (Function.invFunOn V S t) = t) := by
  have hd := hs.hasStrictDerivAt hn
  let g := hd.localInverse V (deriv V x) x hp
  have hge : g (V x) = x := (hd.eventually_left_inverse hp).self_of_nhds
  have hgd : HasDerivAt g (deriv V x)⁻¹ (V x) := (hd.to_localInverse hp).hasDerivAt
  have hgs : ContDiffAt ℝ n g (V x) := hs.to_localInverse (hd.hasDerivAt.hasFDerivAt_equiv hp) hn
  have hg : Tendsto g (𝓝 (V x)) (𝓝 x) := by
    simpa only [hge] using hgd.continuousAt.tendsto
  have hright : ∀ᶠ t in 𝓝 (V x), V (g t) = t := hd.eventually_right_inverse hp
  have he : Function.invFunOn V S =ᶠ[𝓝 (V x)] g := by
    filter_upwards [hg (mem_interior_iff_mem_nhds.mp hx), hright] with t hmem ht
    calc Function.invFunOn V S t = Function.invFunOn V S (V (g t)) := congrArg _ ht.symm
         _ = g t := hi.leftInvOn_invFunOn hmem
  refine ⟨hgs.congr_of_eventuallyEq he, hgd.congr_of_eventuallyEq he, ?_⟩
  filter_upwards [he, hright] with t h₁ h₂
  simpa only [h₁] using h₂

/-- The derivative of the utility transform at an attained interior value is a marginal ratio. -/
theorem utilityTransform_hasDerivAt {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ} (hx : x ∈ interior S)
    (hi : Set.InjOn V S) (hV : ContDiffAt ℝ 1 V x) (hp : deriv V x ≠ 0)
    (hW : DifferentiableAt ℝ W x) :
    HasDerivAt (UtilityTransform S W V) (MarginalRatio W V x) (V x) := by
  have hInv := (inverse_utility_regularity hx hi hV one_ne_zero hp).2.1
  have he := hi.leftInvOn_invFunOn (interior_subset hx)
  have hf : HasDerivAt W (deriv W x) (Function.invFunOn V S (V x)) := by
    rw [he]
    exact hW.hasDerivAt
  change HasDerivAt (W ∘ Function.invFunOn V S) (deriv W x / deriv V x) (V x)
  rw [div_eq_mul_inv]
  exact hf.comp (V x) hInv

/-- The displayed formula in the proof of Proposition 6.8, on the interior of the monetary
interval. Twice continuous differentiability is inherited on the inverse utility scale. -/
theorem utilityTransform_second_derivative {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ} (hx : x ∈ interior S)
    (hi : Set.InjOn V S) (hV : ContDiffAt ℝ 2 V x) (hpV : deriv V x ≠ 0)
    (hW : ContDiffAt ℝ 2 W x) (hpW : deriv W x ≠ 0) :
    ContDiffAt ℝ 2 (UtilityTransform S W V) (V x) ∧
      deriv (deriv (UtilityTransform S W V)) (V x) = deriv W x / (deriv V x) ^ 2 *
        (deriv (deriv W) x / deriv W x - deriv (deriv V) x / deriv V x) := by
  let g := Function.invFunOn V S
  have hxg : g (V x) = x := hi.leftInvOn_invFunOn (interior_subset hx)
  obtain ⟨hgs, hgd, hright⟩ := inverse_utility_regularity hx hi hV (by norm_num) hpV
  have hg : Tendsto g (𝓝 (V x)) (𝓝 x) := by
    have h : Tendsto g (𝓝 (V x)) (𝓝 (g (V x))) := hgd.continuousAt.tendsto
    rwa [hxg] at h
  have hdW := hW.derivWithin (m := 1) (by norm_num)
  have hdV := hV.derivWithin (m := 1) (by norm_num)
  have hev : ∀ᶠ y in 𝓝 x, deriv V y ≠ 0 := hdV.continuousAt.eventually_ne hpV
  have hR := hdW.differentiableAt_one.hasDerivAt.div hdV.differentiableAt_one.hasDerivAt hpV
  have hRg : HasDerivAt (MarginalRatio W V)
      ((deriv (deriv W) x * deriv V x - deriv W x * deriv (deriv V) x) / deriv V x ^ 2)
      (g (V x)) := by rw [hxg]; exact hR
  have hlocal : deriv (UtilityTransform S W V) =ᶠ[𝓝 (V x)] (MarginalRatio W V ∘ g) := by
    filter_upwards [hg (isOpen_interior.mem_nhds hx), hright, hg hev,
      hg (hV.eventually (by norm_num)), hg (hW.eventually (by norm_num))] with y hy hre hpy hVy hWy
    change g y ∈ interior S at hy
    change deriv V (g y) ≠ 0 at hpy
    change ContDiffAt ℝ 2 V (g y) at hVy
    change ContDiffAt ℝ 2 W (g y) at hWy
    have hh := (utilityTransform_hasDerivAt hy hi (hVy.of_le (by norm_num)) hpy
      (hWy.differentiableAt (by norm_num))).deriv
    change V (g y) = y at hre
    rw [hre] at hh
    exact hh
  have hWg : ContDiffAt ℝ 2 W (g (V x)) := by rwa [hxg]
  refine ⟨hWg.comp (V x) hgs, ?_⟩
  rw [hlocal.deriv_eq, (hRg.comp (V x) hgd).deriv]
  field_simp

end Kreps.UtilityForMoney
