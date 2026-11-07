/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.AtomicDensityCounterexample

/-!
# Normalizing the two components of the mixed-law example

Kreps I, pp. 97–98. Each member of the example's domain is an actual mixture
of a simple probability and a normalized continuous compact density, including
the endpoints. At zero weight a normalized component can be chosen arbitrarily.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity

attribute [local instance] BorelConvexSpace

/-- Testing a finite mass vector against one gives its total mass. -/
theorem atomicFunctional_one (w : ℝ →₀ ℝ) :
    AtomicFunctional (fun _ => 1) w = w.sum (fun _ t => t) := by
  simp [AtomicFunctional, Finsupp.linearCombination_apply]

/-- Split a finite nonnegative mass vector into total mass times a probability lottery. -/
theorem atomicWeights_normalize (w : ℝ →₀ ℝ) (hw : 0 ≤ w) :
    ∃ q : SimpleLottery ℝ, w = AtomicFunctional (fun _ => 1) w • q.weights := by
  classical
  let a := AtomicFunctional (fun _ => 1) w
  have hs : (∑ x ∈ w.support, w x) = a := (atomicFunctional_one w).symm
  have ha : 0 ≤ a := hs ▸ Finset.sum_nonneg fun i _ => hw i
  by_cases hz : a = 0
  · refine ⟨PureLottery 0, ?_⟩
    change w = a • _
    rw [hz, zero_smul]
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ w.support) => hw i)).mp
      (hs.trans hz)
    ext i
    by_cases hi : i ∈ w.support
    · exact hsum i hi
    · exact Finsupp.notMem_support_iff.mp hi
  · let q : SimpleLottery ℝ := {
      weights := a⁻¹ • w
      nonneg := smul_nonneg (inv_nonneg.mpr ha) hw
      total := by
        rw [← atomicFunctional_one, map_smul, smul_eq_mul]
        exact inv_mul_cancel₀ hz }
    refine ⟨q, ?_⟩
    change w = a • (a⁻¹ • w)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- Normalize a nonnegative compact density, selecting any unit density at zero total mass. -/
theorem compactDensity_normalize {f : ℝ → ℝ} (hc : Continuous f) (hk : HasCompactSupport f)
    (hf : ∀ x, 0 ≤ f x) :
    ∃ v : ℝ → ℝ, Continuous v ∧ HasCompactSupport v ∧ (∀ x, 0 ≤ v x) ∧
      (∫ x, v x = 1) ∧ ∀ x, f x = (∫ t, f t) * v x := by
  let m := ∫ x, f x
  have hm : 0 ≤ m := integral_nonneg hf
  by_cases hz : m = 0
  · have he := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hf)
        (hc.integrable_of_hasCompactSupport (μ := volume) hk)).mp hz
    have hzero : f = 0 := (hc.ae_eq_iff_eq volume continuous_zero).mp he
    refine ⟨ThreeFourBump.normed volume, ThreeFourBump.continuous_normed,
      ThreeFourBump.hasCompactSupport_normed, ThreeFourBump.nonneg_normed,
      ThreeFourBump.integral_normed, ?_⟩
    intro x
    change f x = m * _
    simp [hzero, hz]
  · refine ⟨fun x => m⁻¹ * f x, continuous_const.mul hc,
      hk.mul_left (f := fun _ => m⁻¹), fun x => mul_nonneg (inv_nonneg.mpr hm) (hf x), ?_, ?_⟩
    · rw [integral_const_mul]
      exact inv_mul_cancel₀ hz
    · intro x
      change f x = m * (m⁻¹ * f x)
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- Matching weighted atom vectors and densities imply equality of the actual Borel laws. -/
theorem atomicDensityPresentation_ext {p q : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (hp : AtomicDensityPresentation p w f) (hq : AtomicDensityPresentation q w f) : p = q := by
  apply ProbabilityMeasure.toMeasure_injective
  ext T hT
  rw [← ofReal_measureReal (measure_ne_top (p : Measure ℝ) T),
    ← ofReal_measureReal (measure_ne_top (q : Measure ℝ) T), hp.event T hT, hq.event T hT]

/-- Exactly the laws in the example have the printed mixture of two normalized probabilities. -/
theorem atomicDensityDomain_iff_mixture (p : ProbabilityMeasure ℝ) :
    p ∈ AtomicDensityDomain ↔ ∃ (a : Weight) (q : SimpleLottery ℝ) (f : ℝ → ℝ)
      (hc : Continuous f) (hk : HasCompactSupport f) (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1),
      p = Mix a (AtomicProbability q) (DensityProbability f
        (hc.integrable_of_hasCompactSupport hk) hf hn) := by
  constructor
  · rintro ⟨w, g, h⟩
    let t := AtomicFunctional (fun _ => 1) w
    have ht : 0 ≤ t := by
      change 0 ≤ AtomicFunctional _ w
      rw [atomicFunctional_one]
      exact Finset.sum_nonneg fun i _ => h.atoms_nonneg i
    have hsum : t + (∫ x, g x) = 1 := atomicDensity_normalized h
    have hm : 0 ≤ ∫ x, g x := integral_nonneg h.density_nonneg
    let a : Weight := ⟨t, ht, by linarith⟩
    obtain ⟨q, hq⟩ := atomicWeights_normalize w h.atoms_nonneg
    obtain ⟨f, hc, hk, hf, hn, he⟩ :=
      compactDensity_normalize h.continuous h.compact h.density_nonneg
    refine ⟨a, q, f, hc, hk, hf, hn, atomicDensityPresentation_ext h ?_⟩
    have H := atomicDensity_mix a (atomicProbability_presentation q)
      (densityProbability_presentation f hc hk hf hn)
    have hw : a.val • q.weights + (1 - a.val) • (0 : ℝ →₀ ℝ) = w := by
      simpa only [smul_zero, add_zero] using hq.symm
    have hd : (fun x => a.val * 0 + (1 - a.val) * f x) = g := by
      funext x
      have ht' : 1 - a.val = ∫ t, g t := by change 1 - t = _; linarith
      simpa only [mul_zero, zero_add, ht'] using (he x).symm
    rw [hw, hd] at H
    exact H
  · rintro ⟨a, q, f, hc, hk, hf, hn, rfl⟩
    exact ⟨_, _, atomicDensity_mix a (atomicProbability_presentation q)
      (densityProbability_presentation f hc hk hf hn)⟩

end Kreps.ChoiceUnderUncertainty
