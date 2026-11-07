/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.AtomicDensityLaws
import ChoiceUnderUncertainty.AffineUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A mixture-affine utility with no expected prize utility

Kreps I, pp. 97–98. Purely atomic laws have their ordinary monetary expectation.
Purely continuous laws have value one. The example compares two dollars for
sure with a continuous probability supported on the entire interval [3,4].
Finite lotteries force any proposed prize index to be positive affine in money.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped ENNReal

/-- Every simple lottery is a member of the example's domain with zero continuous density. -/
theorem atomicProbability_presentation (q : SimpleLottery ℝ) :
    AtomicDensityPresentation (AtomicProbability q) q.weights (fun _ => 0) := by
  refine ⟨q.nonneg, continuous_const, ?_, fun _ => le_rfl, ?_⟩
  · simp [HasCompactSupport]
  · intro T hT
    have hd (x : ℝ) : (diracProba x : Measure ℝ).real T = T.indicator (fun _ => 1) x := by
      classical
      by_cases hx : x ∈ T <;> simp [diracProba, measureReal_def, Measure.dirac_apply' _ hT, hx]
    rw [AtomicProbability, measureCombination_event, iConvexComb_eq_sum]
    simp only [hd, integral_zero, add_zero, AtomicFunctional, Finsupp.linearCombination_apply]

/-- Embed a finite monetary roulette in the actual space of Borel probability laws. -/
noncomputable def AtomicLaw (q : SimpleLottery ℝ) : AtomicDensityDomain :=
  ⟨AtomicProbability q, q.weights, fun _ => 0, atomicProbability_presentation q⟩

/-- On the purely atomic slice the printed index is the expected monetary payoff. -/
theorem atomicDensityIndex_atomic (q : SimpleLottery ℝ) :
    AtomicDensityIndex (AtomicLaw q) = ExpectedUtility id q := by
  have h : AtomicDensityPresentation (AtomicLaw q).val ((1 : ℝ) • q.weights) (fun _ => 0) := by
    simpa [AtomicLaw] using atomicProbability_presentation q
  simpa using atomicDensityIndex_scaled (AtomicLaw q) q 1 h

/-- Integration against a discrete law is finite expectation even for unbounded prize utility. -/
theorem integral_atomicLaw (q : SimpleLottery ℝ) (U : ℝ → ℝ) :
    ∫ x, U x ∂((AtomicLaw q).val : Measure ℝ) = ExpectedUtility U q := by
  change (∫ x, U x ∂(∑ i ∈ q.weights.support,
    ENNReal.ofReal (q.weights i) • (diracProba i : Measure ℝ))) = _
  rw [integral_finsetSum_measure]
  · simp [ExpectedUtility, Finsupp.sum, integral_smul_measure, diracProba,
      ENNReal.toReal_ofReal (q.nonneg _)]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The Borel probability with the supplied nonnegative unit-integral density. -/
noncomputable def DensityProbability (f : ℝ → ℝ) (hi : Integrable f volume)
    (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1) : ProbabilityMeasure ℝ := by
  refine ⟨volume.withDensity (fun x => ENNReal.ofReal (f x)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf), hn, ENNReal.ofReal_one]

/-- The probability with this compact continuous density has no atomic component. -/
theorem densityProbability_presentation (f : ℝ → ℝ) (hc : Continuous f)
    (hk : HasCompactSupport f) (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1) :
    AtomicDensityPresentation
      (DensityProbability f (hc.integrable_of_hasCompactSupport hk) hf hn) 0 f := by
  refine ⟨le_rfl, hc, hk, hf, ?_⟩
  intro T hT
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))).real T = _
  rw [measureReal_def, withDensity_apply _ hT,
    ← ofReal_integral_eq_lintegral_ofReal
      (hc.integrable_of_hasCompactSupport (μ := volume) hk).integrableOn (Eventually.of_forall hf),
    ENNReal.toReal_ofReal (integral_nonneg hf), map_zero, zero_add]

/-- A smooth bump whose support closure is exactly the literal interval [3,4]. -/
noncomputable def ThreeFourBump : ContDiffBump (7 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalized compact density in the comparison is supported precisely on [3,4]. -/
theorem threeFour_support : tsupport (ThreeFourBump.normed volume) = Set.Icc 3 4 := by
  rw [ThreeFourBump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  norm_num [ThreeFourBump]

/-- The continuous-density probability competing with the sure two dollars. -/
noncomputable def ThreeFourLaw : AtomicDensityDomain :=
  ⟨DensityProbability (ThreeFourBump.normed volume) ThreeFourBump.integrable_normed
    ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed,
    0, ThreeFourBump.normed volume, densityProbability_presentation _
      ThreeFourBump.continuous_normed ThreeFourBump.hasCompactSupport_normed
      ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed⟩

/-- All prizes paid by the continuous law lie almost surely between three and four dollars. -/
theorem threeFourLaw_range : ∀ᵐ x ∂(ThreeFourLaw.val : Measure ℝ), x ∈ Set.Icc 3 4 := by
  apply (ae_withDensity_iff ThreeFourBump.continuous_normed.measurable.ennreal_ofReal).mpr
  apply Eventually.of_forall
  intro x hx
  rw [← threeFour_support]
  apply subset_tsupport _
  intro h
  exact hx (by simp [h])

/-- The source index assigns the continuous law one and ranks two dollars for sure above it. -/
theorem atomicDensity_literal_values : AtomicDensityIndex ThreeFourLaw = 1 ∧
    AtomicDensityIndex (AtomicLaw (PureLottery 2)) = 2 := by
  constructor
  · rw [atomicDensityIndex_eq ThreeFourLaw (densityProbability_presentation _
      ThreeFourBump.continuous_normed ThreeFourBump.hasCompactSupport_normed
      ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed), map_zero, zero_add]
  · rw [atomicDensityIndex_atomic, expectedUtility_pure]
    rfl

/-- The mixture-axiom preferences on this domain have no expected prize utility. -/
theorem atomicDensity_no_expectedUtility : ¬∃ U : ℝ → ℝ,
    Represents (fun p : AtomicDensityDomain => ∫ x, U x ∂(p.val : Measure ℝ))
      (UtilityPref AtomicDensityIndex) := by
  rintro ⟨U, hU⟩
  have hfinite : Represents (ExpectedUtility U) (UtilityPref (ExpectedUtility id)) := by
    intro p q
    have he := hU (AtomicLaw p) (AtomicLaw q)
    simpa only [UtilityPref, atomicDensityIndex_atomic, integral_atomicLaw] using he
  obtain ⟨a, ha, b, hab⟩ := proposition_5_3_unique
    (r := UtilityPref (ExpectedUtility id)) (U := id) (fun _ _ => Iff.rfl) hfinite
  have heU : U = fun x => a * x + b := funext hab
  have hint : Integrable U (ThreeFourLaw.val : Measure ℝ) := by
    rw [heU]
    apply Integrable.of_bound (by fun_prop) (4 * a + |b|)
    filter_upwards [threeFourLaw_range] with x hx
    rw [Real.norm_eq_abs]
    calc
      |a * x + b| ≤ |a * x| + |b| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (mul_nonneg ha.le (by linarith [hx.1]))]; nlinarith [hx.2]
  have hmin : a * 3 + b ≤ ∫ x, U x ∂(ThreeFourLaw.val : Measure ℝ) := by
    have hle : ∀ᵐ x ∂(ThreeFourLaw.val : Measure ℝ), a * 3 + b ≤ U x := by
      filter_upwards [threeFourLaw_range] with x hx
      rw [hab x]
      change a * 3 + b ≤ a * x + b
      exact add_le_add_left (mul_le_mul_of_nonneg_left hx.1 ha.le) _
    simpa using integral_mono_ae (integrable_const _) hint hle
  obtain ⟨hd, hs⟩ := atomicDensity_literal_values
  have h := (hU (AtomicLaw (PureLottery 2)) ThreeFourLaw).mp
    (show AtomicDensityIndex ThreeFourLaw ≤ AtomicDensityIndex (AtomicLaw (PureLottery 2)) by
      rw [hd, hs]; norm_num)
  dsimp only at h
  rw [integral_atomicLaw, expectedUtility_pure, hab 2] at h
  change _ ≤ a * 2 + b at h
  linarith

end Kreps.ChoiceUnderUncertainty
