/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MeasureMixtures
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The countable lottery and Gaussian example on page 100

For an unbounded-below prize utility, geometrically decreasing probabilities
can give infinite expected loss. This proof constructs distinct prizes and
uses an actual probability law. On Gaussian laws and their finite mixtures,
negative exponential utility is integrable and has a finite expected value.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- Choose distinct prizes below the successive negative powers of two. -/
theorem unbounded_prize_sequence {X : Type*} (U : X → ℝ) (hU : ¬BddBelow (Set.range U)) :
    ∃ x : ℕ → X, Function.Injective x ∧ ∀ n, U (x n) < -(2 : ℝ) ^ (n + 1) := by
  have h (t : ℝ) : ∃ z, U z < t := by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := not_bddBelow_iff.mp hU t
    exact ⟨z, hz⟩
  choose pick hp using h
  let x : ℕ → X := Nat.rec (pick (-2)) (fun n z => pick (min (-(2 : ℝ) ^ (n + 2)) (U z)))
  have hs (n : ℕ) : U (x (n + 1)) < U (x n) :=
    (hp _).trans_le (min_le_right _ _)
  have hi : StrictAnti (fun n => U (x n)) := strictAnti_nat_of_succ_lt hs
  refine ⟨x, fun i j he => hi.injective (congrArg U he), ?_⟩
  intro n
  cases n with
  | zero => simpa [x] using hp (-2)
  | succ n => exact (hp _).trans_le (min_le_left _ _)

/-- The countable branch law gives branch number `n+1` probability `1/2^(n+1)`. -/
noncomputable def HalfGeometric : ProbabilityMeasure ℕ :=
  ⟨geometricMeasure ⟨1 / 2, by constructor <;> norm_num⟩, inferInstance⟩

/-- The source's branch probabilities, including the first mass of one half. -/
theorem halfGeometric_odds (n : ℕ) : (HalfGeometric : Measure ℕ).real {n} =
    1 / (2 : ℝ) ^ (n + 1) := by
  change (geometricMeasure _).real {n} = _
  rw [geometricMeasure_real_singleton (by
    intro he
    have := congrArg Subtype.val he
    norm_num at this)]
  norm_num [pow_succ, div_pow]
  ring

/-- The pushforward lottery on the prizes themselves, on any measurable prize space. -/
noncomputable def GeometricPrizeLaw {X : Type*} [MeasurableSpace X] (x : ℕ → X) :
    ProbabilityMeasure X := ⟨(HalfGeometric : Measure ℕ).map x, inferInstance⟩

/-- No branch weights are merged when the prizes are distinct. -/
theorem geometricPrizeLaw_mass {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x : ℕ → X) (hi : Function.Injective x) (n : ℕ) :
    ((GeometricPrizeLaw x : ProbabilityMeasure X) : Measure X).real {x n} =
      1 / (2 : ℝ) ^ (n + 1) := by
  have he : x ⁻¹' {x n} = {n} := by ext j; exact hi.eq_iff
  change ((HalfGeometric : Measure ℕ).map x).real {x n} = _
  rw [measureReal_def, Measure.map_apply (Measurable.of_discrete) (measurableSet_singleton _), he]
  exact halfGeometric_odds n

/-- On the constructed lottery the positive utility part vanishes and expected loss is infinite. -/
theorem geometric_expected_loss {X : Type*} (U : X → ℝ) (x : ℕ → X)
    (hx : ∀ n, U (x n) < -(2 : ℝ) ^ (n + 1)) :
    (∫⁻ n, ENNReal.ofReal (U (x n)) ∂(HalfGeometric : Measure ℕ)) = 0 ∧
    (∫⁻ n, ENNReal.ofReal (-U (x n)) ∂(HalfGeometric : Measure ℕ)) = ⊤ := by
  have hneg (n : ℕ) : U (x n) ≤ 0 := (hx n).le.trans (neg_nonpos.mpr (by positivity))
  constructor
  · simp [ENNReal.ofReal_eq_zero.mpr (hneg _)]
  · rw [lintegral_countable']
    apply top_unique
    calc
      ⊤ = ∑' _ : ℕ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
        have he : (HalfGeometric : Measure ℕ) {n} =
            ENNReal.ofReal (1 / (2 : ℝ) ^ (n + 1)) := by
          rw [← halfGeometric_odds, ofReal_measureReal (measure_ne_top _ _)]
        rw [he, ← ENNReal.ofReal_mul (neg_nonneg.mpr (hneg n)), ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        linarith [hx n]

/-- The pushforward prize law has the literal odds and extended expected utility minus infinity. -/
theorem unbounded_utility_lottery {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (U : X → ℝ) (hm : Measurable U) (hU : ¬BddBelow (Set.range U)) :
    ∃ (p : ProbabilityMeasure X) (x : ℕ → X), Function.Injective x ∧
      (∀ n, (p : Measure X).real {x n} = 1 / (2 : ℝ) ^ (n + 1)) ∧
      (∫⁻ y, ENNReal.ofReal (U y) ∂(p : Measure X)) = 0 ∧
      (∫⁻ y, ENNReal.ofReal (-U y) ∂(p : Measure X)) = ⊤ := by
  obtain ⟨x, hi, hx⟩ := unbounded_prize_sequence U hU
  refine ⟨GeometricPrizeLaw x, x, hi, geometricPrizeLaw_mass x hi, ?_⟩
  obtain ⟨h₁, h₂⟩ := geometric_expected_loss U x hx
  have hneg : Measurable (fun y => ENNReal.ofReal (-U y)) := by fun_prop
  simpa only [GeometricPrizeLaw, ProbabilityMeasure.coe_mk,
    lintegral_map hm.ennreal_ofReal Measurable.of_discrete,
    lintegral_map hneg Measurable.of_discrete] using And.intro h₁ h₂

/-- The printed Gaussian example has a finite closed-form expectation for every real parameter. -/
theorem exponentialUtility_gaussian (m a : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => -Real.exp (-(a * x))) (gaussianReal m v) ∧
    (∫ x : ℝ, -Real.exp (-(a * x)) ∂gaussianReal m v) =
      -Real.exp (m * (-a) + v * (-a) ^ 2 / 2) := by
  constructor
  · convert (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-a)).neg using 1
    simp [Pi.neg_def, neg_mul]
  · rw [integral_neg]
    congr 1
    simpa only [mgf, neg_mul] using congrFun (mgf_fun_id_gaussianReal (μ := m) (v := v)) (-a)

/-- Finite mixtures of normal returns also have integrable negative exponential utility. -/
theorem exponentialUtility_gaussianMixture {I : Type*} (w : SimpleLottery I) (m : I → ℝ)
    (v : I → ℝ≥0) (a : ℝ) :
    Integrable (fun x : ℝ => -Real.exp (-(a * x)))
      (MeasureCombination w (fun i => ⟨gaussianReal (m i) (v i), inferInstance⟩) : Measure ℝ) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (exponentialUtility_gaussian (m i) a (v i)).1.smul_measure ENNReal.ofReal_ne_top

end Kreps.ChoiceUnderUncertainty
