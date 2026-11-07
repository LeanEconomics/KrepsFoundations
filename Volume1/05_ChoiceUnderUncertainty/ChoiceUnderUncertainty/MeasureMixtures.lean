/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.LotteryEvaluation
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Mixtures of Borel probability measures

Kreps I, Proposition 5.10, pp. 98–100. A finite mixture of probability measures is
an actual measure with total mass one. Evaluation on every measurable event
identifies its convex-space structure. Weak convergence is Mathlib's topology
of convergence of integrals against bounded continuous functions.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity
open scoped ENNReal BoundedContinuousFunction

variable {X I : Type*} [MeasurableSpace X]

/-- A finite convex combination of probability measures, with its unit mass proved. -/
noncomputable def MeasureCombination (w : SimpleLottery I) (f : I → ProbabilityMeasure X) :
    ProbabilityMeasure X :=
  ⟨∑ i ∈ w.weights.support, ENNReal.ofReal (w.weights i) • (f i : Measure X), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => w.nonneg i)]
    change ENNReal.ofReal (w.weights.sum (fun _ v => v)) = 1
    rw [w.total, ENNReal.ofReal_one]⟩⟩

/-- The probability of an event is the weighted average of its component probabilities. -/
theorem measureCombination_event (w : SimpleLottery I) (f : I → ProbabilityMeasure X) (T : Set X) :
    (MeasureCombination w f : Measure X).real T =
      w.iConvexComb (fun i => (f i : Measure X).real T) := by
  rw [measureReal_def, MeasureCombination, ProbabilityMeasure.coe_mk, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (w.nonneg _), iConvexComb_eq_sum,
    Finsupp.sum, smul_eq_mul, measureReal_def]

/-- Event evaluations distinguish probability measures. -/
theorem probabilityMeasure_ext_real {p q : ProbabilityMeasure X}
    (h : ∀ T, (p : Measure X).real T = (q : Measure X).real T) : p = q := by
  apply ProbabilityMeasure.toMeasure_injective
  ext T
  rw [← ofReal_measureReal (measure_ne_top (p : Measure X) T),
    ← ofReal_measureReal (measure_ne_top (q : Measure X) T), h T]

/-- The finite-barycenter structure for Borel probability measures used by Proposition 5.10. -/
@[instance_reducible] noncomputable def BorelConvexSpace (X : Type*) [MeasurableSpace X] :
    ConvexSpace ℝ (ProbabilityMeasure X) := .mk (fun w => MeasureCombination w id)
  (by
    intro p
    apply probabilityMeasure_ext_real
    intro T
    rw [measureCombination_event, iConvexComb_single]
    rfl)
  (by
    intro w
    apply probabilityMeasure_ext_real
    intro T
    simp only [measureCombination_event, id_eq, iConvexComb_map]
    simpa only [id_eq, iConvexComb_id'] using
      iConvexComb_assoc w id (fun p : ProbabilityMeasure X => (p : Measure X).real T))

attribute [local instance] BorelConvexSpace

/-- Mixing Borel measures takes the same real weighted average of every event's probabilities. -/
theorem borelMix_event (a : Weight) (p q : ProbabilityMeasure X) (T : Set X) :
    ((Mix a p q : ProbabilityMeasure X) : Measure X).real T =
      a.val * (p : Measure X).real T + (1 - a.val) * (q : Measure X).real T := by
  unfold Mix convexCombPair
  rw [show ∀ w : SimpleLottery (ProbabilityMeasure X),
    (w.sConvexComb : ProbabilityMeasure X) = MeasureCombination w id from fun _ => rfl]
  rw [measureCombination_event, iConvexComb, StdSimplex.map_duple]
  exact convexCombPair_eq_sum _ _ _ _ _ _ _

/-- The simple lottery regarded as its discrete Borel probability distribution. -/
noncomputable def AtomicProbability (p : SimpleLottery X) : ProbabilityMeasure X :=
  MeasureCombination p diracProba

/-- Bounded continuous test functions integrate linearly over any finite mixture. -/
theorem integral_measureCombination [TopologicalSpace X] [OpensMeasurableSpace X]
    (w : SimpleLottery I) (f : I → ProbabilityMeasure X) (g : X →ᵇ ℝ) :
    ∫ x, g x ∂(MeasureCombination w f : Measure X) =
      w.iConvexComb (fun i => ∫ x, g x ∂(f i : Measure X)) := by
  change (∫ x, g x ∂(∑ i ∈ w.weights.support,
    ENNReal.ofReal (w.weights i) • (f i : Measure X))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (w.nonneg _), smul_eq_mul,
      iConvexComb_eq_sum, Finsupp.sum]
  · intro i _
    exact (g.integrable (f i : Measure X)).smul_measure ENNReal.ofReal_ne_top

/-- The integral of a test function against a simple distribution agrees with finite expectation. -/
theorem integral_atomicProbability [TopologicalSpace X] [OpensMeasurableSpace X]
    (p : SimpleLottery X) (g : X →ᵇ ℝ) :
    ∫ x, g x ∂(AtomicProbability p : Measure X) = ExpectedUtility g p := by
  rw [AtomicProbability, integral_measureCombination]
  simp only [diracProba, ProbabilityMeasure.coe_mk,
    integral_dirac' _ _ g.continuous.stronglyMeasurable, iConvexComb_eq_sum, smul_eq_mul,
    ExpectedUtility]

end Kreps.ChoiceUnderUncertainty
