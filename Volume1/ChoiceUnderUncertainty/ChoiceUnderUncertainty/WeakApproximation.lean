/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MeasureMixtures
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Approximating Borel probabilities by lotteries of finite support

Kreps I, pp. 98–99. Approximating the identity map pointwise by measurable simple
functions induces a sequence of finite lotteries. The probabilities are the
actual masses of their fibers. Bounded convergence proves weak convergence.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped ENNReal Topology BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

attribute [local instance] BorelConvexSpace

/-- An indexed combination is the convex-space barycenter of its mapped weights. -/
theorem measureCombination_eq_barycenter {I : Type*} (w : SimpleLottery I)
    (f : I → ProbabilityMeasure X) : MeasureCombination w f = (w.map f).sConvexComb := by
  apply probabilityMeasure_ext_real
  intro T
  change _ = (MeasureCombination (w.map f) id : Measure X).real T
  simp only [measureCombination_event, iConvexComb_map, id_eq]

/-- Any binary-affine index respects arbitrary finite barycenters. -/
theorem affineInMix_barycenter {Z : Type*} [ConvexSpace ℝ Z] {u : Z → ℝ}
    (hu : AffineInMix u) (w : SimpleLottery Z) : u w.sConvexComb = ExpectedUtility u w := by
  have hf : AffineInMix (fun p : SimpleLottery Z => u p.sConvexComb) := by
    intro a p q
    change u (Mix a p q).sConvexComb = _
    rw [Mix, sConvexComb_convexCombPair]
    exact hu a p.sConvexComb q.sConvexComb
  simpa only [PureLottery, sConvexComb_single] using affineInMix_eq_expectedUtility hf w

/-- On a discrete probability, an affine index sums its values on the sure prizes. -/
theorem affineInMix_atomicProbability {u : ProbabilityMeasure X → ℝ} (hu : AffineInMix u)
    (p : SimpleLottery X) :
    u (AtomicProbability p) = ExpectedUtility (fun x => u (diracProba x)) p := by
    rw [AtomicProbability, measureCombination_eq_barycenter, affineInMix_barycenter hu,
      expectedUtility_eq_affineMap, expectedUtility_eq_affineMap, StdSimplex.affineMapMk_apply,
      StdSimplex.affineMapMk_apply, iConvexComb_map]

/-- The fiber probabilities on the finite range of a simple function sum to one. -/
noncomputable def ImageWeights (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    SimpleLottery f.range := {
    weights := Finsupp.equivFunOnFinite.symm (fun t => (μ : Measure X).real (f ⁻¹' {t.val}))
    nonneg := fun _ => ENNReal.toReal_nonneg
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change ∑ t : f.range, (μ : Measure X).real (f ⁻¹' {t.val}) = 1
      rw [Finset.sum_coe_sort f.range (fun t => (μ : Measure X).real (f ⁻¹' {t}))]
      simp only [measureReal_def, ← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
        f.sum_range_measure_preimage_singleton, measure_univ, ENNReal.toReal_one] }

/-- The lottery of outputs of a measurable simple function under a probability measure. -/
noncomputable def SimpleImageLottery (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    SimpleLottery X := (ImageWeights μ f).map Subtype.val

/-- The finite image lottery has exactly the pushforward probability law. -/
theorem simpleImageLottery_law [MeasurableSingletonClass X] (μ : ProbabilityMeasure X)
    (f : SimpleFunc X X) : AtomicProbability (SimpleImageLottery μ f) = μ.map f := by
  classical
  let w := ImageWeights μ f
  have he : AtomicProbability (SimpleImageLottery μ f) =
      MeasureCombination w (fun t => diracProba t.val) := by
    apply probabilityMeasure_ext_real
    intro T
    simp only [AtomicProbability, SimpleImageLottery, measureCombination_event, iConvexComb_map]
    rfl
  rw [he]
  apply ProbabilityMeasure.toMeasure_injective
  change w.weights.sum (fun t v => ENNReal.ofReal v • Measure.dirac t.val) =
    (μ : Measure X).map f
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ t : f.range, ENNReal.ofReal ((μ : Measure X).real (f ⁻¹' {t.val})) •
    Measure.dirac t.val = _
  simp only [ofReal_measureReal (measure_ne_top _ _)]
  rw [Finset.sum_coe_sort f.range (fun t => (μ : Measure X) (f ⁻¹' {t}) • Measure.dirac t)]
  exact ((Measure.ae_mem_finset_iff_map_eq_sum_dirac f.aemeasurable).mp
    (Eventually.of_forall f.mem_range_self)).symm

/-- Every Borel law on a second-countable metric prize space is a weak limit of simple lotteries. -/
theorem exists_simpleLotteries_tendsto [PseudoMetricSpace X]
    [SecondCountableTopology X] [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (μ : ProbabilityMeasure X) : ∃ p : ℕ → SimpleLottery X,
      Tendsto (fun n => AtomicProbability (p n)) atTop (𝓝 μ) := by
  have hf : StronglyMeasurable (id : X → X) := continuous_id.stronglyMeasurable
  refine ⟨fun n => SimpleImageLottery μ (hf.approx n), ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [simpleImageLottery_law, ProbabilityMeasure.toMeasure_map]
  simp_rw [integral_map (SimpleFunc.aemeasurable _) g.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
  · exact fun n => (g.continuous.measurable.comp (hf.approx n).measurable).aestronglyMeasurable
  · exact integrable_const _
  · exact fun n => Eventually.of_forall (fun x => g.norm_coe_le_norm (hf.approx n x))
  · exact Eventually.of_forall fun x => g.continuous.continuousAt.tendsto.comp (hf.tendsto_approx x)

end Kreps.ChoiceUnderUncertainty
