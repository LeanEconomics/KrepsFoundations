/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureRepresentation
import ChoiceUnderUncertainty.WeakUtilityContinuity

/-!
# Expected utility on all Borel probability measures

Kreps I, Proposition 5.10, pp. 98–100. The proof works on second-countable metric
prize spaces with their Borel sets, including finite-dimensional real space and
its nonnegative orthant. Utility on prizes is evaluated at Dirac laws. Weak
continuity and approximation extend its integral representation to every law.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped Topology BoundedContinuousFunction

attribute [local instance] BorelConvexSpace

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSingletonClass X]

/-- An affine weakly continuous index is the expectation of its values on Dirac laws. -/
theorem borel_index_is_integral {u : ProbabilityMeasure X → ℝ} (hc : Continuous u)
    (ha : AffineInMix u) : ∃ U : X →ᵇ ℝ, (∀ x, U x = u (diracProba x)) ∧
      ∀ p : ProbabilityMeasure X, u p = ∫ x, U x ∂(p : Measure X) := by
  obtain ⟨C, hC⟩ := continuous_affine_bounded hc ha
  let U : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => u (diracProba x), hc.comp continuous_diracProba⟩ (C + C) (by
      intro x y
      change |u (diracProba x) - u (diracProba y)| ≤ C + C
      exact (abs_sub _ _).trans (add_le_add (hC _) (hC _)))
  refine ⟨U, fun _ => rfl, fun p => ?_⟩
  obtain ⟨q, hq⟩ := exists_simpleLotteries_tendsto p
  have h₁ := hc.continuousAt.tendsto.comp hq
  have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U).continuousAt
    |>.tendsto.comp hq
  have he (n : ℕ) : u (AtomicProbability (q n)) =
      ∫ x, U x ∂(AtomicProbability (q n) : Measure X) := by
    rw [affineInMix_atomicProbability ha, integral_atomicProbability]
    rfl
  exact tendsto_nhds_unique (h₁.congr (fun n => he n)) h₂

/-- Proposition 5.10. Weak continuity and the mixture axioms characterize bounded continuous EU. -/
theorem proposition_5_10 {r : ProbabilityMeasure X → ProbabilityMeasure X → Prop} :
    MixtureAxioms r ∧ OpenStrictSections r ↔
      ∃ U : X →ᵇ ℝ, Represents (fun p : ProbabilityMeasure X => ∫ x, U x ∂(p : Measure X)) r := by
  constructor
  · rintro ⟨hm, hw⟩
    obtain ⟨u, hr, ha⟩ := proposition_5_4.mp hm
    have hc := (openStrictSections_iff_continuous hr ha).mp hw
    obtain ⟨U, _, he⟩ := borel_index_is_integral hc ha
    exact ⟨U, fun p q => by simpa only [← he p, ← he q] using hr p q⟩
  · rintro ⟨U, hr⟩
    have ha := integral_affineInMix U
    exact ⟨proposition_5_4.mpr ⟨_, hr, ha⟩, (openStrictSections_iff_continuous hr ha).mpr
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U)⟩

/-- The proposition applies to Borel laws on the book's full Euclidean commodity space. -/
theorem proposition_5_10_euclidean (k : ℕ) {r : ProbabilityMeasure (Fin k → ℝ) →
    ProbabilityMeasure (Fin k → ℝ) → Prop} :
    MixtureAxioms r ∧ OpenStrictSections r ↔
      ∃ U : (Fin k → ℝ) →ᵇ ℝ, Represents (fun p : ProbabilityMeasure (Fin k → ℝ) =>
        ∫ x, U x ∂(p : Measure (Fin k → ℝ))) r := proposition_5_10

/-- The proposition also applies on the closed nonnegative orthant, including its boundary. -/
theorem proposition_5_10_orthant (k : ℕ) :
    let X := {x : Fin k → ℝ // 0 ≤ x}
    ∀ r : ProbabilityMeasure X → ProbabilityMeasure X → Prop,
      MixtureAxioms r ∧ OpenStrictSections r ↔
        ∃ U : X →ᵇ ℝ, Represents (fun p : ProbabilityMeasure X => ∫ x, U x ∂(p : Measure X)) r :=
  fun _ => proposition_5_10

end Kreps.ChoiceUnderUncertainty
