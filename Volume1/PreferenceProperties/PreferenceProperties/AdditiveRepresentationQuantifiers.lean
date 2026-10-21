/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.PrimitiveAdditiveExistence
import PreferenceProperties.RepresentationQuantifiers

/-!
# The additive existence entry in Table 2.1

Kreps I, Problem 2.1 and Table 2.1, p. 45. With continuity and three nontrivial
blocks, strong separability has the indicated `some` additive representation.
The forward implication uses the fully constructed Proposition 2.14 theorem;
the backward implication uses cancellation of unchanged additive contributions.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
  [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
  [TopologicalSpace.SeparableSpace (∀ i, B i)]
  {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- Table 2.1, strong separability: `some` additive representation under the book's hypotheses. -/
theorem table_additive (hr : Rational r) (hc : ContinuousPreference r)
    (hthree : ThreeNontrivialBlocks r) :
    StronglySeparable r ↔ SomeRepresentation r AdditiveForm := by
  constructor
  · intro hs
    obtain ⟨w, _, hw⟩ := proposition_2_14_exists hr hc hs hthree
    exact ⟨AdditiveUtility w, hw, w, rfl⟩
  · exact table_additive_converse

/-- Continuity and strong separability admit a continuous additive representation. -/
theorem table_continuous_additive (hr : Rational r) (hthree : ThreeNontrivialBlocks r) :
    (ContinuousPreference r ∧ StronglySeparable r) ↔
      SomeRepresentation r (fun u => Continuous u ∧ AdditiveForm u) := by
  constructor
  · rintro ⟨hc, hs⟩
    obtain ⟨w, hwc, hwr⟩ := proposition_2_14_exists hr hc hs hthree
    exact ⟨AdditiveUtility w, hwr, additiveUtility_continuous hwc, w, rfl⟩
  · rintro ⟨u, hu, huc, w, rfl⟩
    exact ⟨proposition_2_9_forward hu huc, proposition_2_14_additive hu⟩

end Kreps.PreferenceProperties
