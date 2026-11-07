/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.NondegenerateScalarAdditiveExistence
import PreferenceProperties.ActiveScalarUtility
import PreferenceProperties.AdditiveScoreLifting
import PreferenceProperties.GeneralContinuousRepresentation

/-!
# Continuous additive utility from primitive preference assumptions

**Proposition 2.14**, p. 42: continuous strongly separable rational preferences
with at least three nontrivial blocks have continuous additive block utilities.
The blocks may contain indifferent alternatives and inessential blocks. A
continuous ordinal representation is first derived from preference continuity;
its block scores reduce the problem to real intervals. Singleton score factors
are removed before the nondegenerate theorem and restored with zero utilities.
-/

namespace Kreps.PreferenceProperties

/-- Three nondegenerate factors suffice even when other scalar factors are singletons. -/
theorem exists_scalar_additive_of_three_nontrivial {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (S i) ∧ Nontrivial (S j) ∧ Nontrivial (S l)) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  classical
  let : ∀ i : NontrivialScalarIndices S, Nontrivial (S i.val) := fun i => i.property
  apply continuous_additive_of_activeScalar z
  exact exists_nondegenerate_scalar_additive (fun i => hS i.val)
    (activeScalarUtility_stronglySeparable hs z) (activeScalarUtility_strictMono hm z)
    (activeScalarUtility_continuous hc z) (three_nontrivialScalarIndices hthree)

variable {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- A continuous ordinal representation yields additive block utilities by scalar reduction. -/
theorem continuous_additive_of_continuous_represents (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (hthree : ThreeNontrivialBlocks r) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  have hz : Nonempty (∀ i, B i) := by
    obtain ⟨_, _, _, _, _, _, hi, _⟩ := hthree
    obtain ⟨_, _, z, _⟩ := hi
    exact ⟨z⟩
  obtain ⟨z⟩ := hz
  apply continuous_additive_of_scoreAggregator hu hs hc z
  obtain ⟨w, hwc, _, hwr⟩ := exists_scalar_additive_of_three_nontrivial
    (fun i => baselineScores_ordConnected hc z i) (scoreAggregator_stronglySeparable hu hs z)
    (scoreAggregator_strictMono hu hs z) (scoreAggregator_continuous hu hs hc z)
    (BlockScores (BaselineScores u z) z) (threeNontrivialBlocks_baselineScores hu hs z hthree)
  exact ⟨w, hwc, hwr⟩

/-- **Proposition 2.14**, existence, from rationality, continuity and strong separability. -/
theorem proposition_2_14_exists [TopologicalSpace.SeparableSpace (∀ i, B i)]
    (hr : Rational r) (hc : ContinuousPreference r) (hs : StronglySeparable r)
    (hthree : ThreeNontrivialBlocks r) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  obtain ⟨u, hu, huc, _⟩ := continuous_represents_of_continuous_connected hr hc
  exact continuous_additive_of_continuous_represents hu hs huc hthree

end Kreps.PreferenceProperties
