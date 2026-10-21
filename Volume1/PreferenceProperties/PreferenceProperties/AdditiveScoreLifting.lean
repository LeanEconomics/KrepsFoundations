/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.IntervalScoreRepresentation
import PreferenceProperties.ActiveCoordinateReduction

/-!
# Lifting additive scalar scores to the original commodity blocks

Nontrivial original blocks have nondegenerate baseline score ranges. Continuous
additive functions on those ranges compose with the baseline scores to give
continuous additive functions on the original blocks.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- A nontrivial block has at least two distinct scores at any reference bundle. -/
theorem nontrivialBlock_baselineScores_nontrivial (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I) (hi : NontrivialBlock r i) :
    Nontrivial (Set.range (BaselineScores u z i)) := by
  let : Nonempty (∀ i, B i) := ⟨z⟩
  obtain ⟨a, b, hab⟩ := (nontrivialBlock_iff_every_context hs i).mp hi
  have hlt : BaselineScores u z i b < BaselineScores u z i a :=
    (strict_iff_utility_lt hu _ _).mp (hab z)
  refine ⟨⟨⟨BaselineScores u z i b, b, rfl⟩, ⟨BaselineScores u z i a, a, rfl⟩, ?_⟩⟩
  intro he
  exact hlt.ne (congrArg Subtype.val he)

/-- The book's three nontrivial blocks remain three distinct nondegenerate score factors. -/
theorem threeNontrivialBlocks_baselineScores (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (h : ThreeNontrivialBlocks r) :
    ∃ i j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (Set.range (BaselineScores u z i)) ∧
      Nontrivial (Set.range (BaselineScores u z j)) ∧
      Nontrivial (Set.range (BaselineScores u z l)) := by
  obtain ⟨i, j, l, hij, hil, hjl, hi, hj, hl⟩ := h
  exact ⟨i, j, l, hij, hil, hjl,
    nontrivialBlock_baselineScores_nontrivial hu hs z i hi,
    nontrivialBlock_baselineScores_nontrivial hu hs z j hj,
    nontrivialBlock_baselineScores_nontrivial hu hs z l hl⟩

/-- Compose each cardinal score function with its original block's baseline score. -/
def ScoreLiftedCoordinate (z : ∀ i, B i)
    (w : ∀ i, Set.range (BaselineScores u z i) → ℝ) (i : I) (a : B i) : ℝ :=
  w i ⟨BaselineScores u z i a, a, rfl⟩

/-- Continuous cardinal score functions lift to continuous original block functions. -/
theorem scoreLiftedCoordinate_continuous [∀ i, TopologicalSpace (B i)]
    (hc : Continuous u) (z : ∀ i, B i)
    {w : ∀ i, Set.range (BaselineScores u z i) → ℝ}
    (hw : ∀ i, Continuous (w i)) (i : I) :
    Continuous (ScoreLiftedCoordinate z w i) :=
  (hw i).comp ((baselineScores_continuous hc z i).subtype_mk (fun a => ⟨a, rfl⟩))

/-- An additive representation of the exact score aggregator represents the original preference. -/
theorem represents_additive_of_scoreAggregator [Fintype I] (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i)
    {w : ∀ i, Set.range (BaselineScores u z i) → ℝ}
    (hw : Represents (AdditiveUtility w) (UtilityPref (ScoreAggregator u z))) :
    Represents (AdditiveUtility (ScoreLiftedCoordinate z w)) r := by
  intro x y
  rw [hu, scoreAggregator_factors hu hs z x, scoreAggregator_factors hu hs z y]
  exact hw (BlockScores (BaselineScores u z) x) (BlockScores (BaselineScores u z) y)

/-- Continuous additive score functions yield the book's continuous additive block functions. -/
theorem continuous_additive_of_scoreAggregator [Fintype I]
    [∀ i, TopologicalSpace (B i)] (hu : Represents u r) (hs : StronglySeparable r)
    (hc : Continuous u) (z : ∀ i, B i)
    (h : ∃ w : ∀ i, Set.range (BaselineScores u z i) → ℝ,
      (∀ i, Continuous (w i)) ∧
        Represents (AdditiveUtility w) (UtilityPref (ScoreAggregator u z))) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  obtain ⟨w, hwc, hwr⟩ := h
  exact ⟨ScoreLiftedCoordinate z w, scoreLiftedCoordinate_continuous hc z hwc,
    represents_additive_of_scoreAggregator hu hs z hwr⟩

end Kreps.PreferenceProperties
