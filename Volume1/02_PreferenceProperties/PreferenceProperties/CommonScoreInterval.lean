/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommonScoreRestriction

/-!
# A common interval for three nontrivial score blocks

The original preference hypotheses supply an interior reference bundle and
an open numerical interval shared by the three selected block-score ranges.
The scalar restriction has normalized axes on precisely that common scale.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- Three nontrivial blocks admit a common open interval around one reference utility. -/
theorem exists_common_baseline_score_interval [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) (i j l : I)
    (hi : NontrivialBlock r i) (hj : NontrivialBlock r j) (hl : NontrivialBlock r l) :
    ∃ (t : ∀ i, B i) (L R : ℝ), u t ∈ Set.Ioo L R ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t i) ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t j) ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t l) := by
  obtain ⟨t, ht⟩ := exists_interior_baseline_scores hr hu hs hc z
  have hni := mem_interior_iff_mem_nhds.mp (ht i hi)
  have hnj := mem_interior_iff_mem_nhds.mp (ht j hj)
  have hnl := mem_interior_iff_mem_nhds.mp (ht l hl)
  obtain ⟨L, R, hLR, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hni (Filter.inter_mem hnj hnl))
  exact ⟨t, L, R, hLR, fun x hx => (hsub hx).1,
    fun x hx => (hsub hx).2.1, fun x hx => (hsub hx).2.2⟩

/-- The original scalar-score construction supplies normalized common axes. -/
theorem scoreAggregator_commonThree_axes [Finite I] (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ Set.range (BaselineScores u z i))
    (hj : J ⊆ Set.range (BaselineScores u z j))
    (hl : J ⊆ Set.range (BaselineScores u z l)) (e : J) (he : e.val = u z) :
    NormalizedThreeAxes
      (CommonThreeScoreUtility (ScoreAggregator u z) (BlockScores (BaselineScores u z) z)
        i j l hi hj hl) Subtype.val e := by
  apply commonThreeScoreUtility_axes _ (scoreAggregator_reference_axis hu hs z)
    hij hil hjl hi hj hl e
  intro k
  exact (baselineScores_reference u z k).trans he.symm

end Kreps.PreferenceProperties
