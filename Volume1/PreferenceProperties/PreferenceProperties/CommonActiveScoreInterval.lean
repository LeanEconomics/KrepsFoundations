/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.NormalizedCoordinatePairs
import PreferenceProperties.CommonLocalAdditiveScale

/-!
# A common interval for all active score coordinates

Finite intersection gives one score neighborhood at every specified interior
reference value. Its coordinate embeddings leave inactive coordinates at their
reference values, so singleton score ranges impose no restriction on the interval.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Finitely many active score ranges have a common interval at any common interior value. -/
theorem exists_all_active_score_interval [Finite I] {T : Set I} {c : ℝ}
    (hc : ∀ i ∈ T, c ∈ interior (S i)) :
    ∃ L R, c ∈ Set.Ioo L R ∧ ∀ i ∈ T, Set.Ioo L R ⊆ S i := by
  classical
  have hn : ∀ᶠ x in nhds c, ∀ i ∈ T, x ∈ S i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ T
    · exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp (hc i hi))
        (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  obtain ⟨L, R, hcLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  exact ⟨L, R, hcLR, fun i hi x hx => hLR hx i hi⟩

/-- Embed a common score in each active coordinate and retain all inactive reference scores. -/
noncomputable def CommonActiveScoreEmbedding (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) (i : I) (x : J) : S i := by
  classical
  exact if hi : i ∈ T then ⟨x.val, hJ i hi x.property⟩ else z i

/-- On active coordinates the common embedding is the ordinary set inclusion. -/
theorem commonActiveScoreEmbedding_active (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) {i : I} (hi : i ∈ T) (x : J) :
    CommonActiveScoreEmbedding z T hJ i x = Set.inclusion (hJ i hi) x := by
  simp only [CommonActiveScoreEmbedding, dite_eq_left hi]

/-- On inactive coordinates the common embedding leaves the reference score fixed. -/
theorem commonActiveScoreEmbedding_inactive (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) {i : I} (hi : i ∉ T) (x : J) :
    CommonActiveScoreEmbedding z T hJ i x = z i := by
  simp only [CommonActiveScoreEmbedding, dite_eq_right hi]

/-- The common embedding is continuous in every coordinate. -/
theorem commonActiveScoreEmbedding_continuous (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) (i : I) :
    Continuous (CommonActiveScoreEmbedding z T hJ i) := by
  classical
  by_cases hi : i ∈ T
  · have he : CommonActiveScoreEmbedding z T hJ i = Set.inclusion (hJ i hi) :=
      funext (commonActiveScoreEmbedding_active z T hJ hi)
    rw [he]
    exact continuous_inclusion _
  · have he : CommonActiveScoreEmbedding z T hJ i = fun _ => z i :=
      funext (commonActiveScoreEmbedding_inactive z T hJ hi)
    rw [he]
    exact continuous_const

/-- Numerical axis normalization survives restriction to the common active interval. -/
theorem commonActiveScoreEmbedding_axes [DecidableEq I] {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (hv : ∀ i (q : S i), V (Function.update z i q) = q.val) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) :
    NormalizedCoordinateAxes V z (CommonActiveScoreEmbedding z T hJ) Subtype.val T := by
  intro i hi x
  rw [hv, commonActiveScoreEmbedding_active z T hJ hi]

end Kreps.PreferenceProperties
