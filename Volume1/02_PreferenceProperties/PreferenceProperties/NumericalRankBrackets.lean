/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AugmentedPreferenceSample

/-!
# A countable sequence brackets every numerical rank

Kreps I, Problem 2.14(a). A countable dense sequence in the numerical range is
cofinal below every nonminimal rank and coinitial above every nonmaximal rank.
Include any attained extrema to obtain weak brackets for every point. This uses
only a real-valued representation, with no continuity assumption on that function.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- A dense sample of the numerical range, with extrema included, brackets every rank. -/
theorem sampleBrackets_of_dense_rank_range (v : X → ℝ) (q : ℕ → X)
    (hd : DenseRange (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)))
    (he : SampleContainsExtremes v q) : SampleBrackets v q := by
  intro x
  have hlo : ∃ i, v (q i) ≤ v x := by
    by_cases hy : ∃ y, v y < v x
    · obtain ⟨y, hy⟩ := hy
      have ho : IsOpen {a : Set.range v | a.val < v x} :=
        isOpen_lt continuous_subtype_val continuous_const
      obtain ⟨i, hi⟩ := hd.exists_mem_open ho ⟨⟨v y, Set.mem_range_self y⟩, hy⟩
      exact ⟨i, hi.le⟩
    · obtain ⟨i, hi⟩ := he.1 x (fun y => le_of_not_gt (fun h => hy ⟨y, h⟩))
      exact ⟨i, hi.le⟩
  have hhi : ∃ j, v x ≤ v (q j) := by
    by_cases hy : ∃ y, v x < v y
    · obtain ⟨y, hy⟩ := hy
      have ho : IsOpen {a : Set.range v | v x < a.val} :=
        isOpen_lt continuous_const continuous_subtype_val
      obtain ⟨j, hj⟩ := hd.exists_mem_open ho ⟨⟨v y, Set.mem_range_self y⟩, hy⟩
      exact ⟨j, hj.le⟩
    · obtain ⟨j, hj⟩ := he.2 x (fun y => le_of_not_gt (fun h => hy ⟨y, h⟩))
      exact ⟨j, hj.ge⟩
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  exact ⟨i, j, hi, hj⟩

/-- Every real-valued scale has a countable bracketing sample containing attained extremes. -/
theorem exists_sample_brackets [Nonempty X] (v : X → ℝ) :
    ∃ q : ℕ → X, SampleBrackets v q ∧ SampleContainsExtremes v q := by
  classical
  let : Nonempty (Set.range v) := ⟨⟨v (Classical.arbitrary X), Set.mem_range_self _⟩⟩
  obtain ⟨f, hf⟩ := TopologicalSpace.exists_dense_seq (Set.range v)
  let q : ℕ → X := fun n => (f n).property.choose
  have hq (n : ℕ) : v (q n) = (f n).val := (f n).property.choose_spec
  have hqd : DenseRange (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)) := by
    have heq : (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)) = f := by
      funext n
      exact Subtype.ext (hq n)
    rwa [heq]
  let q' := AugmentedPreferenceSample (UtilityPref v) q
  have hd : DenseRange (fun n => (⟨v (q' n), Set.mem_range_self (q' n)⟩ : Set.range v)) := by
    apply hqd.mono
    rintro a ⟨n, rfl⟩
    exact ⟨n + 2, rfl⟩
  have he : SampleContainsExtremes v q' :=
    sampleContainsExtremes_of_preference (fun _ _ => Iff.rfl)
      (augmentedPreferenceSample_extremes (UtilityPref v) q)
  exact ⟨q', sampleBrackets_of_dense_rank_range v q' hd he, he⟩

/-- In preference language, a countable sequence is both cofinal and coinitial. -/
theorem exists_preference_bracketing_sequence [Nonempty X] {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) :
    ∃ q : ℕ → X, ∀ x, ∃ i j, r (q i) x ∧ r x (q j) := by
  obtain ⟨q, hb, _⟩ := exists_sample_brackets v
  refine ⟨q, fun x => ?_⟩
  obtain ⟨j, i, hj, hi⟩ := hb x
  exact ⟨i, j, (hv (q i) x).mpr hi, (hv x (q j)).mpr hj⟩

end Kreps.PreferenceProperties
