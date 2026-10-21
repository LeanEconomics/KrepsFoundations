/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RecursiveUtilityLimits

/-!
# Include attained best and worst ranks in the dense sample

Kreps I, Problem 2.14, pp. 48-49. Prepending a worst point when one exists and a
best point when one exists preserves density and covers both possible extreme
classes. If an extreme does not exist, the original first sample point is used.
Thus all four attained/unattained-extrema cases are covered without an assumption
that the numerical range is bounded or that its supremum or infimum is attained.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- A globally worst point when one exists; otherwise use the specified anchor. -/
noncomputable def WorstSamplePoint (r : X → X → Prop) (anchor : X) : X := by
  classical
  exact if h : ∃ x, ∀ y, r y x then h.choose else anchor

/-- A globally best point when one exists; otherwise use the specified anchor. -/
noncomputable def BestSamplePoint (r : X → X → Prop) (anchor : X) : X := by
  classical
  exact if h : ∃ x, ∀ y, r x y then h.choose else anchor

/-- The dense enumeration with possible extreme ranks prepended. -/
noncomputable def AugmentedPreferenceSample (r : X → X → Prop) (q : ℕ → X) : ℕ → X
  | 0 => WorstSamplePoint r (q 0)
  | 1 => BestSamplePoint r (q 0)
  | n + 2 => q n

/-- Every original sample point remains in the augmented enumeration. -/
theorem augmentedPreferenceSample_tail (r : X → X → Prop) (q : ℕ → X) (n : ℕ) :
    AugmentedPreferenceSample r q (n + 2) = q n := rfl

/-- Prepending the extreme ranks preserves density. -/
theorem augmentedPreferenceSample_dense [TopologicalSpace X]
    (r : X → X → Prop) (q : ℕ → X) (hq : DenseRange q) :
    DenseRange (AugmentedPreferenceSample r q) := by
  apply hq.mono
  rintro x ⟨n, rfl⟩
  exact ⟨n + 2, rfl⟩

/-- Every attained best or worst class is represented in the augmented sample. -/
theorem augmentedPreferenceSample_extremes (r : X → X → Prop) (q : ℕ → X) :
    SampleContainsPreferenceExtremes r (AugmentedPreferenceSample r q) := by
  classical
  constructor
  · intro x hx
    have h : ∃ z, ∀ y, r y z := ⟨x, hx⟩
    refine ⟨0, ?_⟩
    change Indifferent r (WorstSamplePoint r (q 0)) x
    rw [WorstSamplePoint, dite_eq_left h]
    exact ⟨hx h.choose, h.choose_spec x⟩
  · intro x hx
    have h : ∃ z, ∀ y, r z y := ⟨x, hx⟩
    refine ⟨1, ?_⟩
    change Indifferent r (BestSamplePoint r (q 0)) x
    rw [BestSamplePoint, dite_eq_left h]
    exact ⟨h.choose_spec x, hx h.choose⟩

/-- Dense samples augmented as in the book bracket every original numerical rank. -/
theorem augmentedPreferenceSample_brackets [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) (q : ℕ → X) (hq : DenseRange q) :
    SampleBrackets v (AugmentedPreferenceSample r q) :=
  sampleBrackets_of_extremes
    (dense_strictRankSeparator hr hc hv (augmentedPreferenceSample_dense r q hq))
    (sampleContainsExtremes_of_preference hv (augmentedPreferenceSample_extremes r q))

/-- The complete recursive proof starts from any dense enumeration. -/
theorem recursive_completion_of_dense_sample [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} (hr : Rational r) (hc : ContinuousPreference r)
    (q : ℕ → X) (hq : DenseRange q) :
    let q' := AugmentedPreferenceSample r q
    let v := SampledWeightedUtility r q' DyadicWeight
    Represents v r ∧ Represents (RecursiveUtility v q') r ∧ Continuous (RecursiveUtility v q') ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q' ∘ s) Filter.atTop (nhds x) →
        Filter.Tendsto (RecursiveRank (v ∘ q') ∘ s) Filter.atTop
          (nhds (RecursiveUtility v q' x)) :=
  problem_2_14_recursive_completion hr hc (AugmentedPreferenceSample r q)
    (augmentedPreferenceSample_dense r q hq) (augmentedPreferenceSample_extremes r q)

/-- Existence of the augmented enumeration requires only a nonempty separable domain. -/
theorem exists_dense_sample_with_extremes [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X] (r : X → X → Prop) :
    ∃ q : ℕ → X, DenseRange q ∧ SampleContainsPreferenceExtremes r q := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq X
  exact ⟨AugmentedPreferenceSample r q, augmentedPreferenceSample_dense r q hq,
    augmentedPreferenceSample_extremes r q⟩

end Kreps.PreferenceProperties
