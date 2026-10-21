/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SampledRankExtension
import PreferenceProperties.WeightedUtilitySemicontinuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Sequences

/-!
# The continuous extension and finite limits of the recursive scale

Kreps I, Problem 2.14(f)-(g). Complete precisely the assigned midpoint scale by
lower cuts. Its dense numerical range gives continuity. Every convergent sequence
of sampled points consequently has a finite limit, with extended-real limsup and
liminf equal to that real number. All such sequences give the same value.

The final wrapper constructs its initial, possibly discontinuous representation
by the countable weighted-sum method. It does not invoke the separate general
continuous-representation theorem.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

variable {X : Type*}

/-- The extension of the exact recursive assignment to the full preference domain. -/
noncomputable def RecursiveUtility (v : X → ℝ) (q : ℕ → X) : X → ℝ :=
  SampleRankExtension v q (RecursiveRank (v ∘ q))

/-- The extension retains every value assigned by the recursion. -/
theorem recursiveUtility_at_sample {v : X → ℝ} {q : ℕ → X}
    (hb : SampleBrackets v q) (n : ℕ) :
    RecursiveUtility v q (q n) = RecursiveRank (v ∘ q) n :=
  sampleRankExtension_at_sample (recursiveRank_preserving _) hb n

/-- Completing the recursive scale preserves every preference comparison. -/
theorem recursiveUtility_represents {r : X → X → Prop} {v : X → ℝ} {q : ℕ → X}
    (hv : Represents v r) (hb : SampleBrackets v q)
    (hs : StrictRankSeparator v (Set.range q)) : Represents (RecursiveUtility v q) r :=
  sampleRankExtension_represents hv (recursiveRank_preserving _) hb hs

/-- Every completed value lies in the smallest interval containing the sampled assigned values. -/
theorem recursiveUtility_mem_interval {v : X → ℝ} {q : ℕ → X}
    (hb : SampleBrackets v q) (x : X) :
    RecursiveUtility v q x ∈ RecursiveRankInterval (v ∘ q) := by
  obtain ⟨i, j, hi, hj⟩ := hb x
  exact ⟨i, j, sampleRankExtension_lower (recursiveRank_preserving _) hb hi,
    sampleRankExtension_upper (recursiveRank_preserving _) hb hj⟩

/-- Dense assigned ranks make the completed representation continuous, including at extrema. -/
theorem recursiveUtility_continuous [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Continuous (RecursiveUtility v q) := by
  apply continuous_of_interval_closure_range (recursiveUtility_represents hv hb hs) hc
  have hd : ∀ i j, (v ∘ q) i < (v ∘ q) j →
      ∃ k, (v ∘ q) i < (v ∘ q) k ∧ (v ∘ q) k < (v ∘ q) j := by
    intro i j hij
    obtain ⟨z, ⟨k, rfl⟩, hik, hkj⟩ := hs (q i) (q j) hij
    exact ⟨k, hik, hkj⟩
  have hrange : Set.range (RecursiveRank (v ∘ q)) ⊆ Set.range (RecursiveUtility v q) := by
    rintro t ⟨n, rfl⟩
    exact ⟨q n, recursiveUtility_at_sample hb n⟩
  intro x y t ht
  apply closure_mono hrange
  apply recursiveRankInterval_subset_closure (v ∘ q) hd
  exact (recursiveRankInterval_ordConnected (v ∘ q)).out
    (recursiveUtility_mem_interval hb x) (recursiveUtility_mem_interval hb y) ht

/-- Along every convergent sampled sequence, the assigned values converge to the extension. -/
theorem recursiveUtility_sample_limit [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x)) :
    Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) := by
  have h := (recursiveUtility_continuous hv hc hb hs).continuousAt.tendsto.comp hseq
  simpa only [Function.comp_def, recursiveUtility_at_sample hb] using h

/-- **Problem 2.14(f):** limsup and liminf agree and are finite, as extended-real limits. -/
theorem problem_2_14f [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x)) :
    ∃ l : ℝ, Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 l) ∧
      Filter.limsup (fun n => (RecursiveRank (v ∘ q) (s n) : EReal)) Filter.atTop =
        (l : EReal) ∧
      Filter.liminf (fun n => (RecursiveRank (v ∘ q) (s n) : EReal)) Filter.atTop =
        (l : EReal) := by
  have h := recursiveUtility_sample_limit hv hc hb hs s hseq
  have he : Filter.Tendsto (fun n => (RecursiveRank (v ∘ q) (s n) : EReal))
      Filter.atTop (𝓝 (RecursiveUtility v q x : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp h
  exact ⟨RecursiveUtility v q x, h, he.limsup_eq, he.liminf_eq⟩

/-- The limiting value is independent of the sampled sequence and its enumeration indices. -/
theorem recursiveUtility_limit_unique [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x))
    {l : ℝ} (hl : Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 l)) :
    l = RecursiveUtility v q x :=
  tendsto_nhds_unique hl (recursiveUtility_sample_limit hv hc hb hs s hseq)

/-- Every point of a dense sampled metric domain is approached by a sampled sequence. -/
theorem dense_sample_sequence [TopologicalSpace X] [FrechetUrysohnSpace X]
    (q : ℕ → X) (hq : DenseRange q) (x : X) :
    ∃ s : ℕ → ℕ, Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) := by
  classical
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (hq x)
  choose s hs using hf
  refine ⟨s, ?_⟩
  have he : q ∘ s = f := funext hs
  rwa [he]

/-- Best and worst preference classes, when attained, are represented in the sample. -/
def SampleContainsPreferenceExtremes (r : X → X → Prop) (q : ℕ → X) : Prop :=
  (∀ x, (∀ y, r y x) → ∃ n, Indifferent r (q n) x) ∧
    (∀ x, (∀ y, r x y) → ∃ n, Indifferent r (q n) x)

/-- The preference formulation of included extremes gives the numerical formulation. -/
theorem sampleContainsExtremes_of_preference {r : X → X → Prop} {v : X → ℝ} {q : ℕ → X}
    (hv : Represents v r) (he : SampleContainsPreferenceExtremes r q) :
    SampleContainsExtremes v q := by
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := he.1 x (fun y => (hv y x).mpr (hx y))
    exact ⟨n, le_antisymm ((hv x (q n)).mp hn.2) ((hv (q n) x).mp hn.1)⟩
  · intro x hx
    obtain ⟨n, hn⟩ := he.2 x (fun y => (hv x y).mpr (hx y))
    exact ⟨n, le_antisymm ((hv x (q n)).mp hn.2) ((hv (q n) x).mp hn.1)⟩

/-- **Problem 2.14(g):** the sequence limits define a continuous representation. -/
theorem problem_2_14g [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Represents (RecursiveUtility v q) r ∧ Continuous (RecursiveUtility v q) ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) →
        Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) :=
  ⟨recursiveUtility_represents hv hb hs, recursiveUtility_continuous hv hc hb hs,
    fun _ s hseq => recursiveUtility_sample_limit hv hc hb hs s hseq⟩

/-- Parts (d)-(g) need only continuous rational preference and the book's augmented dense sample. -/
theorem problem_2_14_recursive_completion [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} (hr : Rational r) (hc : ContinuousPreference r)
    (q : ℕ → X) (hq : DenseRange q) (he : SampleContainsPreferenceExtremes r q) :
    let v := SampledWeightedUtility r q DyadicWeight
    Represents v r ∧ Represents (RecursiveUtility v q) r ∧ Continuous (RecursiveUtility v q) ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) →
        Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) := by
  let v := SampledWeightedUtility r q DyadicWeight
  have hv : Represents v r := sampledWeightedUtility_represents q dyadicWeight_pos
    dyadicWeight_summable hr (dense_orderSeparating hr hc hq)
  have hs := dense_strictRankSeparator hr hc hv hq
  have hb := sampleBrackets_of_extremes hs (sampleContainsExtremes_of_preference hv he)
  exact ⟨hv, problem_2_14g hv hc hb hs⟩

end Kreps.PreferenceProperties
