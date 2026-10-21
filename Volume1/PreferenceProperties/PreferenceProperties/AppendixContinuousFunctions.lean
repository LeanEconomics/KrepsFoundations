/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixSequences
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Appendix 2: continuous functions and the intermediate-value theorem

Definition A2.15, Propositions A2.15–A2.16, Definition A2.17 and Proposition
A2.18, pp. 447–448. Using a subtype as the domain gives precisely relative
continuity. The book's term "simply connected" here means path connected;
its definition also permits the empty set. No assertion about homotopies is made.
-/

namespace Kreps.PreferenceProperties

open scoped Topology NNReal

/-- **Definition A2.15:** the epsilon–delta definition on a relative domain. -/
theorem definition_A2_15 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (S : Set X) (x : X) :
    ContinuousWithinAt f S x ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃y⦄,
      y ∈ S → dist y x < δ → dist (f y) (f x) < ε := Metric.continuousWithinAt_iff

/-- The footnote's uniform continuity condition uses one delta for all base points. -/
theorem appendix2_uniform_continuity {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x y⦄,
      dist x y < δ → dist (f x) (f y) < ε := Metric.uniformContinuous_iff

/-- A uniform Lipschitz bound supplies the footnote's uniform continuity. -/
theorem appendix2_lipschitz_uniform {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    UniformContinuous f := hf.uniformContinuous

/-- **Proposition A2.15(a):** continuity at a point is equivalent to sequential continuity. -/
theorem proposition_A2_15a {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ u : ℕ → X, Filter.Tendsto u Filter.atTop (𝓝 x) →
      Filter.Tendsto (f ∘ u) Filter.atTop (𝓝 (f x)) := tendsto_nhds_iff_seq_tendsto

/-- **Proposition A2.15(b):** open-preimage characterization; subtypes encode relative openness. -/
theorem proposition_A2_15b_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ O, IsOpen O → IsOpen (f ⁻¹' O) := continuous_def

/-- **Proposition A2.15(b):** the equivalent closed-preimage characterization. -/
theorem proposition_A2_15b_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ C, IsClosed C → IsClosed (f ⁻¹' C) :=
  continuous_iff_isClosed

/-- **Proposition A2.16(a):** sums of continuous vector-valued functions are continuous. -/
theorem proposition_A2_16a {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f g : X → CommodityEuclidean k} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := hf.add hg

/-- **Proposition A2.16(b):** products of continuous real functions are continuous. -/
theorem proposition_A2_16b {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := hf.mul hg

/-- **Proposition A2.16(c):** a quotient is continuous where its denominator is nonzero. -/
theorem proposition_A2_16c {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) {x : X} (hx : g x ≠ 0) :
    ContinuousAt (fun y => f y / g y) x := hf.continuousAt.div hg.continuousAt hx

/-- **Proposition A2.16(d):** continuous functions compose. -/
theorem proposition_A2_16d {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := hg.comp hf

/-- **Definition A2.17:** the book's convention is path connectedness, allowing the empty set. -/
theorem definition_A2_17 {X : Type*} [TopologicalSpace X] (S : Set X) :
    (∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y) ↔ S = ∅ ∨ IsPathConnected S := by
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty S with hS | hS
    · exact Or.inl hS
    · exact Or.inr (isPathConnected_iff.mpr ⟨hS, h⟩)
  · rintro (rfl | h)
    · simp
    · exact h.joinedIn

/-- **Proposition A2.18:** every intermediate value is attained along a path-connected domain. -/
theorem proposition_A2_18 {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : ∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y) {f : X → ℝ}
    (hf : ContinuousOn f S) {x y : X} (hx : x ∈ S) (hy : y ∈ S)
    {r : ℝ} (hxr : f x < r) (hry : r < f y) : ∃ z ∈ S, f z = r := by
  have hp : IsPathConnected S := isPathConnected_iff.mpr ⟨⟨x, hx⟩, hS⟩
  exact hp.isConnected.isPreconnected.intermediate_value hx hy hf ⟨hxr.le, hry.le⟩

end Kreps.PreferenceProperties
