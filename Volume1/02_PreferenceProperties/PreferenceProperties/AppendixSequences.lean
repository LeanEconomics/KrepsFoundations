/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixMetricTopology
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Appendix 2: sequences, accumulation and compactness

Definitions A2.6 and A2.9–A2.13, Propositions A2.7–A2.8 and A2.12, and
Corollary A2.14, pp. 445–447. Sequence indices start at zero. Accumulation uses
arbitrarily late visits to neighborhoods, so repeated values are allowed.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- **Definition A2.6:** convergence is eventual closeness for every positive epsilon. -/
theorem definition_A2_6 {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (x : X) :
    Filter.Tendsto u Filter.atTop (𝓝 x) ↔
      ∀ ε > 0, ∃ N, ∀ n > N, dist (u n) x < ε := Metric.tendsto_atTop'

/-- **Proposition A2.7:** openness means eventual membership for convergent sequences. -/
theorem proposition_A2_7 {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∀ u : ℕ → X, Filter.Tendsto u Filter.atTop (𝓝 x) →
      ∃ N, ∀ n ≥ N, u n ∈ S := by
  constructor
  · intro hS x hx u hu
    exact Filter.eventually_atTop.mp (hu.eventually (hS.mem_nhds hx))
  · intro h
    apply isClosed_compl_iff.mp
    apply IsSeqClosed.isClosed
    intro u x hu hlim hx
    obtain ⟨N, hN⟩ := h x hx u hlim
    exact hu N (hN N le_rfl)

/-- **Proposition A2.8:** a set is closed exactly when it contains all its sequential limits. -/
theorem proposition_A2_8 {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsClosed S ↔ ∀ u : ℕ → X, ∀ x, (∀ n, u n ∈ S) →
      Filter.Tendsto u Filter.atTop (𝓝 x) → x ∈ S := by
  constructor
  · intro h u x hu hlim
    exact h.mem_of_tendsto hlim (Filter.Eventually.of_forall hu)
  · intro h
    exact IsSeqClosed.isClosed (fun u x hu hlim => h u x hu hlim)

/-- **Definition A2.9:** accumulation means returning arbitrarily late to every neighborhood. -/
theorem definition_A2_9 {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔
      ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, dist (u n) x < ε := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [Filter.frequently_atTop, Metric.mem_ball]

/-- The printed definition uses a strictly later index, giving the same accumulation criterion. -/
theorem appendix2_accumulation_strict_index {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔
      ∀ ε > 0, ∀ N : ℕ, ∃ n > N, dist (u n) x < ε := by
  rw [definition_A2_9]
  constructor
  · intro h ε hε N
    obtain ⟨n, hn, hx⟩ := h ε hε (N + 1)
    exact ⟨n, by omega, hx⟩
  · intro h ε hε N
    obtain ⟨n, hn, hx⟩ := h ε hε N
    exact ⟨n, hn.le, hx⟩

/-- **Definition A2.10** and its exercise: accumulation means a convergent subsequence exists. -/
theorem appendix2_accumulation_subsequence {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  constructor
  · exact MapClusterPt.tendsto_subseq
  · rintro ⟨φ, hφ, hlim⟩
    exact MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt

/-- The sequential description of closure on p. 446, allowing constant sequences. -/
theorem appendix2_closure_sequence {X : Type*} [PseudoMetricSpace X] (S : Set X) (x : X) :
    x ∈ closure S ↔ ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      Filter.Tendsto u Filter.atTop (𝓝 x) := mem_closure_iff_seq_limit

/-- The book's set-accumulation convention includes every point of the set itself. -/
theorem appendix2_set_accumulation_self {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {x : X} (hx : x ∈ S) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ MapClusterPt x Filter.atTop u :=
  ⟨fun _ => x, fun _ => hx, tendsto_const_nhds.mapClusterPt⟩

/-- **Definition A2.11:** boundedness means a strict uniform bound on norms. -/
theorem definition_A2_11 {E : Type*} [NormedAddCommGroup E] (S : Set E) :
    Bornology.IsBounded S ↔ ∃ M > 0, ∀ x ∈ S, ‖x‖ < M := by
  constructor
  · intro h
    obtain ⟨M, hM, hbound⟩ := h.exists_pos_norm_le
    refine ⟨M + 1, by linarith, fun x hx => ?_⟩
    have hb := hbound x hx
    linarith
  · rintro ⟨M, _, hbound⟩
    exact isBounded_iff_forall_norm_le.mpr ⟨M, fun x hx => (hbound x hx).le⟩

/-- **Proposition A2.12:** a bounded Euclidean sequence has an accumulation point. -/
theorem proposition_A2_12 {k : ℕ} (u : ℕ → CommodityEuclidean k)
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ x ∈ closure (Set.range u), MapClusterPt x Filter.atTop u := by
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hu.isCompact_closure.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨x, hx, (appendix2_accumulation_subsequence u x).mpr ⟨φ, hφ, hlim⟩⟩

/-- The Cauchy criterion stated before Definition A2.13. -/
theorem appendix2_cauchy_criterion {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

/-- Euclidean space is complete: every Cauchy sequence has a finite Euclidean limit. -/
theorem appendix2_euclidean_complete {k : ℕ} (u : ℕ → CommodityEuclidean k)
    (hu : CauchySeq u) : ∃ x, Filter.Tendsto u Filter.atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

/-- **Definition A2.13:** Euclidean compactness is equivalent to closedness and boundedness. -/
theorem definition_A2_13 {k : ℕ} (S : Set (CommodityEuclidean k)) :
    IsCompact S ↔ IsClosed S ∧ Bornology.IsBounded S := Metric.isCompact_iff_isClosed_bounded

/-- **Corollary A2.14:** a compact sequence has accumulation points, all inside its compact set. -/
theorem corollary_A2_14 {X : Type*} [MetricSpace X] {S : Set X} (hS : IsCompact S)
    (u : ℕ → X) (hu : ∀ n, u n ∈ S) :
    (∃ x, MapClusterPt x Filter.atTop u) ∧
      ∀ x, MapClusterPt x Filter.atTop u → x ∈ S := by
  obtain ⟨x, _, φ, hφ, hlim⟩ := hS.tendsto_subseq hu
  refine ⟨⟨x, (appendix2_accumulation_subsequence u x).mpr ⟨φ, hφ, hlim⟩⟩, ?_⟩
  intro y hy
  exact hS.isClosed.mem_of_mapClusterPt hy (Filter.Eventually.of_forall hu)

/-- The finite-set compactness remark on p. 447. -/
theorem appendix2_finite_compact {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : S.Finite) : IsCompact S := hS.isCompact

/-- The open-cover characterization discussed after Corollary A2.14. -/
theorem appendix2_compact_open_cover {X : Type} [TopologicalSpace X] (S : Set X) :
    IsCompact S ↔ ∀ {ι : Type} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      S ⊆ ⋃ i, U i → ∃ F : Finset ι, S ⊆ ⋃ i ∈ F, U i :=
  isCompact_iff_finite_subcover

end Kreps.PreferenceProperties
