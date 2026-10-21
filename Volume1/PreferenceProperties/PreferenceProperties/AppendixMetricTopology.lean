/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order
import Mathlib.Tactic

/-!
# Appendix 2: Euclidean distance and elementary topology

Definitions A2.1–A2.5 and Proposition A2.4, pp. 441–443. Euclidean space carries
its genuine sum-of-squares norm. Its explicit homeomorphism to the finite product
explains why the chapter can use the product metric for topological arguments.
-/

namespace Kreps.PreferenceProperties

/-- The appendix's finite-dimensional Euclidean space, with its Euclidean norm. -/
abbrev CommodityEuclidean (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- **Definition A2.1:** Euclidean distance is the square root of the sum of squared differences. -/
theorem definition_A2_1 {k : ℕ} (x y : CommodityEuclidean k) :
    dist x y = Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  simpa only [Real.dist_eq, sq_abs] using EuclideanSpace.dist_eq x y

/-- The four metric properties listed immediately after Definition A2.1. -/
theorem euclidean_distance_properties {k : ℕ} (x y z : CommodityEuclidean k) (a : ℝ) :
    0 ≤ dist x y ∧ (dist x y = 0 ↔ x = y) ∧ dist x y = dist y x ∧
      dist (a • x) (a • y) = |a| * dist x y ∧ dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_nonneg, dist_eq_zero, dist_comm x y,
    by simpa only [Real.norm_eq_abs] using dist_smul₀ a x y, dist_triangle x y z⟩

/-- The translation invariance noted alongside Definition A2.1. -/
theorem euclidean_distance_translation {k : ℕ} (x y z : CommodityEuclidean k) :
    dist (x + z) (y + z) = dist x y := dist_add_right x y z

/-- The Euclidean and coordinate-product presentations have the same topology. -/
noncomputable def euclideanProductHomeomorph (k : ℕ) :
    CommodityEuclidean k ≃ₜ (Fin k → ℝ) := PiLp.homeomorph 2 (fun _ => ℝ)

/-- **Definition A2.2:** the epsilon-neighborhood is an open metric ball. -/
theorem definition_A2_2 {k : ℕ} (x : CommodityEuclidean k) (ε : ℝ) :
    {y | dist y x < ε} = Metric.ball x ε := rfl

/-- The exercise in footnote 2: every open ball is open. -/
theorem appendix2_open_ball {X : Type*} [PseudoMetricSpace X] (x : X) (ε : ℝ) :
    IsOpen (Metric.ball x ε) := Metric.isOpen_ball

/-- **Definition A2.3:** every point of an open set has a ball inside the set. -/
theorem definition_A2_3_open {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∃ ε > 0, Metric.ball x ε ⊆ S := Metric.isOpen_iff

/-- **Definition A2.3:** closed sets are precisely the complements of open sets. -/
theorem definition_A2_3_closed {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsClosed S ↔ IsOpen Sᶜ := isOpen_compl_iff.symm

/-- Empty and full spaces are both open and closed, as observed on p. 442. -/
theorem appendix2_empty_univ_clopen {X : Type*} [TopologicalSpace X] :
    IsOpen (∅ : Set X) ∧ IsClosed (∅ : Set X) ∧
      IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) :=
  ⟨isOpen_empty, isClosed_empty, isOpen_univ, isClosed_univ⟩

/-- **Proposition A2.4:** arbitrary unions of open sets are open. -/
theorem proposition_A2_4_open_union {X I : Type*} [TopologicalSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) : IsOpen (⋃ i, U i) := isOpen_iUnion hU

/-- **Proposition A2.4:** finite intersections of open sets are open. -/
theorem proposition_A2_4_open_inter {X I : Type*} [TopologicalSpace X] [Finite I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) : IsOpen (⋂ i, U i) :=
  isOpen_iInter_of_finite hU

/-- **Proposition A2.4:** finite unions of closed sets are closed. -/
theorem proposition_A2_4_closed_union {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) : IsClosed (⋃ i, C i) :=
  isClosed_iUnion_of_finite hC

/-- **Proposition A2.4:** arbitrary intersections of closed sets are closed. -/
theorem proposition_A2_4_closed_inter {X I : Type*} [TopologicalSpace X]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) : IsClosed (⋂ i, C i) :=
  isClosed_iInter hC

/-- The relative-open definition on p. 443, expressed through subtype preimages. -/
theorem appendix2_relative_open {X : Type*} [TopologicalSpace X] (S : Set X) (A : Set S) :
    IsOpen A ↔ ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = A := isOpen_induced_iff

/-- The corresponding relative-closed definition. -/
theorem appendix2_relative_closed {X : Type*} [TopologicalSpace X] (S : Set X) (A : Set S) :
    IsClosed A ↔ ∃ C : Set X, IsClosed C ∧ Subtype.val ⁻¹' C = A := isClosed_induced_iff

/-- **Definition A2.5:** closure is the least closed superset. -/
theorem definition_A2_5_closure {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsClosed (closure S) ∧ S ⊆ closure S ∧
      ∀ C, IsClosed C → S ⊆ C → closure S ⊆ C :=
  ⟨isClosed_closure, subset_closure, fun _ hC hSC => closure_minimal hSC hC⟩

/-- **Definition A2.5:** interior is the greatest open subset. -/
theorem definition_A2_5_interior {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsOpen (interior S) ∧ interior S ⊆ S ∧
      ∀ U, IsOpen U → U ⊆ S → U ⊆ interior S :=
  ⟨isOpen_interior, interior_subset, fun _ hU hUS => interior_maximal hUS hU⟩

/-- The intersection construction of closure described after Definition A2.5. -/
theorem appendix2_closure_intersection {X : Type*} [TopologicalSpace X] (S : Set X) :
    closure S = ⋂₀ {C | S ⊆ C ∧ IsClosed C} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sInter.mpr (fun C hC => closure_minimal hC.1 hC.2 hx)
  · intro x hx
    exact Set.mem_sInter.mp hx _ ⟨subset_closure, isClosed_closure⟩

/-- The union construction of interior described on p. 443. -/
theorem appendix2_interior_union {X : Type*} [TopologicalSpace X] (S : Set X) :
    interior S = ⋃₀ {U | U ⊆ S ∧ IsOpen U} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sUnion.mpr ⟨interior S, ⟨interior_subset, isOpen_interior⟩, hx⟩
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    exact interior_maximal hU.1 hU.2 hxU

/-- Interior points are exactly the centers of balls contained in the set. -/
theorem appendix2_interior_ball {X : Type*} [PseudoMetricSpace X] (S : Set X) (x : X) :
    x ∈ interior S ↔ ∃ ε > 0, Metric.ball x ε ⊆ S := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]

/-- The complement-duality exercise on p. 443. -/
theorem appendix2_closure_interior_complement {X : Type*} [TopologicalSpace X] (S : Set X) :
    closure S = (interior Sᶜ)ᶜ ∧ interior S = (closure Sᶜ)ᶜ :=
  ⟨closure_eq_compl_interior_compl, interior_eq_compl_closure_compl⟩

/-- The relative interior of a domain in itself is the entire domain. -/
theorem appendix2_relative_interior_self {X : Type*} [TopologicalSpace X] (S : Set X) :
    interior (Set.univ : Set S) = Set.univ := interior_univ

end Kreps.PreferenceProperties
