/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixConvexSets
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

/-!
# Appendix 3: compactness of convex hulls

Kreps I, Proposition A3.6, p. 455. Carathéodory reduces the convex hull to a
finite union of sets of mixtures with a bounded number of terms. Each such set is
the continuous image of a compact set of weights and a finite product of the
original compact set. The proof includes the empty-set case.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Convex combinations of exactly `n` listed points; zero weights are allowed. -/
def FiniteMixtureSet (S : Set E) (n : ℕ) : Set E :=
  {x | ∃ (w : Fin n → ℝ) (z : Fin n → E), (∀ i, 0 ≤ w i) ∧
    ∑ i, w i = 1 ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x}

/-- Every finite mixture belongs to the convex hull. -/
theorem finiteMixtureSet_subset_convexHull (S : Set E) (n : ℕ) :
    FiniteMixtureSet S n ⊆ convexHull ℝ S := by
  rintro x ⟨w, z, hw, h1, hz, hx⟩
  exact mem_convexHull_of_exists_fintype w z hw h1 hz hx

/-- Reindex a mixture on a finset by a finite interval of natural numbers. -/
theorem mem_finiteMixtureSet_of_mem_finset_hull {S : Set E} (t : Finset E)
    (ht : (↑t : Set E) ⊆ S) {x : E} (hx : x ∈ convexHull ℝ (↑t : Set E)) :
    x ∈ FiniteMixtureSet S t.card := by
  classical
  obtain ⟨w, hw, h1, hx⟩ := Finset.mem_convexHull'.mp hx
  let e : t ≃ Fin t.card := Fintype.equivFinOfCardEq (Fintype.card_coe t)
  refine ⟨fun i => w (e.symm i), fun i => (e.symm i).val,
    fun i => hw _ (e.symm i).property, ?_, fun i => ht (e.symm i).property, ?_⟩
  · calc
      ∑ i : Fin t.card, w (e.symm i) = ∑ i : t, w i :=
        Equiv.sum_comp e.symm (fun i : t => w i)
      _ = ∑ i ∈ t, w i := Finset.sum_attach t w
      _ = 1 := h1
  · calc
      ∑ i : Fin t.card, w (e.symm i) • (e.symm i).val =
          ∑ i : t, w i • i.val := Equiv.sum_comp e.symm (fun i : t => w i • i.val)
      _ = ∑ i ∈ t, w i • i := Finset.sum_attach t (fun i => w i • i)
      _ = x := hx

/-- Carathéodory expresses the hull as finitely many fixed-length mixture sets. -/
theorem convexHull_eq_finite_mixture_union [FiniteDimensional ℝ E] (S : Set E) :
    convexHull ℝ S = ⋃ n : Fin (Module.finrank ℝ E + 2), FiniteMixtureSet S n.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hcard, hxt⟩ := proposition_A3_5 hx
    exact Set.mem_iUnion.mpr ⟨⟨t.card, Nat.lt_add_one_iff.mpr hcard⟩,
      mem_finiteMixtureSet_of_mem_finset_hull t ht hxt⟩
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact finiteMixtureSet_subset_convexHull S n.val hn

/-- Mixtures with a fixed finite number of terms form a compact set. -/
theorem finiteMixtureSet_isCompact {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} (hS : IsCompact S) (n : ℕ) : IsCompact (FiniteMixtureSet S n) := by
  let W : Set (Fin n → ℝ) := Set.Icc 0 1 ∩ {w | ∑ i, w i = 1}
  let Z : Set (Fin n → G) := {z | ∀ i, z i ∈ S}
  let mix : (Fin n → ℝ) × (Fin n → G) → G := fun p => ∑ i, p.1 i • p.2 i
  have hW : IsCompact W := isCompact_Icc.inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hZ : IsCompact Z := isCompact_pi_infinite fun _ => hS
  have hm : Continuous mix := by fun_prop
  have he : FiniteMixtureSet S n = mix '' (W ×ˢ Z) := by
    ext x
    constructor
    · rintro ⟨w, z, hw, h1, hz, hx⟩
      refine ⟨(w, z), ⟨⟨⟨hw, ?_⟩, h1⟩, hz⟩, hx⟩
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hw j)
        (Finset.mem_univ i)
      change w i ≤ (1 : ℝ)
      simpa only [h1] using hi
    · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, hx⟩
      exact ⟨w, z, hw.1.1, hw.2, hz, hx⟩
  rw [he]
  exact (hW.prod hZ).image hm

/-- **Proposition A3.6:** in finite-dimensional Euclidean space, compact hulls stay compact. -/
theorem proposition_A3_6 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {S : Set G} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_finite_mixture_union]
  exact isCompact_iUnion fun n => finiteMixtureSet_isCompact hS n.val

end Kreps.PreferenceProperties
