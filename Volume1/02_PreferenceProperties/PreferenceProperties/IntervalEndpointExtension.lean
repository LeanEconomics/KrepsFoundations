/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.MonotoneEndpointExtension
import Mathlib.Analysis.Convex.Topology

/-!
# Endpoint extensions on real score intervals

A nonempty interior is dense in a real interval. Points of the interval outside
that interior can only be attained least or greatest elements. Consequently,
continuous strict interior scales with finite attained endpoint limits extend
to the full score interval.
-/

namespace Kreps.PreferenceProperties

/-- The real interior is dense relative to a nondegenerate interval. -/
theorem interval_interior_dense {S : Set ℝ} (hS : S.OrdConnected)
    (hn : (interior S).Nonempty) : Dense {x : S | x.val ∈ interior S} := by
  rw [Subtype.dense_iff]
  have he : ((↑) : S → ℝ) '' {x : S | x.val ∈ interior S} = interior S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  rw [he, (convex_iff_ordConnected.mpr hS).closure_interior_eq_closure_of_nonempty_interior hn]
  exact subset_closure

/-- A point of a real interval outside its interior is a least or greatest element. -/
theorem interval_outside_interior_extreme {S : Set ℝ} (hS : S.OrdConnected)
    (x : S) (hx : x.val ∉ interior S) : IsBot x ∨ IsTop x := by
  by_contra! h
  obtain ⟨a, ha⟩ := not_forall.mp h.1
  obtain ⟨b, hb⟩ := not_forall.mp h.2
  have hax : a.val < x.val := lt_of_not_ge ha
  have hxb : x.val < b.val := lt_of_not_ge hb
  apply hx
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Ioo_mem_nhds hax hxb) (fun _ hy =>
      hS.out a.property b.property ⟨hy.1.le, hy.2.le⟩))

/-- A continuous strict scale extends from an interval interior to its bounded attained ends. -/
theorem interval_exists_continuous_strictMono_extension {S : Set ℝ} (hS : S.OrdConnected)
    (hn : (interior S).Nonempty) {f : interior S → ℝ}
    (hf : Continuous f) (hm : StrictMono f)
    (hlo : ∀ x : S, x.val ∉ interior S → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x : S, x.val ∉ interior S → IsTop x → BddAbove (Set.range f)) :
    ∃ g : S → ℝ, Continuous g ∧ StrictMono g ∧
      ∀ x : interior S, g (Set.inclusion interior_subset x) = f x := by
  let : Fact S.OrdConnected := ⟨hS⟩
  let D : Set S := {x | x.val ∈ interior S}
  let inc : D → interior S := fun x => ⟨x.val.val, x.property⟩
  let f' : D → ℝ := f ∘ inc
  have hc : Continuous inc :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hm' : StrictMono f' := fun _ _ h => hm h
  have hr : Set.range f' = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inc x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨⟨x.val, interior_subset x.property⟩, x.property⟩, rfl⟩
  obtain ⟨g, hg, hgm, heq⟩ := exists_continuous_strictMono_endpoint_extension
    (interval_interior_dense hS hn) (interval_outside_interior_extreme hS)
    (hf.comp hc) hm' (fun x hx he => hr ▸ hlo x hx he)
    (fun x hx he => hr ▸ hhi x hx he)
  exact ⟨g, hg, hgm, fun x => heq ⟨Set.inclusion interior_subset x, x.property⟩⟩

end Kreps.PreferenceProperties
