/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith

/-!
# Appendix 3: convex sets and their hulls

Kreps I, Definition A3.1, Propositions A3.2–A3.5 and A3.7, pp. 452–456.
These interfaces use Mathlib's convexity and hull constructions. Finite combinations
include an explicit nonnegative weight vector with total weight one. Carathéodory's
theorem bounds the number of points by the dimension plus one.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition A3.1:** closure under the book's two-point convex combinations. -/
theorem definition_A3_1 : Convex ℝ S ↔
    ∀ x ∈ S, ∀ y ∈ S, ∀ a ∈ Set.Icc (0 : ℝ) 1, a • x + (1 - a) • y ∈ S := by
  constructor
  · intro h x hx y hy a ha
    exact h hx hy ha.1 (sub_nonneg.mpr ha.2) (by linarith)
  · intro h x hx y hy a b ha hb hab
    have he : b = 1 - a := by linarith
    subst b
    exact h x hx y hy a ⟨ha, by linarith⟩

/-- **Proposition A3.2:** any finite convex combination remains in the set. -/
theorem proposition_A3_2 {ι : Type*} (t : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hS : Convex ℝ S) (hw : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ S) : ∑ i ∈ t, w i • z i ∈ S :=
  hS.sum_mem hw h1 hz

/-- **Proposition A3.3:** arbitrary intersections of convex sets are convex. -/
theorem proposition_A3_3 {C : Set (Set E)} (hC : ∀ s ∈ C, Convex ℝ s) :
    Convex ℝ (⋂₀ C) := convex_sInter hC

/-- **Definition A3.4:** the convex hull is the smallest convex superset. -/
theorem definition_A3_4_convexHull : S ⊆ convexHull ℝ S ∧ Convex ℝ (convexHull ℝ S) ∧
    ∀ T, S ⊆ T → Convex ℝ T → convexHull ℝ S ⊆ T :=
  ⟨subset_convexHull ℝ S, convex_convexHull ℝ S, fun _ h hc => convexHull_min h hc⟩

/-- **Proposition A3.4:** hull membership means being a finite convex combination. -/
theorem proposition_A3_4 {x : E} : x ∈ convexHull ℝ S ↔
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x :=
  mem_convexHull_iff_exists_fintype

/-- **Proposition A3.5 (Carathéodory):** at most dimension plus one points suffice. -/
theorem proposition_A3_5 [FiniteDimensional ℝ E] {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ t : Finset E, (↑t : Set E) ⊆ S ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := AffineIndependent.card_le_finrank_succ
    (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx)
  have hcard : t.card ≤ Module.finrank ℝ
      (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 := by
    simpa only [Fintype.card_coe] using h
  exact hcard.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

variable [TopologicalSpace E]

/-- **Definition A3.4:** the closed convex hull has the closed-and-convex universal property. -/
theorem definition_A3_4_closedConvexHull : S ⊆ closedConvexHull ℝ S ∧
    Convex ℝ (closedConvexHull ℝ S) ∧ IsClosed (closedConvexHull ℝ S) ∧
      ∀ T, S ⊆ T → Convex ℝ T → IsClosed T → closedConvexHull ℝ S ⊆ T :=
  ⟨subset_closedConvexHull, convex_closedConvexHull, isClosed_closedConvexHull,
    fun _ h hc ht => closedConvexHull_min h hc ht⟩

/-- **Proposition A3.7**, first assertion: closure preserves convexity. -/
theorem proposition_A3_7_closure [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : Convex ℝ S) : Convex ℝ (closure S) := hS.closure

/-- **Proposition A3.7**, second assertion: close the convex hull to get the closed convex hull. -/
theorem proposition_A3_7_closedHull [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    closure (convexHull ℝ S) = closedConvexHull ℝ S :=
  closedConvexHull_eq_closure_convexHull.symm

end Kreps.PreferenceProperties
