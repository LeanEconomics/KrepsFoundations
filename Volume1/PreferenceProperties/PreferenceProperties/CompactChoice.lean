/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousPreference
import PreferenceProperties.InfiniteChoice
import Mathlib.Topology.Compactness.Compact

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice from compact menus

Kreps I, Proposition 1.19, p. 17, and the direct-proof part of Problem 1.13, pp. 26-27.
Finite preference maxima give the finite intersection property for closed upper contours.
Compactness then yields a greatest element without assuming continuous utility exists.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X]

/-- A rational preference with closed contours attains a greatest element on each compact menu. -/
theorem compact_prefChoice_nonempty {r : X → X → Prop} (hr : Rational r)
    (hc : ClosedContours r) {A : Set X} (hcompact : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hfinite (u : Finset A) : (A ∩ ⋂ i ∈ u, NoWorseThan r i.val).Nonempty := by
    let S : Set X := insert a (Subtype.val '' (u : Set A))
    have hsfin : S.Finite := (u.finite_toSet.image Subtype.val).insert a
    have hsne : S.Nonempty := ⟨a, Set.mem_insert a _⟩
    obtain ⟨x, hx, hmax⟩ := prefChoice_finiteNonempty hr S hsfin hsne
    refine ⟨x, ?_, ?_⟩
    · rcases hx with hxa | ⟨i, _, rfl⟩
      · exact hxa ▸ ha
      · exact i.property
    · simp only [Set.mem_iInter]
      intro i hi
      exact hmax i.val (Or.inr ⟨i, hi, rfl⟩)
  obtain ⟨x, hx, hmax⟩ := hcompact.inter_iInter_nonempty
    (fun i : A => NoWorseThan r i.val) (fun i => (hc i.val).2) hfinite
  refine ⟨x, hx, fun y hy => ?_⟩
  exact Set.mem_iInter.mp hmax ⟨y, hy⟩

/-- **Proposition 1.19**, p. 17, generalized from the orthant to every topological space. -/
theorem proposition_1_19 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hco : Coherent c) (ha : Assumption116 c)
    (hc : ContinuousPreference (Revealed c)) {A : Set X}
    (hcompact : IsCompact A) (hne : A.Nonempty) : (c A).Nonempty := by
  have hr : Rational (Revealed c) := ⟨revealed_complete hf hn, revealed_transitive hf hn hco⟩
  rw [(proposition_1_17 hf hn hco).mpr ha]
  exact compact_prefChoice_nonempty hr ((proposition_1_14c hr).mp hc) hcompact hne

/-- The direct compactness proof requested in **Problem 1.13**, without Debreu's theorem. -/
theorem problem_1_13_direct {r : X → X → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) {A : Set X} (hcompact : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty :=
  compact_prefChoice_nonempty hr ((proposition_1_14c hr).mp hc) hcompact hne

end Kreps.PreferenceProperties
