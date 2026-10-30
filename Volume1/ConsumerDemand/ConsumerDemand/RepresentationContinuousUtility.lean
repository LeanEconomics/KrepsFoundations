/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationMonotonicity
import ConsumerDemand.RepresentationLexicographic
import Mathlib.Topology.Order.Compact

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# Continuous utility and intermediate indifference

Kreps I, the forward direction of Proposition 2.9, the compact-choice consequence
on p. 35, and Lemma 2.10, pp. 36, 38. The connected-image lemma proves the path
crossing result without assuming a continuous numerical representation. It is an
ingredient of that representation construction, not a use of the desired conclusion.
-/

namespace Kreps.ConsumerDemand.Representation

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- **Proposition 2.9**, forward direction, from a continuous representation. -/
theorem proposition_2_9_forward {u : X → ℝ} (hu : Represents u r) (hc : Continuous u) :
    ContinuousPreference r := by
  have he : r = UtilityPref u := by
    funext x y
    exact propext (hu x y)
  rw [he]
  exact continuousPreference_of_continuous_utility hc

/-- The extreme-value proof of nonempty compact-menu choice described on p. 35. -/
theorem compact_choice_of_continuous_utility {u : X → ℝ} (hu : Represents u r)
    (hc : Continuous u) {A : Set X} (hA : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hA.exists_isMaxOn hne hc.continuousOn
  exact ⟨x, hx, fun y hy => (hu x y).mpr (hmax hy)⟩

/-- A connected continuous image crosses every weakly bracketed indifference class. -/
theorem indifference_on_connected_image {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] (hr : Rational r) (hc : ContinuousPreference r)
    (f : T → X) (hf : Continuous f) (x : X) {a b : T}
    (ha : r (f a) x) (hb : r x (f b)) : ∃ t, Indifferent r (f t) x := by
  by_contra hn
  push Not at hn
  let U := f ⁻¹' StrictlyBetterThan r x
  let V := f ⁻¹' StrictlyWorseThan r x
  have ho := continuousPreference_openStrictContours hc
  have hU : IsOpen U := (ho x).1.preimage hf
  have hV : IsOpen V := (ho x).2.preimage hf
  have ha' : a ∈ U := ⟨ha, fun h => hn a ⟨ha, h⟩⟩
  have hb' : b ∈ V := ⟨hb, fun h => hn b ⟨h, hb⟩⟩
  have hcover : Set.univ ⊆ U ∪ V := by
    intro t _
    rcases hr.1 (f t) x with h | h
    · exact Or.inl ⟨h, fun h' => hn t ⟨h, h'⟩⟩
    · exact Or.inr ⟨h, fun h' => hn t ⟨h', h⟩⟩
  obtain ⟨t, _, htU, htV⟩ := isPreconnected_univ U V hU hV hcover
    ⟨a, Set.mem_univ a, ha'⟩ ⟨b, Set.mem_univ b, hb'⟩
  exact htU.2 htV.1

/-- **Lemma 2.10:** a continuous path between weak preference bounds meets the middle class. -/
theorem lemma_2_10 (hr : Rational r) (hc : ContinuousPreference r)
    (f : UnitSegment → X) (hf : Continuous f) (x : X)
    (h0 : r (f ⟨0, by norm_num⟩) x) (h1 : r x (f ⟨1, by norm_num⟩)) :
    ∃ t, Indifferent r (f t) x := by
  let : PreconnectedSpace UnitSegment := isPreconnected_iff_preconnectedSpace.mp
    (convex_Icc (0 : ℝ) 1).isPreconnected
  exact indifference_on_connected_image hr hc f hf x h0 h1

/-- Section 2.4: monotonicity converts coordinate bounds into the bounds in Lemma 2.10. -/
theorem monotone_path_crossing {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (f : UnitSegment → NonnegativeOrthant k) (hf : Continuous f) (x : NonnegativeOrthant k)
    (h0 : x ≤ f ⟨0, by norm_num⟩) (h1 : f ⟨1, by norm_num⟩ ≤ x) :
    ∃ t, Indifferent r (f t) x :=
  lemma_2_10 hr hc f hf x (hm _ _ h0) (hm _ _ h1)

end Kreps.ConsumerDemand.Representation
