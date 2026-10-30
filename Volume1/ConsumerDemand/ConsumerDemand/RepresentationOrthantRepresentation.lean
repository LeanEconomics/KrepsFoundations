/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationContinuousPreference
import Mathlib.Analysis.Convex.PathConnected

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Utility representation on the nonnegative orthant

Kreps I, Proposition 1.15, pp. 14-15. Connectedness supplies an intermediate
strict preference, and a countable dense subset supplies the separator required
by Proposition 1.12. This uses the alternative topological argument invited on p. 15.
The conclusion asserts a utility representation, without claiming its continuity.
-/

namespace Kreps.ConsumerDemand.Representation

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- In a connected domain, a continuous preference has no adjacent strict ranks. -/
theorem exists_strict_between [PreconnectedSpace X] (hr : Rational r)
    (hc : ContinuousPreference r) {x y : X} (hxy : Strict r x y) :
    ∃ z, Strict r x z ∧ Strict r z y := by
  have ho := continuousPreference_openStrictContours hc
  have hcover : Set.univ ⊆ StrictlyWorseThan r x ∪ StrictlyBetterThan r y := by
    intro z _
    by_cases hxz : Strict r x z
    · exact Or.inl hxz
    · right
      have hzx : r z x := by
        by_contra h
        exact hxz ((proposition_1_9a hr.1 x z).mpr h)
      exact weak_strict_trans hr.2 hzx hxy
  obtain ⟨z, _, hxz, hzy⟩ := isPreconnected_univ
    (StrictlyWorseThan r x) (StrictlyBetterThan r y) (ho x).2 (ho y).1 hcover
      ⟨y, Set.mem_univ y, hxy⟩ ⟨x, Set.mem_univ x, hxy⟩
  exact ⟨z, hxz, hzy⟩

/-- A dense subset separates all strict comparisons on a connected domain. -/
theorem dense_orderSeparating [PreconnectedSpace X] (hr : Rational r)
    (hc : ContinuousPreference r) {D : Set X} (hD : Dense D) : OrderSeparating r D := by
  intro x y hxy
  obtain ⟨z, hxz, hzy⟩ := exists_strict_between hr hc hxy
  have ho := continuousPreference_openStrictContours hc
  obtain ⟨d, hd, hxd, hdy⟩ := hD.exists_mem_open ((ho x).2.inter (ho y).1) ⟨z, hxz, hzy⟩
  exact ⟨d, hd, hxd.1, hdy⟩

/-- General form of the countable-dense-set argument for Proposition 1.15. -/
theorem represents_of_continuous_connected [PreconnectedSpace X]
    [TopologicalSpace.SeparableSpace X] (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : X → ℝ, Represents u r := by
  obtain ⟨D, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense X
  exact represents_of_countable_separating hr hcount (dense_orderSeparating hr hc hdense)

/-- The book's commodity domain, with its relative finite-dimensional topology. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- **Proposition 1.15**, pp. 14-15, for every finite number of commodities. -/
theorem proposition_1_15 (k : ℕ) {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  exact represents_of_continuous_connected hr hc

/-- Proposition 1.15 with the common-radius continuity hypothesis from Definition 1.13. -/
theorem proposition_1_15_metric (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : MetricContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r :=
  proposition_1_15 k hr (continuousPreference_iff_metric.mpr hc)

end Kreps.ConsumerDemand.Representation
