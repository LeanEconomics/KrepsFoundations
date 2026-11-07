/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Structural preference properties used by Afriat's theorem

Selected local prerequisite copies from Chapter 2's `OrthantRepresentation`,
`Monotonicity`, `ContinuousPreference` and `ConvexPreference`, commit `7d496c5`.
Definitions preserve the nonnegative orthant, the closed-radius local-insatiability
condition and the distinction between strict coordinate increase and strict
preference. The final concavity bridge specializes standard Jensen inequalities.
-/

namespace Kreps.RevealedPreference

variable {X : Type*} {r : X → X → Prop}

/-- The nonnegative commodity orthant, including boundary bundles. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- A distinct weakly larger bundle is strictly preferred. -/
def StrictlyMonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → x ≠ y → Strict r x y

/-- A strict improvement exists within every positive distance. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

/-- Continuity of preference is openness of its strict-comparison graph. -/
def ContinuousPreference [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  IsOpen {p : X × X | Strict r p.1 p.2}

/-- A convex combination belongs to the same convex consumption domain. -/
def Mix {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- A mixture is weakly preferred to the worse endpoint. -/
def ConvexPreference {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- Continuous utility gives continuous preference. -/
theorem continuousPreference_of_continuous_utility [TopologicalSpace X]
    {u : X → ℝ} (hu : Continuous u) : ContinuousPreference (UtilityPref u) := by
  have heq : {p : X × X | Strict (UtilityPref u) p.1 p.2} =
      {p : X × X | u p.2 < u p.1} := by
    ext p
    exact lt_iff_le_not_ge.symm
  change IsOpen {p : X × X | Strict (UtilityPref u) p.1 p.2}
  rw [heq]
  exact isOpen_lt (hu.comp continuous_snd) (hu.comp continuous_fst)

/-- A strictly increasing numerical utility gives strictly monotone preference. -/
theorem strictlyMonotonePreference_of_strictMono [PartialOrder X] {u : X → ℝ}
    (hu : StrictMono u) : StrictlyMonotonePreference (UtilityPref u) := by
  intro x y hyx hne
  have h := hu (lt_of_le_of_ne hyx hne.symm)
  exact ⟨h.le, not_le_of_gt h⟩

/-- The closed-radius formulation is equivalent to an open-ball improvement. -/
theorem locallyInsatiable_iff_open [PseudoMetricSpace X] :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x < ε ∧ Strict r y x := by
  constructor
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x (ε / 2) (by positivity)
    exact ⟨y, lt_of_le_of_lt hy (by linarith), hr⟩
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x ε hε
    exact ⟨y, hy.le, hr⟩

/-- Raise every coordinate by the same nonnegative amount. -/
def RaisedBundle {k : ℕ} (x : NonnegativeOrthant k) (δ : ℝ) (hδ : 0 ≤ δ) :
    NonnegativeOrthant k := ⟨fun j => x.val j + δ, fun j => add_nonneg (x.property j) hδ⟩

/-- The finite-product distance is bounded by the common coordinate increase. -/
theorem raisedBundle_dist_le {k : ℕ} (x : NonnegativeOrthant k) {δ : ℝ} (hδ : 0 ≤ δ) :
    dist (RaisedBundle x δ hδ) x ≤ δ := by
  change dist (fun j => x.val j + δ) x.val ≤ δ
  apply (dist_pi_le_iff hδ).mpr
  intro j
  simp [abs_of_nonneg hδ]

/-- Strict monotonicity gives local insatiability in a positive number of commodities. -/
theorem strictlyMonotone_locallyInsatiable {k : ℕ} (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : StrictlyMonotonePreference r) : LocallyInsatiable r := by
  intro x ε hε
  refine ⟨RaisedBundle x ε hε.le, raisedBundle_dist_le x hε.le, hm _ x ?_ ?_⟩
  · intro j
    exact le_add_of_nonneg_right hε.le
  · intro he
    have hj := congrArg (fun z : NonnegativeOrthant k => z.val ⟨0, hk⟩) he
    change x.val ⟨0, hk⟩ + ε = x.val ⟨0, hk⟩ at hj
    linarith

end Kreps.RevealedPreference
