/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CountableUtility
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Connected.Basic

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Continuous preferences

Kreps I, Definition 1.13 and Proposition 1.14, pp. 13-14; Problem 1.11.
Continuity is expressed by openness of the strict graph. The metric characterization
uses exactly the common-radius condition in the definition. The contour results hold
on any topological space; the sequence equivalences require a sequential space.
-/

open Filter Topology

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- The upper weak contour, denoted NWT in the book. -/
def NoWorseThan (r : X → X → Prop) (x : X) : Set X := {y | r y x}

/-- The strict upper contour, denoted SBT in the book. -/
def StrictlyBetterThan (r : X → X → Prop) (x : X) : Set X := {y | Strict r y x}

/-- The strict lower contour, denoted SWT in the book. -/
def StrictlyWorseThan (r : X → X → Prop) (x : X) : Set X := {y | Strict r x y}

/-- Topological form of **Definition 1.13**, without bundling rationality. -/
def ContinuousPreference [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  IsOpen {p : X × X | Strict r p.1 p.2}

/-- The common-radius condition in **Definition 1.13**, p. 13. -/
def MetricContinuousPreference [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x y, Strict r x y → ∃ ε > 0, ∀ x' y',
    dist x' x < ε → dist y' y < ε → Strict r x' y'

/-- The graph definition agrees with the book's metric definition. -/
theorem continuousPreference_iff_metric [PseudoMetricSpace X] :
    ContinuousPreference r ↔ MetricContinuousPreference r := by
  constructor
  · intro h x y hxy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h (x, y) hxy
    refine ⟨ε, hε, fun x' y' hx hy => hball (show (x', y') ∈ Metric.ball (x, y) ε from ?_)⟩
    change max (dist x' x) (dist y' y) < ε
    exact max_lt hx hy
  · intro h
    apply Metric.isOpen_iff.mpr
    rintro ⟨x, y⟩ hxy
    obtain ⟨ε, hε, hball⟩ := h x y hxy
    refine ⟨ε, hε, ?_⟩
    rintro ⟨x', y'⟩ hdist
    change max (dist x' x) (dist y' y) < ε at hdist
    exact hball x' y' (max_lt_iff.mp hdist).1 (max_lt_iff.mp hdist).2

/-- A continuous real utility induces a continuous preference. -/
theorem continuousPreference_of_continuous_utility [TopologicalSpace X]
    {u : X → ℝ} (hu : Continuous u) : ContinuousPreference (UtilityPref u) := by
  have heq : {p : X × X | Strict (UtilityPref u) p.1 p.2} =
      {p : X × X | u p.2 < u p.1} := by
    ext p
    exact lt_iff_le_not_ge.symm
  change IsOpen {p : X × X | Strict (UtilityPref u) p.1 p.2}
  rw [heq]
  exact isOpen_lt (hu.comp continuous_snd) (hu.comp continuous_fst)

/-- **Proposition 1.14c**, stated as a property of all weak contours. -/
def ClosedContours [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, IsClosed (NoBetterThan r x) ∧ IsClosed (NoWorseThan r x)

/-- **Proposition 1.14d**, stated as a property of all strict contours. -/
def OpenStrictContours [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, IsOpen (StrictlyBetterThan r x) ∧ IsOpen (StrictlyWorseThan r x)

/-- Strict graph continuity implies openness of each strict contour. -/
theorem continuousPreference_openStrictContours [TopologicalSpace X]
    (h : ContinuousPreference r) : OpenStrictContours r := by
  intro x
  exact ⟨h.preimage (continuous_id.prodMk continuous_const),
    h.preimage (continuous_const.prodMk continuous_id)⟩

/-- Closed weak contours and open strict contours are complementary descriptions. -/
theorem closedContours_iff_openStrictContours [TopologicalSpace X] (hc : Complete r) :
    ClosedContours r ↔ OpenStrictContours r := by
  have hu (x : X) : StrictlyBetterThan r x = (NoBetterThan r x)ᶜ := by
    ext y
    exact proposition_1_9a hc y x
  have hl (x : X) : StrictlyWorseThan r x = (NoWorseThan r x)ᶜ := by
    ext y
    exact proposition_1_9a hc x y
  constructor
  · intro h x
    exact ⟨hu x ▸ (h x).1.isOpen_compl, hl x ▸ (h x).2.isOpen_compl⟩
  · intro h x
    constructor
    · have hh := (h x).1.isClosed_compl
      simpa only [hu x, compl_compl] using hh
    · have hh := (h x).2.isClosed_compl
      simpa only [hl x, compl_compl] using hh

/-- Open strict contours imply joint continuity for a complete, transitive preference. -/
theorem openStrictContours_continuousPreference [TopologicalSpace X] (hr : Rational r)
    (h : OpenStrictContours r) : ContinuousPreference r := by
  apply isOpen_prod_iff.mpr
  intro x y hxy
  by_cases hm : ∃ z, Strict r x z ∧ Strict r z y
  · obtain ⟨z, hxz, hzy⟩ := hm
    refine ⟨StrictlyBetterThan r z, StrictlyWorseThan r z,
      (h z).1, (h z).2, hxz, hzy, ?_⟩
    intro p hp
    exact strict_weak_trans hr.2 hp.1 hp.2.1
  · refine ⟨StrictlyBetterThan r y, StrictlyWorseThan r x,
      (h y).1, (h x).2, hxy, hxy, ?_⟩
    intro p hp
    apply (proposition_1_9a hr.1 p.1 p.2).mpr
    intro hrev
    exact hm ⟨p.1, strict_weak_trans hr.2 hp.2 hrev, hp.1⟩

/-- **Proposition 1.14c**, both directions. -/
theorem proposition_1_14c [TopologicalSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ ClosedContours r :=
  ⟨fun h => (closedContours_iff_openStrictContours hr.1).mpr
    (continuousPreference_openStrictContours h),
    fun h => openStrictContours_continuousPreference hr
      ((closedContours_iff_openStrictContours hr.1).mp h)⟩

/-- **Proposition 1.14d**, both directions. -/
theorem proposition_1_14d [TopologicalSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ OpenStrictContours r :=
  ⟨continuousPreference_openStrictContours, openStrictContours_continuousPreference hr⟩

/-- **Proposition 1.14a**: both weak comparisons are preserved in a sequence limit. -/
def SequenceWeakContinuity [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ (u : ℕ → X) x y, Tendsto u atTop (𝓝 x) →
    ((∀ n, r (u n) y) → r x y) ∧ ((∀ n, r y (u n)) → r y x)

/-- **Proposition 1.14b**: both strict comparisons eventually hold along a convergent sequence. -/
def SequenceStrictContinuity [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ (u : ℕ → X) x y, Tendsto u atTop (𝓝 x) →
    (Strict r x y → ∀ᶠ n in atTop, Strict r (u n) y) ∧
      (Strict r y x → ∀ᶠ n in atTop, Strict r y (u n))

/-- **Proposition 1.14a**, both directions, on every sequential space. -/
theorem proposition_1_14a [TopologicalSpace X] [SequentialSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ SequenceWeakContinuity r := by
  rw [proposition_1_14c hr]
  constructor
  · intro h u x y ht
    exact ⟨fun hn => (h y).2.mem_of_tendsto ht (Eventually.of_forall hn),
      fun hn => (h y).1.mem_of_tendsto ht (Eventually.of_forall hn)⟩
  · intro h y
    constructor
    · apply isSeqClosed_iff_isClosed.mp
      intro u x hn ht
      exact (h u x y ht).2 hn
    · apply isSeqClosed_iff_isClosed.mp
      intro u x hn ht
      exact (h u x y ht).1 hn

/-- **Proposition 1.14b**, both directions, on every sequential space. -/
theorem proposition_1_14b [TopologicalSpace X] [SequentialSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ SequenceStrictContinuity r := by
  constructor
  · intro h u x y ht
    have ho := continuousPreference_openStrictContours h
    exact ⟨fun hxy => ht ((ho y).1.mem_nhds hxy),
      fun hyx => ht ((ho y).2.mem_nhds hyx)⟩
  · intro h
    apply (proposition_1_14a hr).mpr
    intro u x y ht
    constructor
    · intro hn
      by_contra hxy
      obtain ⟨n, hny⟩ := ((h u x y ht).2 ((proposition_1_9a hr.1 y x).mpr hxy)).exists
      exact hny.2 (hn n)
    · intro hn
      by_contra hyx
      obtain ⟨n, hny⟩ := ((h u x y ht).1 ((proposition_1_9a hr.1 x y).mpr hyx)).exists
      exact hny.2 (hn n)

/-- **Problem 1.11**: all four characterizations, including the definition's metric form. -/
theorem problem_1_11 [PseudoMetricSpace X] (hr : Rational r) :
    (MetricContinuousPreference r ↔ SequenceWeakContinuity r) ∧
      (MetricContinuousPreference r ↔ SequenceStrictContinuity r) ∧
      (MetricContinuousPreference r ↔ ClosedContours r) ∧
      (MetricContinuousPreference r ↔ OpenStrictContours r) :=
  ⟨continuousPreference_iff_metric.symm.trans (proposition_1_14a hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14b hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14c hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14d hr)⟩

end Kreps.PreferenceProperties
