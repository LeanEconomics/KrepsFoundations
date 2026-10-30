/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationOrthantRepresentation

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# Monotonicity and insatiability

Kreps I, Section 2.1, pp. 31-32: Definitions 2.1 and 2.3, Proposition 2.2,
and the positive implications in Problem 2.6. Coordinatewise strict increases
are kept distinct from a weak increase with at least one strict coordinate.
-/

namespace Kreps.ConsumerDemand.Representation

variable {X : Type*} {r : X → X → Prop}

/-- **Definition 2.1:** coordinatewise increases are weak preference improvements. -/
def MonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → r x y

/-- **Definition 2.1:** a distinct weakly larger bundle is strictly preferred. -/
def StrictlyMonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → x ≠ y → Strict r x y

/-- The intermediate condition on p. 32 requires a strict increase in every coordinate. -/
def StrictAllIncreasePreference {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x y, (∀ j, y.val j < x.val j) → Strict r x y

/-- **Definition 2.3a:** every bundle has a strictly better alternative. -/
def GloballyInsatiable (r : X → X → Prop) : Prop := ∀ x, ∃ y, Strict r y x

/-- **Definition 2.3b:** a strict improvement exists at distance at most every positive radius. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

/-- **Proposition 2.2**, first equivalence. -/
theorem proposition_2_2_monotone [PartialOrder X] {u : X → ℝ} (hu : Represents u r) :
    MonotonePreference r ↔ Monotone u := by
  constructor
  · intro h x y hxy
    exact (hu y x).mp (h y x hxy)
  · intro h x y hyx
    exact (hu x y).mpr (h hyx)

/-- **Proposition 2.2**, second equivalence. -/
theorem proposition_2_2_strict [PartialOrder X] {u : X → ℝ} (hu : Represents u r) :
    StrictlyMonotonePreference r ↔ StrictMono u := by
  constructor
  · intro h x y hxy
    exact (strict_iff_utility_lt hu y x).mp (h y x hxy.le (ne_of_gt hxy))
  · intro h x y hyx hne
    exact (strict_iff_utility_lt hu x y).mpr (h (lt_of_le_of_ne hyx hne.symm))

/-- The universal quantifier emphasized after Proposition 2.2 and in Problem 2.1. -/
theorem monotone_all_representations [PartialOrder X] (hr : MonotonePreference r) :
    ∀ u : X → ℝ, Represents u r → Monotone u :=
  fun _ hu => (proposition_2_2_monotone hu).mp hr

/-- Existence of one nondecreasing representation suffices for monotone preference. -/
theorem monotone_of_some_representation [PartialOrder X]
    (h : ∃ u : X → ℝ, Represents u r ∧ Monotone u) : MonotonePreference r := by
  obtain ⟨u, hu, hm⟩ := h
  exact (proposition_2_2_monotone hu).mpr hm

/-- Every representation of strictly monotone preference is strictly increasing. -/
theorem strict_all_representations [PartialOrder X] (hr : StrictlyMonotonePreference r) :
    ∀ u : X → ℝ, Represents u r → StrictMono u :=
  fun _ hu => (proposition_2_2_strict hu).mp hr

/-- Existence of one strictly increasing representation suffices. -/
theorem strict_of_some_representation [PartialOrder X]
    (h : ∃ u : X → ℝ, Represents u r ∧ StrictMono u) : StrictlyMonotonePreference r := by
  obtain ⟨u, hu, hm⟩ := h
  exact (proposition_2_2_strict hu).mpr hm

/-- Rational strictly monotone preferences are monotone, including equality of bundles. -/
theorem strictlyMonotone_monotone [PartialOrder X] (hc : Complete r)
    (hs : StrictlyMonotonePreference r) : MonotonePreference r := by
  intro x y hyx
  by_cases hxy : x = y
  · subst y
    exact complete_refl hc x
  · exact (hs x y hyx hxy).1

/-- A strict coordinatewise increase is a nontrivial weak increase in positive dimension. -/
theorem strictlyMonotone_strictAllIncrease {k : ℕ} (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hs : StrictlyMonotonePreference r) : StrictAllIncreasePreference r := by
  intro x y hxy
  refine hs x y (fun j => (hxy j).le) ?_
  intro he
  have h := hxy ⟨0, hk⟩
  rw [he] at h
  exact (lt_irrefl _ h)

/-- The closed-radius definition is equivalent to using open balls. -/
theorem locallyInsatiable_iff_open [PseudoMetricSpace X] :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x < ε ∧ Strict r y x := by
  constructor
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x (ε / 2) (by positivity)
    exact ⟨y, lt_of_le_of_lt hy (by linarith), hr⟩
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x ε hε
    exact ⟨y, hy.le, hr⟩

/-- Local insatiability implies global insatiability. -/
theorem locallyInsatiable_global [PseudoMetricSpace X] (h : LocallyInsatiable r) :
    GloballyInsatiable r := by
  intro x
  obtain ⟨y, _, hy⟩ := h x 1 zero_lt_one
  exact ⟨y, hy⟩

/-- Insatiability in terms of any representing utility, as observed on p. 32. -/
theorem globallyInsatiable_iff_utility {u : X → ℝ} (hu : Represents u r) :
    GloballyInsatiable r ↔ ∀ x, ∃ y, u x < u y := by
  simp only [GloballyInsatiable, strict_iff_utility_lt hu]

/-- The corresponding local numerical restatement. -/
theorem locallyInsatiable_iff_utility [PseudoMetricSpace X] {u : X → ℝ}
    (hu : Represents u r) :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ u x < u y := by
  simp only [LocallyInsatiable, strict_iff_utility_lt hu]

/-- Add the same positive amount to every component. -/
def RaisedBundle {k : ℕ} (x : NonnegativeOrthant k) (δ : ℝ) (hδ : 0 ≤ δ) :
    NonnegativeOrthant k := ⟨fun j => x.val j + δ, fun j => add_nonneg (x.property j) hδ⟩

/-- In the finite-product metric, the common coordinate increase bounds the distance. -/
theorem raisedBundle_dist_le {k : ℕ} (x : NonnegativeOrthant k) {δ : ℝ} (hδ : 0 ≤ δ) :
    dist (RaisedBundle x δ hδ) x ≤ δ := by
  change dist (fun j => x.val j + δ) x.val ≤ δ
  apply (dist_pi_le_iff hδ).mpr
  intro j
  simp [abs_of_nonneg hδ]

/-- **Problem 2.6:** strict all-coordinate improvement gives LNS without continuity. -/
theorem strictAllIncrease_locallyInsatiable {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hs : StrictAllIncreasePreference r) : LocallyInsatiable r := by
  intro x ε hε
  refine ⟨RaisedBundle x ε hε.le, raisedBundle_dist_le x hε.le, ?_⟩
  apply hs
  intro j
  change x.val j < x.val j + ε
  linarith

/-- Monotonicity and LNS give strict all-coordinate improvement without continuity. -/
theorem monotone_locallyInsatiable_strictAllIncrease {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hm : MonotonePreference r) (hl : LocallyInsatiable r) :
    StrictAllIncreasePreference r := by
  intro x y hyx
  let U : Set (NonnegativeOrthant k) := {z | ∀ j, z.val j < x.val j}
  have ho : IsOpen U := by
    have heq : U = ⋂ j, {z : NonnegativeOrthant k | z.val j < x.val j} := by
      ext z
      simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_apply j).comp continuous_subtype_val) continuous_const
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp ho y hyx
  obtain ⟨z, hz, hzy⟩ := locallyInsatiable_iff_open.mp hl y ε hε
  have hzx : z ≤ x := fun j => (hb hz j).le
  exact weak_strict_trans hr.2 (hm x z hzx) hzy

/-- Continuity supplies the missing weak monotonicity in **Problem 2.6**. -/
theorem continuous_strictAllIncrease_monotone {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StrictAllIncreasePreference r) :
    MonotonePreference r := by
  intro x y hyx
  by_contra hnot
  have hyx' := (proposition_1_9a hr.1 y x).mpr hnot
  obtain ⟨ε, hε, hb⟩ := continuousPreference_iff_metric.mp hc y x hyx'
  let z := RaisedBundle x (ε / 2) (by positivity)
  have hz : dist z x < ε :=
    lt_of_le_of_lt (raisedBundle_dist_le x (by positivity)) (by linarith)
  have hyz := hb y z (by simpa using hε) hz
  have hzy : Strict r z y := hs z y (fun j => by
    change y.val j < x.val j + ε / 2
    have h := hyx j
    linarith)
  exact hyz.2 hzy.1

/-- **Problem 2.6**, full equivalence under the stated continuity assumption. -/
theorem problem_2_6 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) :
    StrictAllIncreasePreference r ↔ MonotonePreference r ∧ LocallyInsatiable r :=
  ⟨fun hs => ⟨continuous_strictAllIncrease_monotone hr hc hs,
      strictAllIncrease_locallyInsatiable hs⟩,
    fun h => monotone_locallyInsatiable_strictAllIncrease hr h.1 h.2⟩

end Kreps.ConsumerDemand.Representation
