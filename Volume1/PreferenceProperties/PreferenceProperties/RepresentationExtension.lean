/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousUtility
import Mathlib.Topology.Order.IntermediateValue

/-!
# Extending utility from a curve that meets every indifference class

Kreps I, Problem 2.14c, p. 48. A continuous representation on a connected curve
extends to the whole domain by indifference. The extension has exactly the same
range; its continuity follows from open strict contours and an interval-valued
range. These results also support the homogeneous representation in Proposition 2.19.
-/

namespace Kreps.PreferenceProperties

variable {X Y : Type*} {r : X → X → Prop}

/-- Give each bundle the value of a selected indifferent point on the reference curve. -/
noncomputable def LiftedUtility (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x) (x : X) : ℝ :=
  v (Classical.choose (hcover x))

/-- The chosen indifferent points preserve every original preference comparison. -/
theorem liftedUtility_represents (hr : Rational r) (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) :
    Represents (LiftedUtility f v hcover) r := by
  intro x y
  have hx := Classical.choose_spec (hcover x)
  have hy := Classical.choose_spec (hcover y)
  constructor
  · intro hxy
    exact (hv _ _).mp (hr.2 _ x _ hx.1 (hr.2 x y _ hxy hy.2))
  · intro hxy
    have h := (hv _ _).mpr hxy
    exact hr.2 x _ y hx.2 (hr.2 _ _ y h hy.1)

/-- The extension agrees with the specified values on the reference curve. -/
theorem liftedUtility_agrees (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (y : Y) :
    LiftedUtility f v hcover (f y) = v y := by
  have h := Classical.choose_spec (hcover (f y))
  exact le_antisymm ((hv _ _).mp h.2) ((hv _ _).mp h.1)

/-- Extending by indifference adds no utility values and loses none. -/
theorem liftedUtility_range (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) :
    Set.range (LiftedUtility f v hcover) = Set.range v := by
  apply Set.Subset.antisymm
  · rintro a ⟨x, hx⟩
    exact ⟨Classical.choose (hcover x), hx⟩
  · rintro a ⟨y, hy⟩
    exact ⟨f y, (liftedUtility_agrees f v hcover hv y).trans hy⟩

/-- An interval-valued representation of a continuous preference must itself be continuous. -/
theorem continuous_of_ordConnected_range [TopologicalSpace X] {u : X → ℝ}
    (hu : Represents u r) (hc : ContinuousPreference r)
    (hRange : Set.OrdConnected (Set.range u)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  by_cases ha : a ∈ Set.range u
  · obtain ⟨z, hz⟩ := ha
    have hgt : u ⁻¹' Set.Ioi a = StrictlyBetterThan r z := by
      ext x
      change a < u x ↔ Strict r x z
      rw [strict_iff_utility_lt hu, hz]
    have hlt : u ⁻¹' Set.Iio a = StrictlyWorseThan r z := by
      ext x
      change u x < a ↔ Strict r z x
      rw [strict_iff_utility_lt hu, hz]
    exact ⟨hgt ▸ (ho z).1, hlt ▸ (ho z).2⟩
  · constructor
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change a < u x at hx
      have hall (y : X) : a < u y := by
        by_contra hy
        exact ha (hRange.out ⟨y, rfl⟩ ⟨x, rfl⟩ ⟨le_of_not_gt hy, hx.le⟩)
      exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change u x < a at hx
      have hall (y : X) : u y < a := by
        by_contra hy
        exact ha (hRange.out ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨hx.le, le_of_not_gt hy⟩)
      exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)

/-- A continuous representation on a connected reference domain extends continuously. -/
theorem liftedUtility_continuous [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace Y] (hr : Rational r) (hc : ContinuousPreference r)
    (f : Y → X) (v : Y → ℝ) (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (hvc : Continuous v) :
    Continuous (LiftedUtility f v hcover) := by
  apply continuous_of_ordConnected_range (liftedUtility_represents hr f v hcover hv) hc
  rw [liftedUtility_range f v hcover hv]
  exact (isPreconnected_range hvc).ordConnected

/-- **Problem 2.14c:** extend the curve's continuous representation to the entire orthant. -/
theorem problem_2_14c {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (Z : Set (NonnegativeOrthant k)) (hZ : IsPreconnected Z)
    (v : Z → ℝ) (hv : Represents v (fun a b => r a.val b.val)) (hvc : Continuous v)
    (hcover : ∀ x, ∃ z : Z, Indifferent r z.val x) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧
      ∀ z : Z, u z.val = v z := by
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp hZ
  exact ⟨LiftedUtility Subtype.val v hcover,
    liftedUtility_represents hr Subtype.val v hcover hv,
    liftedUtility_continuous hr hc Subtype.val v hcover hv hvc,
    liftedUtility_agrees Subtype.val v hcover hv⟩

end Kreps.PreferenceProperties
