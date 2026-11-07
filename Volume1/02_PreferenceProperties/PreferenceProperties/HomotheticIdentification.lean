/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SignedHomotheticRepresentation
import PreferenceProperties.IndifferenceCurves

/-!
# Recovering homothetic preference from one indifference curve

Kreps I, Problem 2.13, p. 48. Under continuity, strict monotonicity and
homotheticity, the indifference class of any nonzero bundle determines every
comparison. The origin's singleton class is a degenerate exception. The result
is stated in any finite dimension, hence includes the book's two-good case.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- A representation identifies indifference with equality of utility values. -/
theorem indifferent_iff_utility_eq {X : Type*} {r : X → X → Prop} {u : X → ℝ}
    (hu : Represents u r) (x y : X) : Indifferent r x y ↔ u x = u y := by
  constructor
  · intro h
    exact le_antisymm ((hu y x).mp h.2) ((hu x y).mp h.1)
  · intro h
    exact ⟨(hu x y).mpr h.ge, (hu y x).mpr h.le⟩

/-- Positive homogeneous functions agreeing on their unit class agree everywhere. -/
theorem homogeneous_unit_class_unique {k : ℕ} {u v : NonnegativeOrthant k → ℝ}
    (hu : HomogeneousUtility u) (hv : HomogeneousUtility v)
    (hpos : ∀ x, x ≠ OrthantZero k → 0 < u x)
    (hclass : ∀ x, u x = 1 ↔ v x = 1) : u = v := by
  funext x
  by_cases hx : x = OrthantZero k
  · subst x
    rw [homogeneousUtility_origin hu, homogeneousUtility_origin hv]
  · have hux := hpos x hx
    let t : ℝ≥0 := .mk (u x)⁻¹ (inv_nonneg.mpr hux.le)
    have hut : u (ScaleBundle t x) = 1 := by
      rw [hu]
      exact inv_mul_cancel₀ (ne_of_gt hux)
    have hvt := (hclass (ScaleBundle t x)).mp hut
    rw [hv] at hvt
    change (u x)⁻¹ * v x = 1 at hvt
    calc
      u x = u x * ((u x)⁻¹ * v x) := by rw [hvt, mul_one]
      _ = v x := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hux), one_mul]

/-- Normalize a homogeneous representation so that a specified nonzero bundle has value one. -/
theorem normalized_homogeneous_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    (hm : StrictlyMonotonePreference r) {p : NonnegativeOrthant k} (hp : p ≠ OrthantZero k) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u ∧
      u p = 1 ∧ ∀ x, x ≠ OrthantZero k → 0 < u x := by
  obtain ⟨u, hu, huc, huh⟩ := problem_2_12 hr hc hh
  have hup : 0 < u p := by
    have h := (strict_iff_utility_lt hu _ _).mp (hm p (OrthantZero k) p.property hp)
    simpa only [homogeneousUtility_origin huh] using h
  have hrep : Represents (fun x => u x / u p) r := by
    intro x y
    exact (hu x y).trans (div_le_div_iff_of_pos_right hup).symm
  have hhom : HomogeneousUtility (fun x => u x / u p) := by
    intro t x
    change u (ScaleBundle t x) / u p = (t : ℝ) * (u x / u p)
    rw [huh]
    ring
  refine ⟨fun x => u x / u p, hrep, huc.div_const _, hhom, div_self (ne_of_gt hup), ?_⟩
  intro x hx
  have h := (strict_iff_utility_lt hrep _ _).mp (hm x (OrthantZero k) x.property hx)
  simpa only [homogeneousUtility_origin hhom] using h

/-- **Problem 2.13, homothetic case:** one nonzero indifference class identifies all preferences. -/
theorem problem_2_13_homothetic {k : ℕ}
    {r s : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hs : Rational s)
    (hrc : ContinuousPreference r) (hsc : ContinuousPreference s)
    (hrh : HomotheticPreference r) (hsh : HomotheticPreference s)
    (hrm : StrictlyMonotonePreference r) (hsm : StrictlyMonotonePreference s)
    {p : NonnegativeOrthant k} (hp : p ≠ OrthantZero k)
    (hclass : IndifferenceClass r p = IndifferenceClass s p) : r = s := by
  obtain ⟨u, hu, _, huh, hup, hupos⟩ := normalized_homogeneous_representation hr hrc hrh hrm hp
  obtain ⟨v, hv, _, hvh, hvp, _⟩ := normalized_homogeneous_representation hs hsc hsh hsm hp
  have huv : u = v := by
    apply homogeneous_unit_class_unique huh hvh hupos
    intro x
    have h : Indifferent r x p ↔ Indifferent s x p := Set.ext_iff.mp hclass x
    rw [indifferent_iff_utility_eq hu, indifferent_iff_utility_eq hv, hup, hvp] at h
    exact h
  funext x y
  exact propext ((hu x y).trans (huv ▸ (hv x y).symm))

/-- The origin's class is always a singleton under strict monotonicity, so it is exceptional. -/
theorem strictlyMonotone_origin_class {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hc : Complete r) (hm : StrictlyMonotonePreference r) :
    IndifferenceClass r (OrthantZero k) = {OrthantZero k} := by
  ext x
  change Indifferent r x (OrthantZero k) ↔ x = OrthantZero k
  constructor
  · intro hx
    by_contra hne
    exact (hm x (OrthantZero k) x.property hne).2 hx.2
  · intro hx
    subst x
    exact ⟨complete_refl hc _, complete_refl hc _⟩

end Kreps.PreferenceProperties
