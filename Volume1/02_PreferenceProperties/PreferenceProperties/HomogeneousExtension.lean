/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.HomotheticRays
import PreferenceProperties.RepresentationExtension

/-!
# Homogeneous utility from reference rays

The extension construction for Proposition 2.19 preserves homogeneity when the
reference curve and its utility scale compatibly. This module completes the
cases where every bundle is weakly above the origin or every bundle is weakly
below it. The case with ranks on both sides uses a signed reference curve.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- The scalar itself represents preference along a positive reference ray. -/
theorem positive_ray_represents (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) :
    Represents (fun t : ℝ≥0 => (t : ℝ)) (fun a b => r (ScaleBundle a p) (ScaleBundle b p)) := by
  obtain ⟨v, hv⟩ := proposition_1_15 k hr hc
  have hs := positive_ray_strictMono hr hc hh hv hp
  intro a b
  exact (hv _ _).trans (hs.le_iff_le.trans NNReal.coe_le_coe.symm)

/-- A scale-compatible reference representation extends to a homogeneous utility. -/
theorem liftedUtility_homogeneous {Y : Type*} (hr : Rational r)
    (hh : HomotheticPreference r) (f : Y → NonnegativeOrthant k) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (σ : ℝ≥0 → Y → Y)
    (hfScale : ∀ t y, ScaleBundle t (f y) = f (σ t y))
    (hvScale : ∀ t y, v (σ t y) = (t : ℝ) * v y) :
    HomogeneousUtility (LiftedUtility f v hcover) := by
  intro t x
  let y := Classical.choose (hcover x)
  have hy : Indifferent r (f y) x := Classical.choose_spec (hcover x)
  have hscaled : Indifferent r (f (σ t y)) (ScaleBundle t x) := by
    rw [← hfScale]
    exact ⟨hh _ _ t hy.1, hh _ _ t hy.2⟩
  have hu := liftedUtility_represents hr f v hcover hv
  calc
    LiftedUtility f v hcover (ScaleBundle t x) = LiftedUtility f v hcover (f (σ t y)) :=
      le_antisymm ((hu _ _).mp hscaled.1) ((hu _ _).mp hscaled.2)
    _ = v (σ t y) := liftedUtility_agrees f v hcover hv _
    _ = (t : ℝ) * v y := hvScale t y
    _ = (t : ℝ) * LiftedUtility f v hcover x := rfl

/-- A positive reference represents all ranks when every bundle is weakly above the origin. -/
theorem homogeneous_representation_above_origin (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k))
    (hall : ∀ x, r x (OrthantZero k)) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  let f := fun t : ℝ≥0 => ScaleBundle t p
  let v := fun t : ℝ≥0 => (t : ℝ)
  have hcover (x : NonnegativeOrthant k) : ∃ t, Indifferent r (f t) x :=
    positive_ray_indifference hr hc hh hp (hall x)
  have hv : Represents v (fun a b => r (f a) (f b)) := positive_ray_represents hr hc hh hp
  refine ⟨LiftedUtility f v hcover, liftedUtility_represents hr f v hcover hv,
    liftedUtility_continuous hr hc f v hcover hv NNReal.continuous_coe, ?_⟩
  apply liftedUtility_homogeneous hr hh f v hcover hv (fun t s => t * s)
  · intro t s
    exact (scaleBundle_mul t s p).symm
  · intro t s
    exact NNReal.coe_mul t s

/-- Reversing all comparisons preserves rationality. -/
theorem reversePreference_rational (hr : Rational r) : Rational (fun x y => r y x) :=
  ⟨fun x y => hr.1 y x, fun x y z hxy hyz => hr.2 z y x hyz hxy⟩

/-- Reversing all comparisons preserves continuity. -/
theorem reversePreference_continuous (hc : ContinuousPreference r) :
    ContinuousPreference (fun x y => r y x) :=
  hc.preimage continuous_swap

/-- Reversing all comparisons preserves homotheticity. -/
theorem reversePreference_homothetic (hh : HomotheticPreference r) :
    HomotheticPreference (fun x y => r y x) := fun x y t h => hh y x t h

/-- Negating a utility for reversed preference recovers the original preference. -/
theorem neg_utility_represents {u : NonnegativeOrthant k → ℝ}
    (hu : Represents u (fun x y => r y x)) : Represents (fun x => -u x) r := by
  intro x y
  change r x y ↔ -u y ≤ -u x
  rw [neg_le_neg_iff]
  exact hu y x

/-- Negating a homogeneous utility preserves degree one. -/
theorem neg_utility_homogeneous {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : HomogeneousUtility (fun x => -u x) := by
  intro t x
  change -u (ScaleBundle t x) = (t : ℝ) * -u x
  rw [hh]
  ring

/-- A negative reference handles the case in which every rank lies below the origin. -/
theorem homogeneous_representation_below_origin (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p)
    (hall : ∀ x, r (OrthantZero k) x) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  obtain ⟨u, hu, huc, huh⟩ := homogeneous_representation_above_origin
    (reversePreference_rational hr) (reversePreference_continuous hc)
    (reversePreference_homothetic hh) hp hall
  exact ⟨fun x => -u x, neg_utility_represents hu, huc.neg, neg_utility_homogeneous huh⟩

/-- If every bundle is indifferent to the origin, constant zero is a homogeneous representation. -/
theorem homogeneous_representation_indifferent (hr : Rational r)
    (hall : ∀ x, Indifferent r x (OrthantZero k)) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  refine ⟨fun _ => 0, ?_, continuous_const, ?_⟩
  · intro x y
    exact iff_of_true (hr.2 x (OrthantZero k) y (hall x).1 (hall y).2) le_rfl
  · intro t x
    simp

end Kreps.PreferenceProperties
