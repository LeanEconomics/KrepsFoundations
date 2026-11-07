/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveScaleUniqueness
import PreferenceProperties.SubutilityContinuity

/-!
# Calibrating overlapping additive charts

Preparation for Kreps I, Proposition 2.14. The affine uniqueness theorem is
transported from numerical score intervals back to arbitrary connected ordered
coordinate domains. Fixing one nonzero increment in a companion coordinate
then forces overlap transitions to be translations, synchronizing the units
of the two coordinate scales.
-/

namespace Kreps.PreferenceProperties

/-- Two strictly increasing coordinate scales represent the same coordinate order. -/
theorem strictMono_coordinate_represents {A : Type*} [LinearOrder A]
    {w v : A → ℝ} (hw : StrictMono w) (hv : StrictMono v) :
    Represents v (UtilityPref w) := by
  intro x y
  exact hw.le_iff_le.trans hv.le_iff_le.symm

/-- Equivalent additive charts on two connected ordered blocks have one positive affine slope. -/
theorem pair_chart_positive_affine_unique {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d) :
    ∃ slope β γ : ℝ, 0 < slope ∧ (∀ x, v x = slope * w x + β) ∧
      ∀ y, v' y = slope * w' y + γ := by
  have hwr : Represents w (UtilityPref w) := fun _ _ => Iff.rfl
  have hvr := strictMono_coordinate_represents hwm hvm
  have hwr' : Represents w' (UtilityPref w') := fun _ _ => Iff.rfl
  have hvr' := strictMono_coordinate_represents hwm' hvm'
  have hpc : PreservesPairSumEquality (UtilityTransform w v) (UtilityTransform w' v')
      (Set.range w) (Set.range w') := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ he
    simpa only [utilityTransform_apply hwr hvr, utilityTransform_apply hwr' hvr']
      using hp x x' y y' he
  have hfc : ContinuousOn (UtilityTransform w v) (Set.range w) :=
    continuousOn_iff_continuous_domRestrict.mpr (utilityTransform_continuous_range hwr hvr hw hv)
  have hgc : ContinuousOn (UtilityTransform w' v') (Set.range w') :=
    continuousOn_iff_continuous_domRestrict.mpr
      (utilityTransform_continuous_range hwr' hvr' hw' hv')
  obtain ⟨slope, β, γ, hslope, hf, hg⟩ := pair_additive_positive_affine_unique hpc
    (isPreconnected_range hw).ordConnected (isPreconnected_range hw').ordConnected hfc hgc
    (utilityTransform_strictMonoOn hwr hvr) ⟨a, rfl⟩ ⟨b, rfl⟩ (hwm hab)
    ⟨c, rfl⟩ ⟨d, rfl⟩ (hwm' hcd)
  refine ⟨slope, β, γ, hslope, fun x => ?_, fun y => ?_⟩
  · simpa only [utilityTransform_apply hwr hvr] using hf (w x) ⟨x, rfl⟩
  · simpa only [utilityTransform_apply hwr' hvr'] using hg (w' y) ⟨y, rfl⟩

/-- Equal companion increments force the common affine slope to be one. -/
theorem common_affine_slope_eq_one {A B : Type*} {w v : A → ℝ} {w' v' : B → ℝ}
    {slope β γ : ℝ} (hv : ∀ x, v x = slope * w x + β) (hv' : ∀ y, v' y = slope * w' y + γ)
    {c d : B} (hcd : w' c < w' d) (hunit : v' d - v' c = w' d - w' c) :
    slope = 1 ∧ (∀ x, v x = w x + β) ∧ ∀ y, v' y = w' y + γ := by
  have hc := hv' c
  have hd := hv' d
  have hslope : slope = 1 := by nlinarith
  exact ⟨hslope, fun x => by simpa only [hslope, one_mul] using hv x,
    fun y => by simpa only [hslope, one_mul] using hv' y⟩

/-- Calibrating one companion increment leaves only coordinate translations on an overlap. -/
theorem pair_chart_translation_of_companion_increment {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d)
    (hunit : v' d - v' c = w' d - w' c) :
    ∃ β γ : ℝ, (∀ x, v x = w x + β) ∧ ∀ y, v' y = w' y + γ := by
  obtain ⟨slope, β, γ, _, hf, hg⟩ := pair_chart_positive_affine_unique hw hv hw' hv'
    hwm hvm hwm' hvm' hp hab hcd
  have h := common_affine_slope_eq_one hf hg (hwm' hcd) hunit
  exact ⟨β, γ, h.2⟩

/-- Matching a companion at two levels fixes its offset too; one target baseline fixes the rest. -/
theorem pair_chart_identity_of_companion_and_baseline {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d)
    (hc : v' c = w' c) (hd : v' d = w' d) (ha : v a = w a) :
    (∀ x, v x = w x) ∧ ∀ y, v' y = w' y := by
  obtain ⟨β, γ, hf, hg⟩ := pair_chart_translation_of_companion_increment hw hv hw' hv'
    hwm hvm hwm' hvm' hp hab hcd (by rw [hc, hd])
  have hβ : β = 0 := by have h := hf a; linarith
  have hγ : γ = 0 := by have h := hg c; linarith
  exact ⟨fun x => by simpa only [hβ, add_zero] using hf x,
    fun y => by simpa only [hγ, add_zero] using hg y⟩

end Kreps.PreferenceProperties
