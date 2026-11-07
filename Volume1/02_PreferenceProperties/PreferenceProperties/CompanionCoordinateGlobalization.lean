/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CompanionChartCalibration
import PreferenceProperties.TranslationIntervalAtlas

/-!
# Global coordinates from companion-calibrated charts

For Proposition 2.14, two fixed essential companion coordinates determine cardinal units for
all local charts along a target interval. Translation-atlas gluing then gives a continuous
increasing target scale using those units throughout the interval.
-/

namespace Kreps.PreferenceProperties

/-- A fixed companion calibration glues all target charts without changing their units. -/
theorem CompanionChartFamily.globalize_target_of_calibration {K : Type*}
    (F : CompanionChartFamily K) {S : Set ℝ} (hS : S.OrdConnected)
    (hsub : ∀ k, F.domain k 0 ⊆ S) (hcover : ∀ x ∈ S, ∃ k, x ∈ F.domain k 0)
    (seed : K) (hne : (F.domain seed 0).Nonempty) {slope offset : K → ℝ}
    (hpos : ∀ k, 0 < slope k) (hunit : slope seed = 1)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ F.domain seed 0, f x = F.coord seed 0 x) ∧
      ∀ k, ∃ B : ℝ, ∀ x ∈ F.domain k 0, f x = F.coord k 0 x / slope k + B := by
  have ht := F.calibrated_target_transition seed hpos hc
  let a : PositiveAffineIntervalAtlas K S := {
    domain := fun k => F.domain k 0
    coord := fun k x => F.coord k 0 x / slope k
    isOpen := fun k => F.open_domain k 0
    interval := fun k => F.interval k 0
    subset := hsub
    cover := hcover
    continuous := fun k => (F.continuous k 0).div_const _
    increasing := fun k _ hx _ hy hxy =>
      (div_lt_div_iff_of_pos_right (hpos k)).mpr (F.increasing k 0 hx hy hxy)
    transition := fun k l => by
      obtain ⟨B, hB⟩ := ht k l
      exact ⟨1, B, zero_lt_one, fun x hx => by simpa only [one_mul] using hB x hx⟩ }
  obtain ⟨f, hfc, hfm, hseed, hf⟩ := a.globalize_translations hS seed hne ht
  refine ⟨f, hfc, hfm, ?_, hf⟩
  intro x hx
  simpa only [a, hunit, div_one] using hseed x hx

/-- Two fixed companions provide both the calibration and a global increasing target scale. -/
theorem CompanionChartFamily.exists_global_target {K : Type*}
    (F : CompanionChartFamily K) {S : Set ℝ} (hS : S.OrdConnected)
    (hsub : ∀ k, F.domain k 0 ⊆ S) (hcover : ∀ x ∈ S, ∃ k, x ∈ F.domain k 0)
    (seed : K) (hne : (F.domain seed 0).Nonempty) :
    ∃ (slope : K → ℝ) (f : ℝ → ℝ), (∀ k, 0 < slope k) ∧ slope seed = 1 ∧
      ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ F.domain seed 0, f x = F.coord seed 0 x) ∧
      ∀ k, ∃ B : ℝ, ∀ x ∈ F.domain k 0, f x = F.coord k 0 x / slope k + B := by
  obtain ⟨slope, offset, _, hpos, hunit, hc, _⟩ := F.exists_calibration seed
  obtain ⟨f, hfc, hfm, hseed, hf⟩ :=
    F.globalize_target_of_calibration hS hsub hcover seed hne hpos hunit hc
  exact ⟨slope, f, hpos, hunit, hfc, hfm, hseed, hf⟩

end Kreps.PreferenceProperties
