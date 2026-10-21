/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveChartCalibrationOn

/-!
# Fixed-companion calibration of coordinate charts

Preparation for Kreps I, Proposition 2.14. Along a varying target coordinate,
keep two other essential coordinates at fixed reference values. Their chart
domains always overlap the seed companions. Pair uniqueness fixes a positive
scale for every chart; after dividing by it, all target-coordinate overlap
transitions are translations. The fixed companions synchronize cardinal units.
-/

namespace Kreps.PreferenceProperties

/-- A target-coordinate chart family with two fixed essential companion coordinates. -/
structure CompanionChartFamily (K : Type*) where
  domain : K → Fin 3 → Set ℝ
  coord : K → Fin 3 → ℝ → ℝ
  open_domain : ∀ k i, IsOpen (domain k i)
  interval : ∀ k i, (domain k i).OrdConnected
  continuous : ∀ k i, ContinuousOn (coord k i) (domain k i)
  increasing : ∀ k i, StrictMonoOn (coord k i) (domain k i)
  firstReference : ℝ
  secondReference : ℝ
  first_mem : ∀ k, firstReference ∈ domain k 1
  second_mem : ∀ k, secondReference ∈ domain k 2
  pair_compatible : ∀ k l i j, i ≠ j →
    ∀ x ∈ domain k i ∩ domain l i, ∀ x' ∈ domain k i ∩ domain l i,
    ∀ y ∈ domain k j ∩ domain l j, ∀ y' ∈ domain k j ∩ domain l j,
      coord k i x + coord k j y = coord k i x' + coord k j y' →
        coord l i x + coord l j y = coord l i x' + coord l j y'

variable {K : Type*}

/-- Comparing the two fixed companions with a seed chart calibrates every chart's common unit. -/
theorem CompanionChartFamily.exists_calibration (F : CompanionChartFamily K) (seed : K) :
    ∃ slope firstOffset secondOffset : K → ℝ,
      (∀ k, 0 < slope k) ∧ slope seed = 1 ∧
      (∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
        F.coord k 1 x = slope k * F.coord seed 1 x + firstOffset k) ∧
      ∀ k x, x ∈ F.domain seed 2 ∩ F.domain k 2 →
        F.coord k 2 x = slope k * F.coord seed 2 x + secondOffset k := by
  classical
  have hcal (k : K) : ∃ slope firstOffset secondOffset : ℝ,
      0 < slope ∧ (k = seed → slope = 1) ∧
      (∀ x ∈ F.domain seed 1 ∩ F.domain k 1,
        F.coord k 1 x = slope * F.coord seed 1 x + firstOffset) ∧
      ∀ x ∈ F.domain seed 2 ∩ F.domain k 2,
        F.coord k 2 x = slope * F.coord seed 2 x + secondOffset := by
    by_cases hk : k = seed
    · subst k
      exact ⟨1, 0, 0, by norm_num, fun _ => rfl, by simp, by simp⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
        ((F.open_domain seed 1).inter (F.open_domain k 1)) ⟨F.first_mem seed, F.first_mem k⟩
      obtain ⟨c, hc, d, hd, hcd⟩ := open_real_set_has_pair
        ((F.open_domain seed 2).inter (F.open_domain k 2)) ⟨F.second_mem seed, F.second_mem k⟩
      obtain ⟨slope, β, γ, hpos, hf, hg⟩ := pair_chart_positive_affine_unique_on
        ((F.interval seed 1).inter (F.interval k 1))
        ((F.interval seed 2).inter (F.interval k 2))
        ((F.continuous seed 1).mono Set.inter_subset_left)
        ((F.continuous k 1).mono Set.inter_subset_right)
        ((F.continuous seed 2).mono Set.inter_subset_left)
        ((F.continuous k 2).mono Set.inter_subset_right)
        ((F.increasing seed 1).mono Set.inter_subset_left)
        ((F.increasing k 1).mono Set.inter_subset_right)
        ((F.increasing seed 2).mono Set.inter_subset_left)
        ((F.increasing k 2).mono Set.inter_subset_right)
        (F.pair_compatible seed k 1 2 (by decide)) ha hb hab hc hd hcd
      exact ⟨slope, β, γ, hpos, fun h => (hk h).elim, hf, hg⟩
  choose slope β γ hpos hseed hf hg using hcal
  exact ⟨slope, β, γ, hpos, hseed seed rfl, hf, hg⟩

/-- Calibrated companion scores agree with the seed up to translations. -/
theorem CompanionChartFamily.calibrated_companion (F : CompanionChartFamily K) (seed : K)
    {slope offset : K → ℝ} (hpos : ∀ k, 0 < slope k)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k)
    (k : K) (x : ℝ) (hx : x ∈ F.domain seed 1 ∩ F.domain k 1) :
    F.coord k 1 x / slope k = F.coord seed 1 x + offset k / slope k := by
  rw [hc k x hx, add_div]
  congr 1
  field_simp [(hpos k).ne']

/-- Once companions fix the units, every target overlap has a translation transition. -/
theorem CompanionChartFamily.calibrated_target_transition
    (F : CompanionChartFamily K) (seed : K) {slope offset : K → ℝ}
    (hpos : ∀ k, 0 < slope k)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k) (k l : K) :
    ∃ β : ℝ, ∀ x ∈ F.domain k 0 ∩ F.domain l 0,
      F.coord k 0 x / slope k = F.coord l 0 x / slope l + β := by
  classical
  by_cases hne : (F.domain k 0 ∩ F.domain l 0).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
      ((F.open_domain k 0).inter (F.open_domain l 0)) hx₀
    let T := (F.domain seed 1 ∩ F.domain k 1) ∩ F.domain l 1
    have hTo : IsOpen T := ((F.open_domain seed 1).inter (F.open_domain k 1)).inter
      (F.open_domain l 1)
    have hTi : T.OrdConnected := ((F.interval seed 1).inter (F.interval k 1)).inter
      (F.interval l 1)
    obtain ⟨c, hcm, d, hdm, hcd⟩ := open_real_set_has_pair hTo
      ⟨⟨F.first_mem seed, F.first_mem k⟩, F.first_mem l⟩
    have hcf (r : K) (i : Fin 3) :
        ContinuousOn (fun x => F.coord r i x / slope r) (F.domain r i) :=
      (F.continuous r i).div_const _
    have hmf (r : K) (i : Fin 3) :
        StrictMonoOn (fun x => F.coord r i x / slope r) (F.domain r i) := by
      intro x hx y hy hxy
      exact (div_lt_div_iff_of_pos_right (hpos r)).mpr (F.increasing r i hx hy hxy)
    have hunit : F.coord k 1 d / slope k - F.coord k 1 c / slope k =
        F.coord l 1 d / slope l - F.coord l 1 c / slope l := by
      rw [F.calibrated_companion seed hpos hc k d hdm.1,
        F.calibrated_companion seed hpos hc k c hcm.1,
        F.calibrated_companion seed hpos hc l d ⟨hdm.1.1, hdm.2⟩,
        F.calibrated_companion seed hpos hc l c ⟨hcm.1.1, hcm.2⟩]
      ring
    have hp : ∀ x ∈ F.domain k 0 ∩ F.domain l 0,
        ∀ x' ∈ F.domain k 0 ∩ F.domain l 0, ∀ y ∈ T, ∀ y' ∈ T,
        F.coord l 0 x / slope l + F.coord l 1 y / slope l =
          F.coord l 0 x' / slope l + F.coord l 1 y' / slope l →
        F.coord k 0 x / slope k + F.coord k 1 y / slope k =
          F.coord k 0 x' / slope k + F.coord k 1 y' / slope k := by
      intro x hx x' hx' y hy y' hy' he
      rw [← add_div, ← add_div] at he
      have hraw := (div_left_inj' (hpos l).ne').mp he
      have h := F.pair_compatible l k 0 1 (by decide) x ⟨hx.2, hx.1⟩ x' ⟨hx'.2, hx'.1⟩
        y ⟨hy.2, hy.1.2⟩ y' ⟨hy'.2, hy'.1.2⟩ hraw
      rw [← add_div, ← add_div, h]
    obtain ⟨β, _, hβ, _⟩ := pair_chart_translation_on
      ((F.interval k 0).inter (F.interval l 0)) hTi
      ((hcf l 0).mono Set.inter_subset_right) ((hcf k 0).mono Set.inter_subset_left)
      ((hcf l 1).mono (fun _ hx => hx.2)) ((hcf k 1).mono (fun _ hx => hx.1.2))
      ((hmf l 0).mono Set.inter_subset_right) ((hmf k 0).mono Set.inter_subset_left)
      ((hmf l 1).mono (fun _ hx => hx.2)) ((hmf k 1).mono (fun _ hx => hx.1.2))
      hp ha hb hab hcm hdm hcd hunit
    exact ⟨β, hβ⟩
  · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩

end Kreps.PreferenceProperties
