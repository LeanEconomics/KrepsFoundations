/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CoordinateChartFamily
import PreferenceProperties.CompanionCoordinateGlobalization

/-!
# Global coordinate scales in common companion units

Pointwise local additive existence, fixed companions and translation gluing
produce a continuous strictly increasing scale on an entire open coordinate
interval. The accompanying chart and companion identities retain the common
cardinal unit needed to synchronize different coordinates.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

variable (V) (z : ∀ i, S i) (seed : ScalarAdditiveChart V)

/-- A global coordinate scale, with its actual local charts and two companion calibrations. -/
structure GlobalCoordinateScale (i j k : I) where
  family : CoordinateChartFamily V z seed i
  slope : S i → ℝ
  positive : ∀ x, 0 < slope x
  seed_unit : slope (z i) = 1
  scale : ℝ → ℝ
  continuous : ContinuousOn scale (S i)
  increasing : StrictMonoOn scale (S i)
  seed_agrees : ∀ x ∈ seed.domain i, scale x = seed.coord i x
  chart_agrees : ∀ p, ∃ B : ℝ, ∀ x ∈ (family.chart p).domain i,
    scale x = (family.chart p).coord i x / slope p + B
  companion_calibration : ∀ q, q = j ∨ q = k → ∀ p, ∃ B : ℝ,
    ∀ x ∈ seed.domain q ∩ (family.chart p).domain q,
      (family.chart p).coord q x = slope p * seed.coord q x + B

variable {V}

/-- All local additive charts glue to a target scale while retaining both fixed companions. -/
theorem exists_globalCoordinateScale
    (hl : ∀ z : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i)
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (z : ∀ i, S i) (seed : ScalarAdditiveChart V) (hz : ∀ i, (z i).val ∈ seed.domain i)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nonempty (GlobalCoordinateScale V z seed i j k) := by
  classical
  obtain ⟨F⟩ := exists_coordinateChartFamily hl z seed hz i
  let G := F.toCompanionFamily hs hij hik hjk
  obtain ⟨slope, β, γ, hpos, hunit, hf, hg⟩ := G.exists_calibration (z i)
  have hne : (G.domain (z i) 0).Nonempty := by
    refine ⟨(z i).val, ?_⟩
    change (z i).val ∈ (F.chart (z i)).domain i
    rw [F.seed_eq]
    exact hz i
  obtain ⟨f, hfc, hfm, hseed, hchart⟩ := G.globalize_target_of_calibration (hS i)
    (F.companion_target_subset hs hij hik hjk) (F.companion_target_cover hs hij hik hjk)
    (z i) hne hpos hunit hf
  refine ⟨{
    family := F
    slope := slope
    positive := hpos
    seed_unit := hunit
    scale := f
    continuous := hfc
    increasing := hfm
    seed_agrees := ?_
    chart_agrees := hchart
    companion_calibration := ?_ }⟩
  · simpa only [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex,
      Matrix.cons_val_zero, F.seed_eq] using hseed
  · intro q hq p
    rcases hq with rfl | rfl
    · refine ⟨β p, ?_⟩
      simpa [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex, F.seed_eq]
        using hf p
    · refine ⟨γ p, ?_⟩
      simpa [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex, F.seed_eq]
        using hg p

end Kreps.PreferenceProperties
