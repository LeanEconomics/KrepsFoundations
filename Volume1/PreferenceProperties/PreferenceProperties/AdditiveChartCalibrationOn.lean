/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveChartCalibration

/-!
# Affine calibration on real coordinate domains

The chart calibration lemmas are expressed for ambient real functions on
interval domains. This matches the coordinate atlas used to extend the local
additive scales in Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

/-- A nonempty open real set contains a strictly ordered pair. -/
theorem open_real_set_has_pair {S : Set ℝ} (hS : IsOpen S) {x : ℝ} (hx : x ∈ S) :
    ∃ a ∈ S, ∃ b ∈ S, a < b := by
  obtain ⟨b, hxb, hb⟩ := exists_Ico_subset_of_mem_nhds (hS.mem_nhds hx) (exists_gt x)
  refine ⟨x, hx, (x + b) / 2, hb ⟨by linarith, by linarith⟩, by linarith⟩

/-- Positive affine uniqueness for ambient scales restricted to two real intervals. -/
theorem pair_chart_positive_affine_unique_on {S T : Set ℝ} (hS : S.OrdConnected)
    (hT : T.OrdConnected) {w v w' v' : ℝ → ℝ}
    (hw : ContinuousOn w S) (hv : ContinuousOn v S)
    (hw' : ContinuousOn w' T) (hv' : ContinuousOn v' T)
    (hwm : StrictMonoOn w S) (hvm : StrictMonoOn v S)
    (hwm' : StrictMonoOn w' T) (hvm' : StrictMonoOn v' T)
    (hp : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
      w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ slope β γ : ℝ, 0 < slope ∧ (∀ x ∈ S, v x = slope * w x + β) ∧
      ∀ y ∈ T, v' y = slope * w' y + γ := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hT.isPreconnected
  obtain ⟨slope, β, γ, hpos, hf, hg⟩ := pair_chart_positive_affine_unique
    (continuousOn_iff_continuous_domRestrict.mp hw) (continuousOn_iff_continuous_domRestrict.mp hv)
    (continuousOn_iff_continuous_domRestrict.mp hw')
    (continuousOn_iff_continuous_domRestrict.mp hv')
    (fun x y hxy => hwm x.property y.property hxy)
    (fun x y hxy => hvm x.property y.property hxy)
    (fun x y hxy => hwm' x.property y.property hxy)
    (fun x y hxy => hvm' x.property y.property hxy)
    (fun x x' y y' => hp x.val x.property x'.val x'.property y.val y.property y'.val y'.property)
    (show (⟨a, ha⟩ : S) < ⟨b, hb⟩ from hab) (show (⟨c, hc⟩ : T) < ⟨d, hd⟩ from hcd)
  exact ⟨slope, β, γ, hpos, fun x hx => hf ⟨x, hx⟩, fun y hy => hg ⟨y, hy⟩⟩

/-- Fixing a companion increment forces translation transitions on two real intervals. -/
theorem pair_chart_translation_on {S T : Set ℝ} (hS : S.OrdConnected)
    (hT : T.OrdConnected) {w v w' v' : ℝ → ℝ}
    (hw : ContinuousOn w S) (hv : ContinuousOn v S)
    (hw' : ContinuousOn w' T) (hv' : ContinuousOn v' T)
    (hwm : StrictMonoOn w S) (hvm : StrictMonoOn v S)
    (hwm' : StrictMonoOn w' T) (hvm' : StrictMonoOn v' T)
    (hp : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
      w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d)
    (hunit : v' d - v' c = w' d - w' c) :
    ∃ β γ : ℝ, (∀ x ∈ S, v x = w x + β) ∧ ∀ y ∈ T, v' y = w' y + γ := by
  obtain ⟨slope, β, γ, _, hf, hg⟩ := pair_chart_positive_affine_unique_on hS hT hw hv hw' hv'
    hwm hvm hwm' hvm' hp ha hb hab hc hd hcd
  have hpc := hg c hc
  have hpd := hg d hd
  have hlt := hwm' hc hd hcd
  have hscale : slope = 1 := by nlinarith
  exact ⟨β, γ, fun x hx => by simpa only [hscale, one_mul] using hf x hx,
    fun y hy => by simpa only [hscale, one_mul] using hg y hy⟩

end Kreps.PreferenceProperties
