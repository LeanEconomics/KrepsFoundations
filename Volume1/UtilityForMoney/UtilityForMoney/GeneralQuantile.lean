/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Inverse-CDF sampling for general probability laws

Kreps I, Problem 6.5(b), footnote 15, p. 141. For any probability measure on
the real line, the generalized inverse of its right-continuous distribution
function pushes a uniform draw forward to the original law. The construction
uses the open unit interval, whose omitted endpoints have zero uniform mass.
-/

namespace Kreps.UtilityForMoney

open Filter MeasureTheory ProbabilityTheory Set Topology

/-- Lower quantile of a real probability law, with a default at zero-mass endpoints. -/
noncomputable def GeneralQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf {x : ℝ | u ≤ cdf μ x} else 0

/-- The basic inverse-CDF equivalence at every draw strictly between zero and one. -/
theorem generalQuantile_le_iff (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    GeneralQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  let A : Set ℝ := {y | u ≤ cdf μ y}
  have hne : A.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually (isOpen_Ioi.mem_nhds hu.2)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow A := by
    obtain ⟨z, hz⟩ := ((tendsto_cdf_atBot μ).eventually (isOpen_Iio.mem_nhds hu.1)).exists
    refine ⟨z, fun y hy => ?_⟩
    change u ≤ cdf μ y at hy
    by_contra! h
    exact (not_le_of_gt hz) (hy.trans ((monotone_cdf μ) h.le))
  have hinf : u ≤ cdf μ (sInf A) := by
    apply ge_of_tendsto (((cdf μ).right_continuous (sInf A)).mono Set.Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : sInf A < y := hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy'
    exact hz.trans ((monotone_cdf μ) hzy.le)
  rw [GeneralQuantile, ite_eq_left hu]
  exact ⟨fun h => hinf.trans ((monotone_cdf μ) h), fun h => csInf_le hb h⟩

/-- The extended quantile is a measurable real random variable. -/
theorem generalQuantile_measurable (μ : Measure ℝ) : Measurable (GeneralQuantile μ) := by
  apply measurable_of_Iic
  intro x
  have hin (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) := generalQuantile_le_iff μ hu x
  by_cases hx : 0 ≤ x
  · have he : GeneralQuantile μ ⁻¹' Iic x =
        (Ioo 0 1 ∩ Iic (cdf μ x)) ∪ (Ioo 0 1)ᶜ := by
      ext u
      by_cases h : u ∈ Ioo (0 : ℝ) 1
      · simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, h, true_and, mem_compl_iff,
          not_true_eq_false, or_false, hin u h]
      · simp [GeneralQuantile, h, hx]
    rw [he]
    exact (measurableSet_Ioo.inter measurableSet_Iic).union measurableSet_Ioo.compl
  · have he : GeneralQuantile μ ⁻¹' Iic x = Ioo 0 1 ∩ Iic (cdf μ x) := by
      ext u
      by_cases h : u ∈ Ioo (0 : ℝ) 1
      · simp only [mem_preimage, mem_Iic, mem_inter_iff, h, true_and, hin u h]
      · simp [GeneralQuantile, h, hx]
    rw [he]
    exact measurableSet_Ioo.inter measurableSet_Iic

/-- **Footnote 15:** the generalized inverse pushes uniform probability to an arbitrary real law. -/
theorem generalQuantile_uniform_law (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (GeneralQuantile μ) = μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ioo]⟩
  have : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map (GeneralQuantile μ)) :=
    (Measure.isProbabilityMeasure_map_iff (generalQuantile_measurable μ).aemeasurable).mpr
      inferInstance
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (generalQuantile_measurable μ) measurableSet_Iic,
    Measure.restrict_apply ((generalQuantile_measurable μ) measurableSet_Iic), ← ofReal_cdf]
  have he : (GeneralQuantile μ ⁻¹' Iic x) ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext u
    by_cases h : u ∈ Ioo (0 : ℝ) 1
    · simp only [mem_inter_iff, mem_preimage, mem_Iic, h, and_true, true_and,
        generalQuantile_le_iff μ h]
    · simp [h]
  rw [he]
  rcases (cdf_le_one μ x).eq_or_lt with h | h
  · rw [h, inter_eq_left.mpr (fun _ hu => hu.2.le), Real.volume_Ioo]
    norm_num
  · have ht : Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) = Ioc 0 (cdf μ x) := by
      ext t
      exact ⟨fun ht => ⟨ht.1.1, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.trans_lt h⟩, ht.2⟩⟩
    rw [ht, Real.volume_Ioc, sub_zero]

end Kreps.UtilityForMoney
