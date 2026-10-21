/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

/-!
# Lower-tail mass of a finite real measure

Analytic support for Kreps I, Problem 2.15. The cumulative lower-tail mass of a
finite measure is nondecreasing and upper semicontinuous. No normalization to a
probability measure is imposed. Continuity from above of the measure supplies
the upper-semicontinuity proof.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory
open scoped Topology

/-- The real-valued mass of the closed lower half-line for an arbitrary finite measure. -/
noncomputable def LowerDistribution (μ : Measure ℝ) (a : ℝ) : ℝ := μ.real (Set.Iic a)

/-- Enlarging a lower half-line increases its mass. -/
theorem lowerDistribution_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (LowerDistribution μ) :=
  fun _ _ hab => measureReal_mono (Set.Iic_subset_Iic.mpr hab)

/-- Lower-tail masses converge when cutoffs decrease geometrically to the target cutoff. -/
theorem lowerDistribution_tendsto_above (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => LowerDistribution μ (a + (1 / 2 : ℝ) ^ n))
      Filter.atTop (𝓝 (LowerDistribution μ a)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => a + (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Antitone (fun n : ℕ => a + (1 / 2 : ℝ) ^ n) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hi : (⋂ n : ℕ, Set.Iic (a + (1 / 2 : ℝ) ^ n)) = Set.Iic a := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ n : ℕ, x ≤ a + (1 / 2 : ℝ) ^ n := Set.mem_iInter.mp hx
      exact isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hx')
    · intro hx
      apply Set.mem_iInter.mpr
      intro n
      exact le_trans hx (le_add_of_nonneg_right
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n))
  have hμ := tendsto_measure_iInter_atTop (μ := μ)
    (fun _ : ℕ => isClosed_Iic.measurableSet.nullMeasurableSet)
    (fun i j hij => Set.Iic_subset_Iic.mpr (hm hij)) ⟨0, measure_ne_top μ _⟩
  rw [hi] at hμ
  simpa only [LowerDistribution, measureReal_def, Function.comp_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top μ (Set.Iic a))).tendsto.comp hμ

/-- The lower-tail mass function is upper semicontinuous, even when the measure has atoms. -/
theorem lowerDistribution_upperSemicontinuous (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UpperSemicontinuous (LowerDistribution μ) := by
  intro a b hb
  obtain ⟨n, hn⟩ := ((lowerDistribution_tendsto_above μ a).eventually
    (isOpen_Iio.mem_nhds hb)).exists
  have hnear : ∀ᶠ y in 𝓝 a, y < a + (1 / 2 : ℝ) ^ n :=
    isOpen_Iio.mem_nhds (lt_add_of_pos_right a (pow_pos (by norm_num) n))
  filter_upwards [hnear] with y hy
  exact (lowerDistribution_monotone μ hy.le).trans_lt hn

/-- If the cutoff has zero mass, approaching it from below gives the same lower-tail mass. -/
theorem lowerDistribution_tendsto_below (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) :
    Filter.Tendsto (fun n : ℕ => LowerDistribution μ (a - (1 / 2 : ℝ) ^ n))
      Filter.atTop (𝓝 (LowerDistribution μ a)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 a) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Monotone (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hi : (⋃ n : ℕ, Set.Iic (a - (1 / 2 : ℝ) ^ n)) = Set.Iio a := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact hn.trans_lt (sub_lt_self a (pow_pos (by norm_num) n))
    · intro hx
      obtain ⟨n, hn⟩ := (hlim.eventually (isOpen_Ioi.mem_nhds hx)).exists
      exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hμ := tendsto_measure_iUnion_atTop (μ := μ)
    (fun i j hij => Set.Iic_subset_Iic.mpr (hm hij))
  rw [hi, measure_congr (Iio_ae_eq_Iic' ha)] at hμ
  simpa only [LowerDistribution, measureReal_def, Function.comp_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top μ (Set.Iic a))).tendsto.comp hμ

/-- Absence of an atom supplies lower semicontinuity at the cutoff. -/
theorem lowerDistribution_lowerSemicontinuousAt (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) : LowerSemicontinuousAt (LowerDistribution μ) a := by
  intro b hb
  obtain ⟨n, hn⟩ := ((lowerDistribution_tendsto_below μ a ha).eventually
    (isOpen_Ioi.mem_nhds hb)).exists
  have hnear : ∀ᶠ y in 𝓝 a, a - (1 / 2 : ℝ) ^ n < y :=
    isOpen_Ioi.mem_nhds (sub_lt_self a (pow_pos (by norm_num) n))
  filter_upwards [hnear] with y hy
  exact hn.trans_le (lowerDistribution_monotone μ hy.le)

/-- The lower-tail function is continuous at cutoffs with zero singleton mass. -/
theorem lowerDistribution_continuousAt (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) : ContinuousAt (LowerDistribution μ) a :=
  continuousAt_iff_lower_upperSemicontinuousAt.mpr
    ⟨lowerDistribution_lowerSemicontinuousAt μ a ha, lowerDistribution_upperSemicontinuous μ a⟩

end Kreps.PreferenceProperties
