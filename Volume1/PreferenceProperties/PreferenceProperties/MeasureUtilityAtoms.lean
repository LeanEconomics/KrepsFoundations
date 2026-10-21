/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.OrthantMeasure
import PreferenceProperties.DiagonalBounds
import PreferenceProperties.Rationalization
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Atoms can make lower-contour utility discontinuous

Kreps I, Problem 2.15. Adding a unit atom at a nonminimal bundle creates a jump
along any sequence of strictly worse bundles converging to it. Starting with a
finite measure equivalent to ambient Lebesgue measure preserves the book's exact
positivity condition. The counterexample uses the ordinary increasing preference
on one commodity, so even strict monotonicity cannot exclude this problem.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {r : X → X → Prop}

/-- A unit atom adds one to lower-contour utility at its own reflexive rank. -/
theorem measureUtility_add_dirac_self (ν : Measure X) [IsFiniteMeasure ν]
    (p : X) (hp : r p p) :
    MeasureUtility (ν + Measure.dirac p) r p = MeasureUtility ν r p + 1 := by
  unfold MeasureUtility
  rw [measureReal_add_apply, Measure.dirac_real_apply_of_mem (s := NoBetterThan r p) hp]

/-- The same atom contributes nothing to a strictly lower rank. -/
theorem measureUtility_add_dirac_below [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] {p x : X} (hpx : Strict r p x) :
    MeasureUtility (ν + Measure.dirac p) r x = MeasureUtility ν r x := by
  unfold MeasureUtility
  rw [measureReal_add_apply, Measure.dirac_real_apply,
    Set.indicator_of_notMem (s := NoBetterThan r x) hpx.2, add_zero]

/-- Approaching an atom from strictly worse bundles witnesses a discontinuity. -/
theorem measureUtility_add_dirac_not_continuousAt [TopologicalSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsFiniteMeasure ν]
    (hr : Rational r) (p : X) (f : ℕ → X)
    (hf : Filter.Tendsto f Filter.atTop (𝓝 p)) (hfp : ∀ n, Strict r p (f n)) :
    ¬ ContinuousAt (MeasureUtility (ν + Measure.dirac p) r) p := by
  intro hc
  have hlim := hc.tendsto.comp hf
  have hbound : ∀ n,
      MeasureUtility (ν + Measure.dirac p) r (f n) ≤ MeasureUtility ν r p := by
    intro n
    rw [measureUtility_add_dirac_below ν (hfp n)]
    exact measureUtility_mono ν hr.2 (hfp n).1
  have hle := le_of_tendsto' hlim hbound
  rw [measureUtility_add_dirac_self ν p (complete_refl hr.1 p)] at hle
  linarith

/-- The numerical quantity of the single commodity. -/
def OneCommodityUtility (x : NonnegativeOrthant 1) : ℝ := x.val 0

/-- One unit of the single commodity, where the counterexample places its atom. -/
def OneCommodityUnit : NonnegativeOrthant 1 := Diagonal ⟨1, by norm_num⟩

/-- A sequence of quantities below one converging to one. -/
noncomputable def OneCommodityApproach (n : ℕ) : NonnegativeOrthant 1 :=
  Diagonal ⟨1 - (1 / 2 : ℝ) ^ n,
    sub_nonneg.mpr (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := n)
      (by norm_num) (by norm_num))⟩

/-- The ordinary one-commodity utility is continuous and strictly increasing. -/
theorem oneCommodityUtility_properties :
    Continuous OneCommodityUtility ∧ StrictMono OneCommodityUtility := by
  refine ⟨(continuous_apply 0).comp continuous_subtype_val, ?_⟩
  intro x y hxy
  have hle := hxy.le 0
  have hne : x.val 0 ≠ y.val 0 := by
    intro he
    apply hxy.ne
    apply Subtype.ext
    funext j
    fin_cases j
    exact he
  exact lt_of_le_of_ne hle hne

/-- The specified sequence converges to the atom bundle. -/
theorem oneCommodityApproach_tendsto :
    Filter.Tendsto OneCommodityApproach Filter.atTop (𝓝 OneCommodityUnit) := by
  have hreal : Filter.Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hsub : Filter.Tendsto (fun n : ℕ => (⟨1 - (1 / 2 : ℝ) ^ n,
      sub_nonneg.mpr (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := n)
        (by norm_num) (by norm_num))⟩ : Set.Ici (0 : ℝ)))
      Filter.atTop (𝓝 (⟨1, by norm_num⟩ : Set.Ici (0 : ℝ))) :=
    tendsto_subtype_rng.mpr hreal
  exact diagonal_continuous.continuousAt.tendsto.comp hsub

/-- Every quantity in the sequence is strictly worse than one unit. -/
theorem oneCommodityApproach_strict (n : ℕ) :
    Strict (UtilityPref OneCommodityUtility) OneCommodityUnit (OneCommodityApproach n) := by
  change (1 - (1 / 2 : ℝ) ^ n ≤ 1) ∧ ¬ (1 ≤ 1 - (1 / 2 : ℝ) ^ n)
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  constructor <;> linarith

/-- Pulling back a finite measure that dominates Lebesgue null sets preserves positive sets. -/
theorem orthant_comap_positive {k : ℕ} (ν : Measure (Fin k → ℝ))
    (hν : (volume : Measure (Fin k → ℝ)) ≪ ν)
    {A : Set (NonnegativeOrthant k)} (hA : 0 < OrthantLebesgue k A) :
    0 < ν.comap Subtype.val A := by
  have he : ν.comap Subtype.val A = ν (Subtype.val '' A) :=
    (MeasurableEmbedding.subtype_coe
      (isClosed_Ici (a := (0 : Fin k → ℝ))).measurableSet).comap_apply ν A
  rw [he]
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hvol := hν hzero
  rw [← orthantLebesgue_apply] at hvol
  exact ne_of_gt hA hvol

/-- **Problem 2.15:** the book's assumptions allow a discontinuous measure utility. -/
theorem problem_2_15_not_continuous :
    ∃ μ : Measure (NonnegativeOrthant 1), IsFiniteMeasure μ ∧
      (∀ A, MeasurableSet A → 0 < OrthantLebesgue 1 A → 0 < μ A) ∧
      Represents (MeasureUtility μ (UtilityPref OneCommodityUtility))
        (UtilityPref OneCommodityUtility) ∧
      UpperSemicontinuous (MeasureUtility μ (UtilityPref OneCommodityUtility)) ∧
      ¬ Continuous (MeasureUtility μ (UtilityPref OneCommodityUtility)) := by
  obtain ⟨ν, hfinite, hν, _⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (volume : Measure (Fin 1 → ℝ))
  let : IsFiniteMeasure ν := hfinite
  let ν' : Measure (NonnegativeOrthant 1) := ν.comap Subtype.val
  let μ := ν' + Measure.dirac OneCommodityUnit
  have hpos : ∀ A, MeasurableSet A → 0 < OrthantLebesgue 1 A → 0 < μ A := by
    intro A _ hA
    change 0 < (ν' + Measure.dirac OneCommodityUnit) A
    rw [Measure.add_apply]
    exact (orthant_comap_positive ν hν hA).trans_le (le_add_right le_rfl)
  have hr := proposition_1_3a OneCommodityUtility
  have hc := continuousPreference_of_continuous_utility oneCommodityUtility_properties.1
  obtain ⟨hrep, husc⟩ := problem_2_15 μ hpos hr hc
  refine ⟨μ, inferInstance, hpos, hrep, husc, ?_⟩
  intro hcont
  exact measureUtility_add_dirac_not_continuousAt ν' hr OneCommodityUnit
    OneCommodityApproach oneCommodityApproach_tendsto oneCommodityApproach_strict hcont.continuousAt

end Kreps.PreferenceProperties
