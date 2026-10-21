/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.FiniteMeasureDistribution
import PreferenceProperties.HomotheticIdentification
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Utility from the measure of a lower preference contour

Ingredients for Kreps I, Problem 2.15. A finite measure positive on every nonempty
open set gives a representation on a connected domain. A continuous numerical
representation identifies the construction with a cumulative distribution,
which proves upper semicontinuity. Null indifference classes suffice for continuity.
The book's Lebesgue-positivity assumption is handled by a separate orthant bridge.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {r : X → X → Prop}

/-- The finite-measure construction `u(x) = μ(NBT(x))` in Problem 2.15. -/
noncomputable def MeasureUtility (μ : Measure X) (r : X → X → Prop) (x : X) : ℝ :=
  μ.real (NoBetterThan r x)

/-- Transitivity gives inclusion of lower contours and hence weakly increasing measure utility. -/
theorem measureUtility_mono (μ : Measure X) [IsFiniteMeasure μ] (ht : TransitivePref r)
    {x y : X} (hxy : r x y) : MeasureUtility μ r y ≤ MeasureUtility μ r x :=
  measureReal_mono (fun z hz => ht x y z hxy hz)

/-- A strict rank interval contains a nonempty open set and therefore positive measure. -/
theorem measureUtility_strict [TopologicalSpace X] [OpensMeasurableSpace X]
    [PreconnectedSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) {x y : X} (hxy : Strict r x y) :
    MeasureUtility μ r y < MeasureUtility μ r x := by
  obtain ⟨z, hxz, hzy⟩ := exists_strict_between hr hc hxy
  have ho := (continuousPreference_openStrictContours hc y).1.inter
    (continuousPreference_openStrictContours hc x).2
  have hpos := ho.measure_pos μ ⟨z, hzy, hxz⟩
  have hsub : StrictlyBetterThan r y ∩ StrictlyWorseThan r x ⊆
      NoBetterThan r x \ NoBetterThan r y := fun _ h => ⟨h.2.1, h.1.2⟩
  have hdiff : 0 < μ (NoBetterThan r x \ NoBetterThan r y) :=
    hpos.trans_le (measure_mono hsub)
  have hreal : 0 < μ.real (NoBetterThan r x \ NoBetterThan r y) :=
    ENNReal.toReal_pos (ne_of_gt hdiff) (measure_ne_top μ _)
  have hnsub : NoBetterThan r y ⊆ NoBetterThan r x := fun w hw => hr.2 x y w hxy.1 hw
  rw [measureReal_sdiff hnsub (((proposition_1_14c hr).mp hc y).1.measurableSet)] at hreal
  exact sub_pos.mp hreal

/-- Positive mass on nonempty opens suffices for the finite-measure representation. -/
theorem measureUtility_represents [TopologicalSpace X] [OpensMeasurableSpace X]
    [PreconnectedSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) : Represents (MeasureUtility μ r) r := by
  intro x y
  constructor
  · exact measureUtility_mono μ hr.2
  · intro h
    by_contra hxy
    have hyx : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact not_lt_of_ge h (measureUtility_strict μ hr hc hyx)

/-- A continuous representation expresses lower-contour mass as cumulative mass of real ranks. -/
theorem measureUtility_eq_distribution [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} (hu : Represents u r) (huc : Continuous u) (x : X) :
    MeasureUtility μ r x = LowerDistribution (μ.map u) (u x) := by
  unfold LowerDistribution
  rw [map_measureReal_apply huc.measurable isClosed_Iic.measurableSet]
  change μ.real (NoBetterThan r x) = μ.real (u ⁻¹' Set.Iic (u x))
  congr 1
  ext y
  exact hu x y

/-- A continuous representation makes finite lower-contour measure upper semicontinuous. -/
theorem measureUtility_upperSemicontinuous [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : Represents u r) (huc : Continuous u) : UpperSemicontinuous (MeasureUtility μ r) := by
  have he : MeasureUtility μ r = fun x => LowerDistribution (μ.map u) (u x) :=
    funext (measureUtility_eq_distribution μ hu huc)
  rw [he]
  exact (lowerDistribution_upperSemicontinuous (μ.map u)).comp huc

/-- Zero mass on an indifference class is exactly zero mass at its represented rank. -/
theorem measureUtility_rank_atom [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} (hu : Represents u r) (huc : Continuous u) (x : X) :
    (μ.map u) {u x} = μ (IndifferenceClass r x) := by
  rw [Measure.map_apply huc.measurable isClosed_singleton.measurableSet]
  congr 1
  ext y
  exact (indifferent_iff_utility_eq hu y x).symm

/-- Null indifference classes give continuity at the corresponding bundles. -/
theorem measureUtility_continuousAt_of_null_class [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Represents u r)
    (huc : Continuous u) (x : X) (hx : μ (IndifferenceClass r x) = 0) :
    ContinuousAt (MeasureUtility μ r) x := by
  have he : MeasureUtility μ r = fun y => LowerDistribution (μ.map u) (u y) :=
    funext (measureUtility_eq_distribution μ hu huc)
  rw [he]
  have ha : (μ.map u) {u x} = 0 := (measureUtility_rank_atom μ hu huc x).trans hx
  exact (lowerDistribution_continuousAt (μ.map u) (u x) ha).comp huc.continuousAt

/-- If every indifference class has zero measure, the finite-measure utility is continuous. -/
theorem measureUtility_continuous_of_null_classes [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Represents u r)
    (huc : Continuous u) (hnull : ∀ x, μ (IndifferenceClass r x) = 0) :
    Continuous (MeasureUtility μ r) :=
  continuous_iff_continuousAt.mpr (fun x =>
    measureUtility_continuousAt_of_null_class μ hu huc x (hnull x))

/-- The representation and upper-semicontinuity conclusions on the book's orthant domain. -/
theorem problem_2_15_openPos {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) :
    Represents (MeasureUtility μ r) r ∧ UpperSemicontinuous (MeasureUtility μ r) := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  exact ⟨measureUtility_represents μ hr hc, measureUtility_upperSemicontinuous μ hu huc⟩

/-- A sufficient continuity condition in **Problem 2.15**, stated on indifference classes. -/
theorem problem_2_15_continuity {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ]
    (hr : Rational r) (hc : ContinuousPreference r)
    (hnull : ∀ x, μ (IndifferenceClass r x) = 0) : Continuous (MeasureUtility μ r) := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  exact measureUtility_continuous_of_null_classes μ hu huc hnull

end Kreps.PreferenceProperties
