/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.MeasureUtility
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Lebesgue-positivity hypothesis in Problem 2.15

Lebesgue measure on the orthant is the ambient product measure pulled back through
the subtype inclusion. Every nonempty relatively open set has positive measure,
including neighborhoods at the boundary. Consequently, the book's condition that
positive-Lebesgue-measure sets have positive `μ`-measure gives the full-support
hypothesis used in the finite-measure utility construction.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory

/-- Lebesgue measure restricted to the nonnegative orthant, as a measure on its subtype. -/
noncomputable def OrthantLebesgue (k : ℕ) : Measure (NonnegativeOrthant k) :=
  (volume : Measure (Fin k → ℝ)).comap Subtype.val

/-- Subtype measure is the ambient measure of the corresponding set of bundles. -/
theorem orthantLebesgue_apply (k : ℕ) (A : Set (NonnegativeOrthant k)) :
    OrthantLebesgue k A = volume (Subtype.val '' A) := by
  exact (MeasurableEmbedding.subtype_coe
    (isClosed_Ici (a := (0 : Fin k → ℝ))).measurableSet).comap_apply volume A

/-- Every relative neighborhood contains an ambient ball inside the orthant. -/
theorem orthant_open_contains_ambient_ball {k : ℕ} {U : Set (NonnegativeOrthant k)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : Fin k → ℝ, ∃ δ > 0, Metric.ball y δ ⊆ Subtype.val '' U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let y := RaisedBundle x (ε / 2) (by positivity)
  have hyx : dist y x ≤ ε / 2 := raisedBundle_dist_le x (by positivity)
  refine ⟨y.val, ε / 4, by positivity, ?_⟩
  intro z hz
  have hzdist : dist z y.val < ε / 4 := hz
  have hznonneg : 0 ≤ z := by
    intro j
    have hcoord := (dist_le_pi_dist z y.val j).trans_lt hzdist
    change |z j - (x.val j + ε / 2)| < ε / 4 at hcoord
    have hlow := (abs_lt.mp hcoord).1
    have hxj := x.property j
    change 0 ≤ x.val j at hxj
    change 0 ≤ z j
    linarith
  let z' : NonnegativeOrthant k := ⟨z, hznonneg⟩
  refine ⟨z', hball ?_, rfl⟩
  change dist z x.val < ε
  have htriangle := dist_triangle z y.val x.val
  change dist y.val x.val ≤ ε / 2 at hyx
  linarith

/-- Relative nonempty opens have positive Lebesgue measure, also at boundary points. -/
theorem orthantLebesgue_open_pos {k : ℕ} {U : Set (NonnegativeOrthant k)}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < OrthantLebesgue k U := by
  obtain ⟨y, δ, hδ, hball⟩ := orthant_open_contains_ambient_ball hU hne
  have hpos := Metric.isOpen_ball.measure_pos (volume : Measure (Fin k → ℝ))
    ⟨y, Metric.mem_ball_self hδ⟩
  rw [orthantLebesgue_apply]
  exact hpos.trans_le (measure_mono hball)

/-- The book's Lebesgue-positivity assumption implies positive mass on nonempty opens. -/
theorem orthant_measure_openPos {k : ℕ} (μ : Measure (NonnegativeOrthant k))
    (hμ : ∀ A, MeasurableSet A → 0 < OrthantLebesgue k A → 0 < μ A) :
    μ.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  exact ne_of_gt (hμ U hU.measurableSet (orthantLebesgue_open_pos hU hne))

/-- **Problem 2.15:** lower-contour measure represents preference and is upper semicontinuous. -/
theorem problem_2_15 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → 0 < OrthantLebesgue k A → 0 < μ A)
    (hr : Rational r) (hc : ContinuousPreference r) :
    Represents (MeasureUtility μ r) r ∧ UpperSemicontinuous (MeasureUtility μ r) := by
  let : μ.IsOpenPosMeasure := orthant_measure_openPos μ hμ
  exact problem_2_15_openPos μ hr hc

end Kreps.PreferenceProperties
