/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.UpperSemicontinuousSeries
import PreferenceProperties.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Group.Indicator

/-!
# Appendix 2: semicontinuity and compact maximization

Definition A2.24 and Proposition A2.26, p. 451. The final diagnostic exercise
requires a correction: absolute summability alone does not imply upper
semicontinuity for signed coefficients. Nonnegative coefficients do suffice.
A single negative coefficient on the closed set `{0}` disproves the printed claim.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- **Definition A2.24:** the book's non-strict epsilon formulation of upper semicontinuity. -/
theorem definition_A2_24_upper {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt f x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → f y ≤ f x + ε := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (h (f x + ε) (by linarith))
    exact ⟨δ, hδ, fun y hy => (hnear hy).le⟩
  · intro h b hb
    obtain ⟨δ, hδ, hnear⟩ := h ((b - f x) / 2) (by linarith)
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear y hy
    linarith

/-- **Definition A2.24:** the corresponding lower-semicontinuity formulation. -/
theorem definition_A2_24_lower {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt f x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → f x ≤ f y + ε := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (h (f x - ε) (by linarith))
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear hy
    linarith
  · intro h a ha
    obtain ⟨δ, hδ, hnear⟩ := h ((f x - a) / 2) (by linarith)
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear y hy
    linarith

/-- **Proposition A2.26:** an upper semicontinuous function attains its finite supremum. -/
theorem proposition_A2_26 {X : Type*} [TopologicalSpace X] {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : UpperSemicontinuousOn f K) :
    ∃ x ∈ K, f x = sSup (f '' K) ∧ ∀ y ∈ K, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne hK hf
  have hg : IsGreatest (f '' K) (f x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨x, hx, hg.csSup_eq.symm, hmax⟩

/-- The economic consequence on p. 451: upper semicontinuous utility gives compact-menu choice. -/
theorem upperSemicontinuous_compact_choice {X : Type*} [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} {K : Set X}
    (hu : Represents u r) (hK : IsCompact K) (hne : K.Nonempty)
    (hc : UpperSemicontinuousOn u K) : (PrefChoice r K).Nonempty := by
  obtain ⟨x, hx, _, hmax⟩ := proposition_A2_26 hK hne hc
  exact ⟨x, hx, fun y hy => (hu x y).mpr (hmax y hy)⟩

/-- The weighted closed-set indicator series from the final diagnostic exercise. -/
noncomputable def ClosedIndicatorSeries {X : Type*} (C : ℕ → Set X) (w : ℕ → ℝ)
    (x : X) : ℝ := ∑' n, (C n).indicator (fun _ => w n) x

/-- The diagnostic claim is valid when its absolutely summable coefficients are nonnegative. -/
theorem appendix2_diagnostic_nonnegative {X : Type*} [TopologicalSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable (fun n => |w n|)) :
    UpperSemicontinuous (ClosedIndicatorSeries C w) := by
  apply upperSemicontinuous_tsum_of_norm_le hs
  · intro n
    exact (hC n).upperSemicontinuous_indicator (hw n)
  · intro n x
    simpa only [Real.norm_eq_abs] using
      norm_indicator_le_norm_self (s := C n) (fun _ => w n) x

/-- A single negative coefficient; all later coefficients vanish. -/
def DiagnosticNegativeWeights (n : ℕ) : ℝ := if n = 0 then -1 else 0

/-- The closed sets in the counterexample can all be the same singleton. -/
def DiagnosticClosedSets (_ : ℕ) : Set ℝ := {0}

/-- The counterexample satisfies the printed absolute-summability hypothesis. -/
theorem diagnosticNegativeWeights_summable :
    Summable (fun n => |DiagnosticNegativeWeights n|) := by
  have he : (fun n => |DiagnosticNegativeWeights n|) =
      fun n : ℕ => if n = 0 then 1 else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [DiagnosticNegativeWeights, hn]
  rw [he]
  exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable

/-- Its indicator sum is negative at zero and vanishes elsewhere. -/
theorem diagnosticNegative_formula (x : ℝ) :
    ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights x =
      if x = 0 then -1 else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [ClosedIndicatorSeries, DiagnosticClosedSets, DiagnosticNegativeWeights]
  · simp [ClosedIndicatorSeries, DiagnosticClosedSets, hx]

/-- The printed signed-coefficient diagnostic fails already at the origin of the real line. -/
theorem diagnosticNegative_not_upperSemicontinuousAt :
    ¬ UpperSemicontinuousAt
      (ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights) 0 := by
  intro h
  have hnear := h (-1 / 2) (by
    change ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights 0 < -1 / 2
    rw [diagnosticNegative_formula]
    norm_num)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := (hlim.eventually hnear).exists
  rw [diagnosticNegative_formula, ite_eq_right (ne_of_gt (pow_pos (by norm_num) n))] at hn
  norm_num at hn

/-- A formal counterexample to the final diagnostic as printed, with all its stated hypotheses. -/
theorem appendix2_diagnostic_counterexample :
    (∀ n, IsClosed (DiagnosticClosedSets n)) ∧
      Summable (fun n => |DiagnosticNegativeWeights n|) ∧
      ¬ UpperSemicontinuous
        (ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights) := by
  exact ⟨fun _ => isClosed_singleton, diagnosticNegativeWeights_summable,
    fun h => diagnosticNegative_not_upperSemicontinuousAt (h 0)⟩

end Kreps.PreferenceProperties
