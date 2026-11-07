/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixSequenceLimits
import PreferenceProperties.AppendixSemicontinuity

/-!
# Appendix 2: sequential semicontinuity

Proposition A2.25, p. 451. Extended-real limsup and liminf include sequences
whose function values are unbounded. Subtype domains give the stated relative version.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Real-valued upper semicontinuity is unchanged by inclusion in the extended real line. -/
theorem upperSemicontinuousAt_real_coe {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt (fun y => (f y : EReal)) x ↔ UpperSemicontinuousAt f x := by
  constructor
  · intro h r hr
    exact (h (r : EReal) (EReal.coe_lt_coe hr)).mono fun _ hy =>
      EReal.coe_lt_coe_iff.mp hy
  · intro h a hxa
    induction a using EReal.rec with
    | bot => exact False.elim (not_lt_bot hxa)
    | coe r =>
      exact (h r (EReal.coe_lt_coe_iff.mp hxa)).mono fun _ hy => EReal.coe_lt_coe hy
    | top => exact Filter.Eventually.of_forall fun y => EReal.coe_lt_top (f y)

/-- Real-valued lower semicontinuity is also unchanged by the inclusion. -/
theorem lowerSemicontinuousAt_real_coe {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt (fun y => (f y : EReal)) x ↔ LowerSemicontinuousAt f x := by
  constructor
  · intro h r hr
    exact (h (r : EReal) (EReal.coe_lt_coe hr)).mono fun _ hy =>
      EReal.coe_lt_coe_iff.mp hy
  · intro h a hax
    induction a using EReal.rec with
    | bot => exact Filter.Eventually.of_forall fun y => EReal.bot_lt_coe (f y)
    | coe r =>
      exact (h r (EReal.coe_lt_coe_iff.mp hax)).mono fun _ hy => EReal.coe_lt_coe hy
    | top => exact False.elim (not_top_lt hax)

/-- Upper semicontinuity at a point is characterized by sequential limsup inequalities. -/
theorem appendix2_upper_sequence_iff {X γ : Type*} [PseudoMetricSpace X]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ] (f : X → γ) (x : X) :
    UpperSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) → Filter.limsup (f ∘ u) Filter.atTop ≤ f x := by
  constructor
  · intro h u hu
    exact hu.limsup_comp_le_limsup.trans (upperSemicontinuousAt_iff_limsup_le.mp h)
  · intro h a ha
    have hx : x ∉ closure {y | a ≤ f y} := by
      intro hmem
      obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
      have hlo : a ≤ Filter.liminf (f ∘ u) Filter.atTop :=
        Filter.le_liminf_of_le (by isBoundedDefault) (Filter.Eventually.of_forall hu)
      have hls : Filter.liminf (f ∘ u) Filter.atTop ≤ Filter.limsup (f ∘ u) Filter.atTop :=
        Filter.liminf_le_limsup
      exact (not_le_of_gt ha) (hlo.trans (hls.trans (h u hlim)))
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    exact lt_of_not_ge (fun hge => hy (subset_closure hge))

/-- The lower-semicontinuity version follows by reversing the complete order. -/
theorem appendix2_lower_sequence_iff {X γ : Type*} [PseudoMetricSpace X]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ] (f : X → γ) (x : X) :
    LowerSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) → f x ≤ Filter.liminf (f ∘ u) Filter.atTop :=
  appendix2_upper_sequence_iff (γ := γᵒᵈ) f x

/-- **Proposition A2.25:** upper semicontinuity at a point is the limsup inequality. -/
theorem proposition_A2_25_upper {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) →
        Filter.limsup (fun n => (f (u n) : EReal)) Filter.atTop ≤ (f x : EReal) :=
  (upperSemicontinuousAt_real_coe f x).symm.trans (appendix2_upper_sequence_iff _ x)

/-- **Proposition A2.25:** lower semicontinuity at a point is the liminf inequality. -/
theorem proposition_A2_25_lower {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) →
        (f x : EReal) ≤ Filter.liminf (fun n => (f (u n) : EReal)) Filter.atTop :=
  (lowerSemicontinuousAt_real_coe f x).symm.trans (appendix2_lower_sequence_iff _ x)

end Kreps.PreferenceProperties
