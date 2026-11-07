/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.Prerequisites
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Differentiability is not an ordinal property

Kreps I, p. 63. This is a constructed witness, not a formula printed in the
book: an increasing continuous transform of linear utility introduces a kink
at positive consumption. The same preference retains its smooth linear
representation while the transformed representation is not differentiable.
-/

namespace Kreps.ConsumerDemand

/-- An increasing continuous transformation with a kink at the positive utility level one. -/
noncomputable def KinkTransform (t : ℝ) : ℝ := t + |t - 1| / 2

/-- The kink transformation is strictly increasing on all real utility levels. -/
theorem kinkTransform_strictMono : StrictMono KinkTransform := by
  intro x z hxz
  unfold KinkTransform
  by_cases hx : x ≤ 1
  · by_cases hz : z ≤ 1
    · rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hz)]
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_pos (sub_pos.mpr (lt_of_not_ge hz))]
      linarith
  · have hz : 1 < z := (lt_of_not_ge hx).trans hxz
    rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hx)), abs_of_pos (sub_pos.mpr hz)]
    linarith

/-- The kink transformation is continuous. -/
theorem kinkTransform_continuous : Continuous KinkTransform := by
  exact continuous_id.add ((continuous_id.sub continuous_const).abs.div_const 2)

/-- The transformed function is not differentiable at its positive kink. -/
theorem kinkTransform_not_differentiableAt : ¬DifferentiableAt ℝ KinkTransform 1 := by
  intro hd
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t - 1|) 1 := by
    convert ((hd.sub (differentiableAt_id (x := 1))).const_mul 2) using 1
    funext t
    change |t - 1| = 2 * (KinkTransform t - t)
    unfold KinkTransform
    ring
  have houter : DifferentiableAt ℝ (fun t : ℝ => |t - 1|) ((fun t : ℝ => t + 1) 0) := by
    simpa using habs
  have hshift := houter.comp 0 ((differentiableAt_id (x := (0 : ℝ))).add_const 1)
  apply not_differentiableAt_abs_zero
  convert! hshift using 1
  ext t
  simp

/-- On the actual one-good nonnegative consumption domain the transform represents linear tastes. -/
theorem kinkTransform_represents_linear :
    Represents (fun x : NonnegativeOrthant 1 => KinkTransform (x.val 0))
      (UtilityPref (fun x : NonnegativeOrthant 1 => x.val 0)) := by
  intro x z
  exact kinkTransform_strictMono.le_iff_le.symm

/-- The nonnegative-domain restriction does not remove the kink at consumption one. -/
theorem kinkTransform_not_differentiableWithinAt :
    ¬DifferentiableWithinAt ℝ KinkTransform (Set.Ici 0) 1 := by
  intro hd
  exact kinkTransform_not_differentiableAt (hd.differentiableAt (Ici_mem_nhds (by norm_num)))

end Kreps.ConsumerDemand
