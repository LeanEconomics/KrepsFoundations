/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConvexityExamples
import PreferenceProperties.UtilityExamples

/-!
# Ordinal rescaling can destroy concavity or continuity

Kreps I, p. 35 and Problem 2.5a-b, p. 46. Identity on the one-good orthant is
concave and continuous. A piecewise linear increasing transformation destroys
concavity; the jump transformation from Chapter 1 destroys continuity.
-/

namespace Kreps.PreferenceProperties

/-- A strictly increasing transformation whose slope rises at one. -/
noncomputable def ConvexWarp (t : ℝ) : ℝ := if t ≤ 1 then t else 2 * t - 1

/-- Both slopes are positive and the two branches meet at the breakpoint. -/
theorem convexWarp_strictMono : StrictMono ConvexWarp := by
  intro x y hxy
  unfold ConvexWarp
  split_ifs <;> linarith

/-- Identity satisfies Jensen's inequality with equality. -/
theorem identityUtility_concave :
    ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => x.val) := by
  intro x y a ha
  exact le_rfl

/-- The transformed midpoint is strictly below the average transformed endpoint values. -/
theorem convexWarp_not_concave :
    ¬ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => ConvexWarp x.val) := by
  intro h
  have hm := h ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ (1 / 2) (by constructor <;> norm_num)
  norm_num [ConvexWarp, Mix, smul_eq_mul] at hm

/-- **Problem 2.5a:** concavity is not invariant under strictly increasing rescaling. -/
theorem problem_2_5a :
    ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => x.val) ∧
    StrictMono ConvexWarp ∧
    ¬ConcaveUtility (convex_Ici (0 : ℝ)) (ConvexWarp ∘ fun x : OneGood => x.val) :=
  ⟨identityUtility_concave, convexWarp_strictMono, convexWarp_not_concave⟩

/-- A jump at the interior point one prevents continuity on the half-line. -/
theorem jumpUtility_not_continuous :
    ¬Continuous (fun x : OneGood => JumpUtility x.val) := by
  intro h
  have hc : ContinuousAt (fun x : OneGood => JumpUtility x.val) ⟨1, by norm_num⟩ :=
    h.continuousAt
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  let x : OneGood := ⟨1 + δ / 2, show 0 ≤ 1 + δ / 2 from by positivity⟩
  have hx : dist x (⟨1, by norm_num⟩ : OneGood) < δ := by
    change dist (1 + δ / 2) (1 : ℝ) < δ
    rw [Real.dist_eq, show 1 + δ / 2 - 1 = δ / 2 by ring,
      abs_of_pos (by positivity)]
    linarith
  have hx1 : 1 < x.val := by change 1 < 1 + δ / 2; linarith
  have hj : JumpUtility x.val = x.val + 1 := by
    simp only [JumpUtility, ite_eq_right (not_le.mpr hx1)]
  have h1 : JumpUtility 1 = 1 := by norm_num [JumpUtility]
  have hbound := hb hx
  change dist (JumpUtility x.val) (JumpUtility 1) < 1 / 2 at hbound
  rw [hj, h1, Real.dist_eq, abs_of_pos (by linarith : 0 < x.val + 1 - 1)] at hbound
  linarith

/-- **Problem 2.5b:** continuity is not invariant under strictly increasing rescaling. -/
theorem problem_2_5b :
    Continuous (fun x : OneGood => x.val) ∧ StrictMono JumpUtility ∧
    ¬Continuous (JumpUtility ∘ fun x : OneGood => x.val) :=
  ⟨continuous_subtype_val, jumpUtility_strictMono, jumpUtility_not_continuous⟩

end Kreps.PreferenceProperties
