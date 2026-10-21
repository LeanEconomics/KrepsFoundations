/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConcaveUtility
import PreferenceProperties.Insatiability
import PreferenceProperties.Rationalization

/-!
# Nonattainment and insatiability counterexamples

Kreps I, Problems 2.2-2.3, p. 46. The scalar half-line is the one-good orthant.
A utility increasing up to an unattained peak and decreasing after a downward jump
gives strictly convex preferences with empty choice on [0,1]. A utility with an
initial flat portion is globally insatiable and convex, but not locally insatiable.
-/

namespace Kreps.PreferenceProperties

/-- The one-good nonnegative consumption domain. -/
abbrev OneGood : Type := Set.Ici (0 : ℝ)

/-- An increasing left branch with a downward jump, followed by a decreasing right branch. -/
noncomputable def NonattainingUtility (x : OneGood) : ℝ :=
  if x.val < 1 then x.val else -x.val

/-- This discontinuous utility is nevertheless strictly quasi-concave. -/
theorem nonattainingUtility_strictQuasi :
    StrictlyQuasiConcaveUtility (convex_Ici (0 : ℝ)) NonattainingUtility := by
  intro x y hne horder a ha
  have hx0 : 0 ≤ x.val := x.property
  have hy0 : 0 ≤ y.val := y.property
  have hne' : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  let m := a * x.val + (1 - a) * y.val
  change (if y.val < 1 then y.val else -y.val) ≤
    (if x.val < 1 then x.val else -x.val) at horder
  change (if y.val < 1 then y.val else -y.val) < (if m < 1 then m else -m)
  rcases lt_or_gt_of_ne hne' with hxy | hyx
  · have hmlo : x.val < m := by
      dsimp [m]
      nlinarith [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hxy)]
    have hmhi : m < y.val := by
      dsimp [m]
      nlinarith [mul_pos ha.1 (sub_pos.mpr hxy)]
    split_ifs at horder ⊢ <;> linarith
  · have hmlo : y.val < m := by
      dsimp [m]
      nlinarith [mul_pos ha.1 (sub_pos.mpr hyx)]
    have hmhi : m < x.val := by
      dsimp [m]
      nlinarith [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hyx)]
    split_ifs at horder ⊢ <;> linarith

/-- The corresponding preference satisfies the book's strict convexity definition. -/
theorem nonattainingPreference_strictConvex :
    StrictlyConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref NonattainingUtility) :=
  (proposition_2_8b_strict (fun _ _ => Iff.rfl)).mp nonattainingUtility_strictQuasi

/-- The compact convex menu for Problem 2.2. -/
def UnitMenu : Set OneGood := {x | x.val ≤ 1}

/-- The menu is nonempty. -/
theorem unitMenu_nonempty : UnitMenu.Nonempty := ⟨⟨0, by norm_num⟩, by norm_num [UnitMenu]⟩

/-- Its ambient image is exactly the closed unit interval. -/
theorem unitMenu_image : Subtype.val '' UnitMenu = Set.Icc (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · intro ht
    exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩

/-- The compactness is in the relative topology of the one-good orthant. -/
theorem unitMenu_compact : IsCompact UnitMenu := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, unitMenu_image]
  exact isCompact_Icc

/-- The same menu is convex, independently of the preference. -/
theorem unitMenu_convex : ConvexMenu (convex_Ici (0 : ℝ)) UnitMenu := by
  rw [convexMenu_iff, unitMenu_image]
  exact convex_Icc 0 1

/-- Every menu member is beaten by another member, so the best set is empty. -/
theorem nonattainingUtility_empty : UtilityChoice NonattainingUtility UnitMenu = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx1 : x.val ≤ 1 := hx.1
  by_cases hlt : x.val < 1
  · let y : OneGood := ⟨(x.val + 1) / 2,
      show 0 ≤ (x.val + 1) / 2 from
        div_nonneg (add_nonneg x.property zero_le_one) (by norm_num)⟩
    have hy : y ∈ UnitMenu := by change (x.val + 1) / 2 ≤ 1; linarith
    have horder := hx.2 y hy
    have hy1 : y.val < 1 := by dsimp [y]; linarith
    change NonattainingUtility y ≤ NonattainingUtility x at horder
    simp only [NonattainingUtility, ite_eq_left hlt, ite_eq_left hy1] at horder
    dsimp [y] at horder
    linarith
  · have he : x.val = 1 := le_antisymm hx1 (le_of_not_gt hlt)
    have horder := hx.2 ⟨0, by norm_num⟩ (by norm_num [UnitMenu])
    norm_num [UtilityPref, NonattainingUtility, he] at horder

/-- **Problem 2.2:** strict convexity does not give existence, even on a compact convex menu. -/
theorem problem_2_2 :
    Rational (UtilityPref NonattainingUtility) ∧
    StrictlyConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref NonattainingUtility) ∧
    UnitMenu.Nonempty ∧ ConvexMenu (convex_Ici (0 : ℝ)) UnitMenu ∧ IsCompact UnitMenu ∧
    UtilityChoice NonattainingUtility UnitMenu = ∅ :=
  ⟨proposition_1_3a _, nonattainingPreference_strictConvex, unitMenu_nonempty,
    unitMenu_convex, unitMenu_compact, nonattainingUtility_empty⟩

/-- An initially flat utility that is unbounded above. -/
noncomputable def FlatUtility (x : OneGood) : ℝ := max 0 (x.val - 1)

/-- The flat utility is nondecreasing. -/
theorem flatUtility_monotone : Monotone FlatUtility := by
  intro x y hxy
  have h : x.val ≤ y.val := hxy
  exact max_le_max le_rfl (sub_le_sub_right h 1)

/-- On a one-dimensional interval, a nondecreasing utility is quasi-concave. -/
theorem flatUtility_quasi : QuasiConcaveUtility (convex_Ici (0 : ℝ)) FlatUtility := by
  apply (quasiConcaveUtility_iff_quasiconcaveOn (convex_Ici (0 : ℝ))
    (fun x : ℝ => max 0 (x - 1))).mpr
  exact (show MonotoneOn (fun x : ℝ => max 0 (x - 1)) (Set.Ici 0) from
    fun _ _ _ _ hxy => max_le_max le_rfl (sub_le_sub_right hxy 1)).quasiconcaveOn
      (convex_Ici 0)

/-- More than two additional units always give a strict improvement over the flat part. -/
theorem flatUtility_globallyInsatiable : GloballyInsatiable (UtilityPref FlatUtility) := by
  intro x
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨x.val + 2, add_nonneg hx0 (by norm_num)⟩
  have hlt : FlatUtility x < FlatUtility y := by
    dsimp [FlatUtility, y]
    rw [max_eq_right (by linarith : 0 ≤ x.val + 2 - 1)]
    exact max_lt (by linarith) (by linarith)
  exact ⟨y, hlt.le, not_le_of_gt hlt⟩

/-- At zero, a sufficiently small ball contains no strict improvement. -/
theorem flatUtility_not_locallyInsatiable : ¬LocallyInsatiable (UtilityPref FlatUtility) := by
  intro h
  obtain ⟨y, hy, hs⟩ := h ⟨0, by norm_num⟩ (1 / 2) (by norm_num)
  have hy0 : 0 ≤ y.val := y.property
  change dist y.val (0 : ℝ) ≤ 1 / 2 at hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0] at hy
  have he : FlatUtility y = 0 := max_eq_left (by linarith)
  apply hs.2
  change FlatUtility y ≤ FlatUtility ⟨0, by norm_num⟩
  rw [he]
  norm_num [FlatUtility]

/-- **Problem 2.3:** convexity alone does not replace semi-strict convexity. -/
theorem problem_2_3_counterexample :
    Rational (UtilityPref FlatUtility) ∧ GloballyInsatiable (UtilityPref FlatUtility) ∧
    ConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref FlatUtility) ∧
    ¬LocallyInsatiable (UtilityPref FlatUtility) :=
  ⟨proposition_1_3a _, flatUtility_globallyInsatiable,
    (proposition_2_8b_quasi (fun _ _ => Iff.rfl)).mp flatUtility_quasi,
    flatUtility_not_locallyInsatiable⟩

end Kreps.PreferenceProperties
