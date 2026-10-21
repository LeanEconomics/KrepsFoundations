/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ActiveCoordinateReduction

/-!
# Retaining precisely the nondegenerate scalar factors

The scalar utility reduction may contain singleton score ranges. Their deletion
preserves every hypothesis needed for the nondegenerate interval theorem, and
zero extension transports its additive representation to all original ranges.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Scalar coordinates with at least two attainable values. -/
abbrev NontrivialScalarIndices (S : I → Set ℝ) := {i : I // Nontrivial (S i)}

/-- The exact utility on nondegenerate factors, with singleton coordinates fixed at baseline. -/
noncomputable def ActiveScalarUtility (V : (∀ i, S i) → ℝ) (z : ∀ i, S i)
    (x : ∀ i : NontrivialScalarIndices S, S i.val) : ℝ :=
  V (ActiveCoordinateExtend (fun i => Nontrivial (S i)) z x)

/-- A factor excluded from the active index set is a singleton type. -/
theorem inactiveScalar_subsingleton (i : I) (hi : ¬ Nontrivial (S i)) : Subsingleton (S i) :=
  not_nontrivial_iff_subsingleton.mp hi

/-- Continuity survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_continuous {V : (∀ i, S i) → ℝ} (hc : Continuous V)
    (z : ∀ i, S i) : Continuous (ActiveScalarUtility V z) :=
  hc.comp (activeCoordinateExtend_continuous (fun i => Nontrivial (S i)) z)

/-- Strict increase survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_strictMono {V : (∀ i, S i) → ℝ} (hm : StrictMono V)
    (z : ∀ i, S i) : StrictMono (ActiveScalarUtility V z) :=
  hm.comp (ActiveCoordinateOrderIso (fun i => Nontrivial (S i)) z
    inactiveScalar_subsingleton).strictMono

/-- Strong separability survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_stronglySeparable [DecidableEq I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, S i) :
    StronglySeparable (UtilityPref (ActiveScalarUtility V z)) :=
  stronglySeparable_activeCoordinates (fun i => Nontrivial (S i)) hs z

/-- Three nondegenerate scalar factors give three distinct members of the retained index set. -/
theorem three_nontrivialScalarIndices
    (h : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (S i) ∧ Nontrivial (S j) ∧ Nontrivial (S l)) :
    ∃ i j l : NontrivialScalarIndices S, i ≠ j ∧ i ≠ l ∧ j ≠ l := by
  obtain ⟨i, j, l, hij, hil, hjl, hi, hj, hl⟩ := h
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩,
    fun h => hij (congrArg Subtype.val h),
    fun h => hil (congrArg Subtype.val h),
    fun h => hjl (congrArg Subtype.val h)⟩

/-- Extend an actual continuous increasing active additive representation to every scalar factor. -/
theorem continuous_additive_of_activeScalar [Fintype I] [Fintype (NontrivialScalarIndices S)]
    {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (h : ∃ w : ∀ i : NontrivialScalarIndices S, S i.val → ℝ,
      (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
        Represents (AdditiveUtility w) (UtilityPref (ActiveScalarUtility V z))) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  obtain ⟨w, hwc, hwm, hwr⟩ := h
  exact ⟨ActiveCoordinateUtility (fun i => Nontrivial (S i)) w,
    activeCoordinateUtility_continuous _ hwc,
    activeCoordinateUtility_strictMono _ hwm inactiveScalar_subsingleton,
    represents_activeCoordinates _ z inactiveScalar_subsingleton hwr⟩

end Kreps.PreferenceProperties
