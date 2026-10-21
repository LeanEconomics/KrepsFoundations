/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CountableUtility
import Mathlib.Data.EReal.Basic

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Equivalent utility representations

Kreps I, §1.7, Propositions 1.20-1.21, pp. 17-18, and Problem 1.14, p. 27.
The transformation need only be strictly increasing on the attained utility range.
A globally nondecreasing extension exists with values in the extended reals.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop} {u v : X → ℝ}

/-- **Proposition 1.20**, p. 17: strictly increasing transforms preserve representation. -/
theorem proposition_1_20 (hu : Represents u r) {f : ℝ → ℝ} (hf : StrictMono f) :
    Represents (f ∘ u) r := by
  intro x y
  exact (hu x y).trans hf.le_iff_le.symm

/-- Two utilities representing the same preference have identical equality fibers. -/
theorem same_utility_fibers (hu : Represents u r) (hv : Represents v r)
    {x y : X} (h : u x = u y) : v x = v y := by
  apply le_antisymm
  · exact (hv y x).mp ((hu y x).mpr h.le)
  · exact (hv x y).mp ((hu x y).mpr h.ge)

/-- Choose a value on the attained range and extend arbitrarily elsewhere. -/
noncomputable def UtilityTransform (u v : X → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, u x = t then v (Classical.choose h) else 0

/-- The transformation recovers the second utility exactly. -/
theorem utilityTransform_apply (hu : Represents u r) (hv : Represents v r) (x : X) :
    UtilityTransform u v (u x) = v x := by
  classical
  unfold UtilityTransform
  rw [dite_eq_left (show ∃ y, u y = u x from ⟨x, rfl⟩)]
  exact same_utility_fibers hu hv (Classical.choose_spec (show ∃ y, u y = u x from ⟨x, rfl⟩))

/-- The transformation is strictly increasing on the original utility range. -/
theorem utilityTransform_strictMonoOn (hu : Represents u r) (hv : Represents v r) :
    StrictMonoOn (UtilityTransform u v) (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [utilityTransform_apply hu hv x, utilityTransform_apply hu hv y]
  exact (strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy)

/-- A transformation strictly increasing only on attained values still preserves preference. -/
theorem represents_of_transform_on_range (hu : Represents u r) {f : ℝ → ℝ}
    (hf : StrictMonoOn f (Set.range u)) (hv : ∀ x, v x = f (u x)) : Represents v r := by
  intro x y
  rw [hv x, hv y]
  exact (hu x y).trans (hf.le_iff_le ⟨y, rfl⟩ ⟨x, rfl⟩).symm

/-- **Proposition 1.21**, p. 18: exact characterization, with `u` a representation. -/
theorem proposition_1_21 (hu : Represents u r) :
    Represents v r ↔ ∃ f : ℝ → ℝ, StrictMonoOn f (Set.range u) ∧ ∀ x, v x = f (u x) := by
  constructor
  · intro hv
    exact ⟨UtilityTransform u v, utilityTransform_strictMonoOn hu hv,
      fun x => (utilityTransform_apply hu hv x).symm⟩
  · rintro ⟨f, hf, hv⟩
    exact represents_of_transform_on_range hu hf hv

/-- Problem 1.14d's supremum extension, allowing empty and unbounded lower sections. -/
noncomputable def ExtendedUtilityTransform (u v : X → ℝ) (t : ℝ) : EReal :=
  sSup {a : EReal | ∃ x, u x ≤ t ∧ a = (v x : EReal)}

/-- The supremum extension is nondecreasing on all real arguments. -/
theorem extendedUtilityTransform_monotone (u v : X → ℝ) :
    Monotone (ExtendedUtilityTransform u v) := by
  intro a b hab
  apply sSup_le_sSup
  rintro t ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans hab, rfl⟩

/-- At an attained value the supremum is exactly the corresponding second utility. -/
theorem extendedUtilityTransform_apply (hu : Represents u r) (hv : Represents v r) (x : X) :
    ExtendedUtilityTransform u v (u x) = (v x : EReal) := by
  apply le_antisymm
  · apply sSup_le
    rintro t ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe ((hv x y).mp ((hu x y).mpr hy))
  · apply le_sSup
    exact ⟨x, le_rfl, rfl⟩

/-- The extended-real transformation is strictly increasing on the attained range. -/
theorem extendedUtilityTransform_strictMonoOn (hu : Represents u r) (hv : Represents v r) :
    StrictMonoOn (ExtendedUtilityTransform u v) (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [extendedUtilityTransform_apply hu hv x, extendedUtilityTransform_apply hu hv y]
  exact EReal.coe_lt_coe
    ((strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy))

/-- The extended-real conclusion of **Proposition 1.21**, p. 18. -/
theorem proposition_1_21_extension (hu : Represents u r) (hv : Represents v r) :
    ∃ f : ℝ → EReal, Monotone f ∧ StrictMonoOn f (Set.range u) ∧
      ∀ x, f (u x) = (v x : EReal) :=
  ⟨ExtendedUtilityTransform u v, extendedUtilityTransform_monotone u v,
    extendedUtilityTransform_strictMonoOn hu hv, extendedUtilityTransform_apply hu hv⟩

/-- **Problem 1.14a**, p. 27: the represented relations coincide. -/
theorem problem_1_14a {s : X → X → Prop} (hu : Represents u r) (hv : Represents v s)
    {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.range u)) (hvu : ∀ x, v x = f (u x)) : r = s := by
  funext x y
  exact propext ((represents_of_transform_on_range hu hf hvu x y).trans (hv x y).symm)

/-- **Problem 1.14b**, p. 27: any given transformation is strict on attained values. -/
theorem problem_1_14b (hu : Represents u r) (hv : Represents v r)
    {f : ℝ → ℝ} (hvu : ∀ x, v x = f (u x)) : StrictMonoOn f (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [← hvu x, ← hvu y]
  exact (strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy)

/-- **Problem 1.14d**, p. 27: the actual supremum construction and both order properties. -/
theorem problem_1_14d (hu : Represents u r) (hv : Represents v r) :
    Monotone (ExtendedUtilityTransform u v) ∧
      StrictMonoOn (ExtendedUtilityTransform u v) (Set.range u) ∧
      ∀ x, ExtendedUtilityTransform u v (u x) = (v x : EReal) :=
  ⟨extendedUtilityTransform_monotone u v, extendedUtilityTransform_strictMonoOn hu hv,
    extendedUtilityTransform_apply hu hv⟩

end Kreps.PreferenceProperties
