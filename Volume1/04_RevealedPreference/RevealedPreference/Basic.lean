/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Preference prerequisites for finite demand data

Selected prerequisite definitions and proofs from `PreferenceProperties.Basic`,
`StrictPreference`, `Rationalization` and `CountableUtility`, originating at commit
`7d496c5`. The namespace and imports are local to this independent chapter.
Kreps I, pp. 3-11, supplies the rationality and numerical-representation conventions
used throughout Chapter 4, pp. 67-78.
-/

namespace Kreps.RevealedPreference

variable {X : Type*} {r : X → X → Prop}

/-- Every pair of alternatives can be compared. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- Weak preference is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- The standing complete-and-transitive preference assumption. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Strict preference is weak preference without its converse. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference is weak preference in both directions. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- All feasible alternatives weakly preferred to every member of the menu. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Numerical utility induces the book's orientation of weak preference. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- A numerical utility represents all and only the weak comparisons. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Completeness includes reflexivity. -/
theorem complete_refl (hc : Complete r) (x : X) : r x x := (hc x x).elim id id

/-- A strict comparison followed by a weak comparison remains strict. -/
theorem strict_weak_trans (ht : TransitivePref r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨ht x y z hxy.1 hyz, fun hzx => hxy.2 (ht y z x hyz hzx)⟩

/-- A weak comparison followed by a strict comparison remains strict. -/
theorem weak_strict_trans (ht : TransitivePref r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨ht x y z hxy hyz.1, fun hzx => hyz.2 (ht z x y hzx hxy)⟩

/-- Numerical preference is always complete and transitive. -/
theorem utilityPref_rational (u : X → ℝ) : Rational (UtilityPref u) := by
  constructor
  · exact fun x y => le_total (u y) (u x)
  · exact fun _ _ _ hxy hyz => le_trans hyz hxy

/-- A represented preference is rational. -/
theorem represents_rational {u : X → ℝ} (hu : Represents u r) : Rational r := by
  constructor
  · intro x y
    exact (le_total (u y) (u x)).imp ((hu x y).mpr) ((hu y x).mpr)
  · intro x y z hxy hyz
    exact (hu x z).mpr (((hu y z).mp hyz).trans ((hu x y).mp hxy))

/-- Strict preference corresponds exactly to strict inequality of represented utilities. -/
theorem strict_iff_utility_lt {u : X → ℝ} (hu : Represents u r) (x y : X) :
    Strict r x y ↔ u y < u x := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hle => h.2 ((hu y x).mpr hle))
  · intro h
    exact ⟨(hu x y).mpr h.le, fun hyx => (not_le_of_gt h) ((hu y x).mp hyx)⟩

end Kreps.RevealedPreference
