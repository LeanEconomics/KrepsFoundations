/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Logic.Function.Basic

/-!
# Selecting shared essential companions

Three distinct essential coordinates suffice to assign two companions to every target
coordinate, so that every pair of targets shares a companion different from both. This
elementary selection synchronizes the independently continued scales in Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

/-- Three distinct anchors supply two companions per target with a shared companion per pair. -/
theorem exists_shared_companions {I : Type*} {a b c : I}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ first second : I → I,
      (∀ i, first i ≠ i ∧ second i ≠ i ∧ first i ≠ second i) ∧
      ∀ i j, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j ∧
        (k = first i ∨ k = second i) ∧ (k = first j ∨ k = second j) := by
  classical
  let first : I → I := fun i => if i = a then b else a
  let second : I → I := fun i => if i = a ∨ i = b then c else b
  have hc : ∀ i, first i ≠ i ∧ second i ≠ i ∧ first i ≠ second i := by
    intro i
    by_cases hi : i = a
    · subst i
      simp [first, second, hab, hbc, Ne.symm hab, Ne.symm hac]
    · by_cases hib : i = b
      · subst i
        simp [first, second, hab, hac, Ne.symm hab, Ne.symm hbc]
      · simp [first, second, hi, hib, hab, Ne.symm hi, Ne.symm hib]
  refine ⟨first, second, hc, fun i j hij => ?_⟩
  by_cases hi : i = a
  · subst i
    have hja : j ≠ a := Ne.symm hij
    by_cases hjb : j = b
    · subst j
      exact ⟨c, Ne.symm hac, Ne.symm hbc, by simp [second], by simp [second]⟩
    · exact ⟨b, Ne.symm hab, Ne.symm hjb, by simp [first], by simp [second, hja, hjb]⟩
  · by_cases hj : j = a
    · subst j
      by_cases hib : i = b
      · subst i
        exact ⟨c, Ne.symm hbc, Ne.symm hac, by simp [second], by simp [second]⟩
      · exact ⟨b, Ne.symm hib, Ne.symm hab, by simp [second, hi, hib], by simp [first]⟩
    · exact ⟨a, Ne.symm hi, Ne.symm hj, by simp [first, hi], by simp [first, hj]⟩

end Kreps.PreferenceProperties
