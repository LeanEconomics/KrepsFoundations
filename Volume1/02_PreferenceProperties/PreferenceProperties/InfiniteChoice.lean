/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Rationalization

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice from infinite menus

Kreps I, §1.6, pp. 15-17. Assumption 1.16 is exactly what is needed to eliminate
the empty-choice exception in Proposition 1.5. Emptying any family of infinite
menus preserves the original two choice conditions, as the book explains on p. 16.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- **Assumption 1.16**, p. 16: choose whenever a revealed greatest element exists. -/
def Assumption116 (c : ChoiceRule X) : Prop :=
  ∀ A x, x ∈ A → A ⊆ NoBetterThan (Revealed c) x → (c A).Nonempty

/-- **Proposition 1.17**, p. 17, in both directions. -/
theorem proposition_1_17 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    c = PrefChoice (Revealed c) ↔ Assumption116 c := by
  constructor
  · intro h A x hx hmax
    rw [h]
    exact ⟨x, hx, fun y hy => hmax hy⟩
  · intro h
    funext A
    ext x
    constructor
    · intro hx
      exact ⟨hf A hx, fun y hy => revealed_of_chosen hf hn hc hx hy⟩
    · rintro ⟨hx, hmax⟩
      have hne := h A x hx (fun y hy => hmax y hy)
      rw [choice_eq_revealed_of_nonempty hf hn hc hne]
      exact ⟨hx, hmax⟩

/-- **Proposition 1.18**, p. 17: no revealed greatest element implies empty choice. -/
theorem proposition_1_18 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X}
    (hA : ∀ x ∈ A, ¬A ⊆ NoBetterThan (Revealed c) x) : c A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hA x (hf A hx) (fun _ hy => revealed_of_chosen hf hn hc hx hy)

/-- Replace choice by the empty set on a specified family of menus. -/
noncomputable def EmptyMenus (c : ChoiceRule X) (E : Set (Set X)) : ChoiceRule X := by
  classical
  exact fun A => if A ∈ E then ∅ else c A

/-- Emptying menus preserves feasibility. -/
theorem emptyMenus_feasible {c : ChoiceRule X} (hf : Feasible c) (E : Set (Set X)) :
    Feasible (EmptyMenus c E) := by
  classical
  intro A x hx
  by_cases hA : A ∈ E
  · simp [EmptyMenus, hA] at hx
  · exact hf A (by simpa [EmptyMenus, hA] using hx)

/-- Emptying only infinite menus preserves finite nonemptiness. -/
theorem emptyMenus_finiteNonempty {c : ChoiceRule X} (hn : FiniteNonempty c)
    {E : Set (Set X)} (hE : ∀ A ∈ E, ¬A.Finite) : FiniteNonempty (EmptyMenus c E) := by
  classical
  intro A hfin hne
  have hA : A ∉ E := fun he => hE A he hfin
  simpa [EmptyMenus, hA] using hn A hfin hne

/-- The argument on p. 16: emptying any collection of menus preserves coherence. -/
theorem emptyMenus_coherent {c : ChoiceRule X} (hc : Coherent c) (E : Set (Set X)) :
    Coherent (EmptyMenus c E) := by
  classical
  intro A B x hx y hy hxc hyc hyB
  by_cases hA : A ∈ E
  · simp [EmptyMenus, hA] at hxc
  · by_cases hB : B ∈ E
    · simp [EmptyMenus, hB] at hyB
    · exact hc A B x hx y hy (by simpa [EmptyMenus, hA] using hxc)
        (by simpa [EmptyMenus, hA] using hyc) (by simpa [EmptyMenus, hB] using hyB)

/-- Full formalization of the arbitrary infinite-menu modification on p. 16. -/
theorem empty_infinite_menus_preserves_choice {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {E : Set (Set X)}
    (hE : ∀ A ∈ E, ¬A.Finite) :
    Feasible (EmptyMenus c E) ∧ FiniteNonempty (EmptyMenus c E) ∧
      Coherent (EmptyMenus c E) :=
  ⟨emptyMenus_feasible hf E, emptyMenus_finiteNonempty hn hE, emptyMenus_coherent hc E⟩

end Kreps.PreferenceProperties
