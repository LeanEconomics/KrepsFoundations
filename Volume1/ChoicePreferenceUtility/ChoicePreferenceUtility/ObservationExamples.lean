/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.SGARP

/-!
# Limits of observing choice

Kreps I, Problem 1.16a-b, p. 28. If unobserved ties are allowed, constant utility
accommodates every feasible selection. If full chosen sets are observed on only
the pair menus, coherence on those observations need not imply rationalizability.
-/

namespace Kreps.ChoicePreferenceUtility

/-- **Problem 1.16a**: constant utility accommodates any feasible observed selections. -/
theorem problem_1_16a {X I : Type*} (menus chosen : I → Set X)
    (hf : ∀ i, chosen i ⊆ menus i) :
    ∃ u : X → ℝ, ∀ i, chosen i ⊆ UtilityChoice u (menus i) := by
  refine ⟨fun _ => 0, fun i x hx => ?_⟩
  exact ⟨hf i hx, fun _ _ => le_rfl⟩

/-- Coherence expressed directly on an indexed family of observations. -/
def ObservedCoherence {X I : Type*} (menus chosen : I → Set X) : Prop :=
  ∀ i j x y, x ∈ menus i ∩ menus j → y ∈ menus i ∩ menus j →
    x ∈ chosen i → y ∉ chosen i → y ∉ chosen j

/-- All three pair menus in the cycle example. -/
def CyclicMenus (i : Fin 3) : Set (Fin 3) :=
  if i = 0 then {0, 1} else if i = 1 then {1, 2} else {2, 0}

/-- Each menu selects its first alternative, producing the cycle zero, one, two, zero. -/
def CyclicChoices (i : Fin 3) : Set (Fin 3) := {i}

/-- The three observed menus are distinct, so these data define a partial choice function. -/
theorem cyclicMenus_injective : Function.Injective CyclicMenus := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [CyclicMenus, Set.ext_iff, Fin.forall_fin_succ] at h ⊢

/-- The cyclic observations are feasible and nonempty. -/
theorem cyclicChoices_valid :
    (∀ i, CyclicChoices i ⊆ CyclicMenus i) ∧ (∀ i, (CyclicChoices i).Nonempty) := by
  constructor
  · intro i
    fin_cases i <;> simp [CyclicChoices, CyclicMenus]
  · intro i
    exact Set.singleton_nonempty i

/-- **Problem 1.16b**: the pairwise observations satisfy coherence on the observed domain. -/
theorem cyclicChoices_coherent : ObservedCoherence CyclicMenus CyclicChoices := by
  intro i j x y hx hy hxc hyc
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;>
    simp [CyclicChoices, CyclicMenus] at *

/-- **Problem 1.16b**: nevertheless no complete, transitive preference rationalizes the data. -/
theorem problem_1_16b_not_rationalizable :
    ¬∃ r : Fin 3 → Fin 3 → Prop, Rational r ∧ RationalizesData r CyclicMenus CyclicChoices := by
  rintro ⟨r, hr, he⟩
  have h01 : ObservedWeak CyclicMenus CyclicChoices 0 1 :=
    ⟨0, by simp [CyclicChoices], by simp [CyclicMenus]⟩
  have h12 : ObservedWeak CyclicMenus CyclicChoices 1 2 :=
    ⟨1, by simp [CyclicChoices], by simp [CyclicMenus]⟩
  have h20 : ObservedStrict CyclicMenus CyclicChoices 2 0 :=
    ⟨2, by simp [CyclicChoices], by simp [CyclicMenus], by simp [CyclicChoices]⟩
  exact sgarp_of_rationalizes hr he 0 2
    ((Relation.ReflTransGen.single h01).trans (Relation.ReflTransGen.single h12)) h20

end Kreps.ChoicePreferenceUtility
