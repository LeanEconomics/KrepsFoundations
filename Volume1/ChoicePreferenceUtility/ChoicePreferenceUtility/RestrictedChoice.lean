/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Rationalization

/-!
# Rationalization on a restricted menu domain

Kreps I, Problem 1.15, p. 27. Observing every menu with at most three alternatives
is enough when admissible menus have nonempty choice and coherence holds on that
domain. No assumption is made about choice on unobserved menus.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*} {menus : Set (Set X)} {c : ChoiceRule X}

/-- The domain includes all one-, two-, and three-element menus (allowing repetitions). -/
def ContainsSmallMenus (menus : Set (Set X)) : Prop :=
  (∀ x, {x} ∈ menus) ∧ (∀ x y, {x, y} ∈ menus) ∧ (∀ x y z, {x, y, z} ∈ menus)

/-- Nonemptiness is assumed exactly on the admissible domain. -/
def NonemptyOn (menus : Set (Set X)) (c : ChoiceRule X) : Prop :=
  ∀ A ∈ menus, (c A).Nonempty

/-- Symmetric exchange using only two admissible menus. -/
theorem coherentOn_exchange (hc : CoherentOn menus c) {A B : Set X}
    (hA : A ∈ menus) (hB : B ∈ menus) {x y : X}
    (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hxc : x ∈ c A) (hyc : y ∈ c B) :
    x ∈ c B ∧ y ∈ c A := by
  constructor
  · by_contra h
    exact hc B hB A hA y ⟨hy.2, hy.1⟩ x ⟨hx.2, hx.1⟩ hyc h hxc
  · by_contra h
    exact hc A hA B hB x hx y hy hxc h hyc

/-- Every chosen alternative wins each admissible pairwise comparison. -/
theorem restricted_revealed_of_chosen (hs : ContainsSmallMenus menus)
    (hf : FeasibleOn menus c) (hn : NonemptyOn menus c) (hc : CoherentOn menus c)
    {A : Set X} (hA : A ∈ menus) {x y : X} (hx : x ∈ c A) (hy : y ∈ A) :
    Revealed c x y := by
  have hp := hs.2.1 x y
  obtain ⟨z, hz⟩ := hn {x, y} hp
  have hzmem := hf _ hp hz
  have hzA : z ∈ A := by
    rcases Set.mem_insert_iff.mp hzmem with hzx | hzy
    · exact hzx ▸ hf A hA hx
    · exact (Set.mem_singleton_iff.mp hzy) ▸ hy
  exact (coherentOn_exchange hc hA hp ⟨hf A hA hx, by simp⟩ ⟨hzA, hzmem⟩ hx hz).1

/-- An admissible-menu choice can be replaced by a revealed weak improvement. -/
theorem restricted_chosen_of_revealed (hs : ContainsSmallMenus menus)
    (hc : CoherentOn menus c) {A : Set X} (hA : A ∈ menus) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : Revealed c x y) (hyc : y ∈ c A) : x ∈ c A :=
  (coherentOn_exchange hc (hs.2.1 x y) hA ⟨by simp, hx⟩ ⟨by simp, hy⟩ hxy hyc).1

/-- Pairwise observations suffice for completeness. -/
theorem restricted_revealed_complete (hs : ContainsSmallMenus menus)
    (hf : FeasibleOn menus c) (hn : NonemptyOn menus c) : Complete (Revealed c) := by
  intro x y
  obtain ⟨z, hz⟩ := hn {x, y} (hs.2.1 x y)
  rcases Set.mem_insert_iff.mp (hf _ (hs.2.1 x y) hz) with hzx | hzy
  · subst z
    exact Or.inl hz
  · have hzy' : z = y := Set.mem_singleton_iff.mp hzy
    subst z
    right
    simpa only [Revealed, Set.pair_comm y x] using hz

/-- Three-alternative observations and coherence imply transitivity. -/
theorem restricted_revealed_transitive (hs : ContainsSmallMenus menus)
    (hf : FeasibleOn menus c) (hn : NonemptyOn menus c) (hc : CoherentOn menus c) :
    TransitivePref (Revealed c) := by
  intro x y z hxy hyz
  have ht := hs.2.2 x y z
  obtain ⟨w, hw⟩ := hn {x, y, z} ht
  have hx : x ∈ c {x, y, z} := by
    have hwmem := hf _ ht hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with hwx | hwy | hwz
    · subst w
      exact hw
    · subst w
      exact restricted_chosen_of_revealed hs hc ht (by simp) (by simp) hxy hw
    · subst w
      have hy := restricted_chosen_of_revealed hs hc ht (by simp) (by simp) hyz hw
      exact restricted_chosen_of_revealed hs hc ht (by simp) (by simp) hxy hy
  exact restricted_revealed_of_chosen hs hf hn hc ht hx (by simp)

/-- **Problem 1.15**, p. 27: rationality and exact rationalization on every admissible menu. -/
theorem problem_1_15 (hs : ContainsSmallMenus menus) (hf : FeasibleOn menus c)
    (hn : NonemptyOn menus c) (hc : CoherentOn menus c) :
    Rational (Revealed c) ∧ ∀ A ∈ menus, c A = PrefChoice (Revealed c) A := by
  refine ⟨⟨restricted_revealed_complete hs hf hn,
    restricted_revealed_transitive hs hf hn hc⟩, ?_⟩
  intro A hA
  ext x
  constructor
  · intro hx
    exact ⟨hf A hA hx, fun y hy => restricted_revealed_of_chosen hs hf hn hc hA hx hy⟩
  · rintro ⟨hx, hmax⟩
    obtain ⟨y, hy⟩ := hn A hA
    exact restricted_chosen_of_revealed hs hc hA hx (hf A hA hy)
      (hmax y (hf A hA hy)) hy

end Kreps.ChoicePreferenceUtility
