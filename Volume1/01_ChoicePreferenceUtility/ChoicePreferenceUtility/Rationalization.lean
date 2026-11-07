/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Basic

/-!
# Rationalization of choice

Kreps I, §1.2, Propositions 1.3-1.5, pp. 5-7. The alternative space is arbitrary.
Finite nonemptiness does not assert nonemptiness on infinite menus. The final result
therefore preserves the book's disjunction: empty choice or exact rationalization.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- **Proposition 1.3a**, p. 5. Utility induces complete, transitive preference. -/
theorem proposition_1_3a (u : X → ℝ) : Rational (UtilityPref u) := by
  constructor
  · exact fun x y => le_total (u y) (u x)
  · exact fun _ _ _ hxy hyz => le_trans hyz hxy

/-- Finite-set induction supplies a preference maximum without a utility function. -/
theorem prefChoice_finiteNonempty {r : X → X → Prop} (hr : Rational r) :
    FiniteNonempty (PrefChoice r) := by
  intro A hA
  induction A, hA using Set.Finite.induction_on with
  | empty =>
    intro h
    exact (Set.not_nonempty_empty h).elim
  | @insert a s _ _ ih =>
    intro _
    by_cases hn : s.Nonempty
    · obtain ⟨b, hb, hmax⟩ := ih hn
      rcases hr.1 a b with hab | hba
      · refine ⟨a, Set.mem_insert a s, ?_⟩
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hys
        · exact complete_refl hr.1 _
        · exact hr.2 a b y hab (hmax y hys)
      · refine ⟨b, Set.mem_insert_of_mem a hb, ?_⟩
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hys
        · exact hba
        · exact hmax y hys
    · have hs : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      subst s
      refine ⟨a, by simp, ?_⟩
      intro y hy
      have hy' : y = a := by simpa using hy
      subst y
      exact complete_refl hr.1 a

/-- Transitivity alone suffices for coherence of preference maximization. -/
theorem prefChoice_coherent {r : X → X → Prop} (ht : TransitivePref r) :
    Coherent (PrefChoice r) := by
  intro A B x hx y hy hxc hyc hyB
  apply hyc
  exact ⟨hy.1, fun z hz => ht y x z (hyB.2 x hx.2) (hxc.2 z hz)⟩

/-- **Proposition 1.3b**, p. 5. Utility choice is finite-nonempty and coherent. -/
theorem proposition_1_3b (u : X → ℝ) :
    FiniteNonempty (UtilityChoice u) ∧ Coherent (UtilityChoice u) :=
  ⟨prefChoice_finiteNonempty (proposition_1_3a u),
    prefChoice_coherent (proposition_1_3a u).2⟩

/-- **Proposition 1.4**, pp. 5-6. Rational preference generates coherent choice. -/
theorem proposition_1_4 {r : X → X → Prop} (hr : Rational r) :
    FiniteNonempty (PrefChoice r) ∧ Coherent (PrefChoice r) :=
  ⟨prefChoice_finiteNonempty hr, prefChoice_coherent hr.2⟩

/-- The symmetric formulation of coherence in the footnote on p. 4. -/
theorem coherent_exchange {c : ChoiceRule X} (hc : Coherent c)
    {A B : Set X} {x y : X} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B)
    (hxc : x ∈ c A) (hyc : y ∈ c B) : x ∈ c B ∧ y ∈ c A := by
  constructor
  · by_contra h
    exact hc B A y ⟨hy.2, hy.1⟩ x ⟨hx.2, hx.1⟩ hyc h hxc
  · by_contra h
    exact hc A B x hx y hy hxc h hyc

/-- A chosen alternative wins every feasible pairwise comparison. -/
theorem revealed_of_chosen {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X} {x y : X}
    (hx : x ∈ c A) (hy : y ∈ A) : Revealed c x y := by
  obtain ⟨z, hz⟩ := hn {x, y} (by simp) (by simp)
  have hzmem : z ∈ ({x, y} : Set X) := hf _ hz
  have hzA : z ∈ A := by
    rcases Set.mem_insert_iff.mp hzmem with rfl | hz'
    · exact hf A hx
    · simpa only [Set.mem_singleton_iff.mp hz'] using hy
  exact (coherent_exchange hc ⟨hf A hx, by simp⟩ ⟨hzA, hzmem⟩ hx hz).1

/-- A revealed weak improvement on a chosen alternative is also chosen. -/
theorem chosen_of_revealed {c : ChoiceRule X} (hc : Coherent c)
    {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : Revealed c x y) (hyc : y ∈ c A) : x ∈ c A :=
  (coherent_exchange hc ⟨by simp, hx⟩ ⟨by simp, hy⟩ hxy hyc).1

/-- Pairwise nonemptiness makes revealed preference complete. -/
theorem revealed_complete {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) : Complete (Revealed c) := by
  intro x y
  obtain ⟨z, hz⟩ := hn {x, y} (by simp) (by simp)
  rcases Set.mem_insert_iff.mp (hf _ hz) with rfl | hz'
  · exact Or.inl hz
  · have hz' : z = y := Set.mem_singleton_iff.mp hz'
    subst z
    right
    simpa only [Revealed, Set.pair_comm y x] using hz

/-- Coherence and finite nonemptiness make revealed preference transitive. -/
theorem revealed_transitive {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) : TransitivePref (Revealed c) := by
  intro x y z hxy hyz
  obtain ⟨w, hw⟩ := hn {x, y, z} (by simp) (by simp)
  have hx : x ∈ c {x, y, z} := by
    have hwmem := hf {x, y, z} hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with hwx | hwy | hwz
    · subst w
      exact hw
    · subst w
      exact chosen_of_revealed hc (by simp) (by simp) hxy hw
    · subst w
      have hy : y ∈ c {x, y, z} :=
        chosen_of_revealed hc (by simp) (by simp) hyz hw
      exact chosen_of_revealed hc (by simp) (by simp) hxy hy
  exact revealed_of_chosen hf hn hc hx (by simp)

/-- Nonempty choice agrees exactly with maximization of revealed preference. -/
theorem choice_eq_revealed_of_nonempty {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X} (hA : (c A).Nonempty) :
    c A = PrefChoice (Revealed c) A := by
  ext x
  constructor
  · intro hx
    exact ⟨hf A hx, fun y hy => revealed_of_chosen hf hn hc hx hy⟩
  · rintro ⟨hx, hmax⟩
    obtain ⟨y, hy⟩ := hA
    exact chosen_of_revealed hc hx (hf A hy) (hmax y (hf A hy)) hy

/-- **Proposition 1.5**, pp. 6-7, including the infinite-menu exception. -/
theorem proposition_1_5 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    Rational (Revealed c) ∧
      FiniteNonempty (PrefChoice (Revealed c)) ∧ Coherent (PrefChoice (Revealed c)) ∧
      ∀ A, c A = ∅ ∨ c A = PrefChoice (Revealed c) A := by
  have hr : Rational (Revealed c) :=
    ⟨revealed_complete hf hn, revealed_transitive hf hn hc⟩
  refine ⟨hr, (proposition_1_4 hr).1, (proposition_1_4 hr).2, ?_⟩
  intro A
  rcases (c A).eq_empty_or_nonempty with hA | hA
  · exact Or.inl hA
  · exact Or.inr (choice_eq_revealed_of_nonempty hf hn hc hA)

end Kreps.ChoicePreferenceUtility
