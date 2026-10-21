/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Rationalization

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Finite utility representation

Kreps I, §1.3, pp. 7-8: no-better-than sets and their cardinalities provide the
utility representation in Proposition 1.8 and complete Proposition 1.2.
The inclusion results do not require a finite alternative space.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- Every alternative belongs to its own no-better-than set. -/
theorem mem_noBetterThan_self (hc : Complete r) (x : X) : x ∈ NoBetterThan r x :=
  complete_refl hc x

/-- **Proposition 1.7**, p. 8: preference is inclusion of lower contour sets. -/
theorem pref_iff_noBetterThan_subset (hr : Rational r) (x y : X) :
    r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x := by
  constructor
  · exact fun h z hz => hr.2 x y z h hz
  · exact fun h => h (mem_noBetterThan_self hr.1 y)

/-- Strict preference is strict inclusion of no-better-than sets. -/
theorem strict_iff_noBetterThan_ssubset (hr : Rational r) (x y : X) :
    Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x := by
  change (r x y ∧ ¬r y x) ↔ _
  rw [Set.ssubset_def, ← pref_iff_noBetterThan_subset hr x y,
    ← pref_iff_noBetterThan_subset hr y x]

/-- **Proposition 1.7**, p. 8: nonemptiness and the three nesting possibilities. -/
theorem proposition_1_7 (hr : Rational r) (x y : X) :
    (NoBetterThan r x).Nonempty ∧
      (r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x) ∧
      (Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x) ∧
      (NoBetterThan r x ⊂ NoBetterThan r y ∨
        NoBetterThan r y ⊂ NoBetterThan r x ∨ NoBetterThan r x = NoBetterThan r y) := by
  refine ⟨⟨x, mem_noBetterThan_self hr.1 x⟩, pref_iff_noBetterThan_subset hr x y,
    strict_iff_noBetterThan_ssubset hr x y, ?_⟩
  by_cases hxy : r x y
  · by_cases hyx : r y x
    · exact Or.inr (Or.inr (Set.Subset.antisymm
        ((pref_iff_noBetterThan_subset hr y x).mp hyx)
        ((pref_iff_noBetterThan_subset hr x y).mp hxy)))
    · exact Or.inr (Or.inl ((strict_iff_noBetterThan_ssubset hr x y).mp ⟨hxy, hyx⟩))
  · exact Or.inl ((strict_iff_noBetterThan_ssubset hr y x).mp
      ⟨(hr.1 x y).resolve_left hxy, hxy⟩)

/-- The book's cardinality utility; representation is asserted only for finite `X`. -/
noncomputable def FiniteUtility (r : X → X → Prop) (x : X) : ℝ :=
  (NoBetterThan r x).ncard

/-- **Proposition 1.8**, p. 8: cardinality of lower contours represents preference. -/
theorem proposition_1_8 [Finite X] (hr : Rational r) : Represents (FiniteUtility r) r := by
  intro x y
  constructor
  · intro hxy
    have h := Set.ncard_le_ncard ((pref_iff_noBetterThan_subset hr x y).mp hxy)
    unfold FiniteUtility
    exact_mod_cast h
  · intro h
    by_contra hxy
    have hyx := (hr.1 x y).resolve_left hxy
    have hlt := Set.ncard_lt_ncard
      ((strict_iff_noBetterThan_ssubset hr y x).mp ⟨hyx, hxy⟩)
    have hlt' : FiniteUtility r x < FiniteUtility r y := by
      unfold FiniteUtility
      exact_mod_cast hlt
    exact (not_lt_of_ge h) hlt'

/-- **Proposition 1.2b**, p. 4: rational finite preference has a utility representation. -/
theorem proposition_1_2b [Finite X] (hr : Rational r) :
    FiniteNonempty (PrefChoice r) ∧ Coherent (PrefChoice r) ∧
      ∃ u : X → ℝ, Represents u r :=
  ⟨(proposition_1_4 hr).1, (proposition_1_4 hr).2, FiniteUtility r, proposition_1_8 hr⟩

/-- On a finite alternative space every coherent feasible choice is rationalized exactly. -/
theorem finite_choice_eq_revealed [Finite X] {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) : c = PrefChoice (Revealed c) := by
  funext A
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [feasible_empty hf]
    simp [PrefChoice]
  · exact choice_eq_revealed_of_nonempty hf hn hc (hn A (Set.toFinite A) hA)

/-- **Proposition 1.2a**, p. 4: the same preferences and utility rationalize finite choice. -/
theorem proposition_1_2a [Finite X] {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    ∃ (u : X → ℝ) (r : X → X → Prop),
      Rational r ∧ Represents u r ∧ c = PrefChoice r ∧ c = UtilityChoice u := by
  have hr := (proposition_1_5 hf hn hc).1
  have hu := proposition_1_8 hr
  have hchoice := finite_choice_eq_revealed hf hn hc
  exact ⟨FiniteUtility (Revealed c), Revealed c, hr, hu, hchoice,
    hchoice.trans (represents_choice hu)⟩

/-- **Proposition 1.2c**, p. 4. This direction holds even for infinite `X`. -/
theorem proposition_1_2c (u : X → ℝ) :
    FiniteNonempty (UtilityChoice u) ∧ Coherent (UtilityChoice u) ∧
      Rational (UtilityPref u) ∧ PrefChoice (UtilityPref u) = UtilityChoice u :=
  ⟨(proposition_1_3b u).1, (proposition_1_3b u).2, proposition_1_3a u, rfl⟩

/-- **Problem 1.8**, p. 26, asks for the proof of Proposition 1.7. -/
theorem problem_1_8 (hr : Rational r) (x y : X) :
    (NoBetterThan r x).Nonempty ∧
      (r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x) ∧
      (Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x) :=
  ⟨(proposition_1_7 hr x y).1, (proposition_1_7 hr x y).2.1,
    (proposition_1_7 hr x y).2.2.1⟩

end Kreps.PreferenceProperties
