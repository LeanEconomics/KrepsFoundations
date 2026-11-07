/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.StrictPreference

/-!
# Strict preference, positive indifference, and incomparability

Kreps I, Problem 1.17a-e, p. 29. The four proposed conditions recover a reflexive,
transitive weak relation, without completeness. A fixed utility threshold satisfies
the conditions, but they are insufficient for such a representation. The two-plus-two
counterexample refutes representation even before requiring equality for indifference.
The additional characterization requested in part f is proved in `ThresholdRepresentation`.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- The four conditions on strict preference and positive indifference from Problem 1.17. -/
structure PartialPreferenceAxioms (s i : X → X → Prop) : Prop where
  strict_asymm : AsymmetricPref s
  strict_trans : TransitivePref s
  indiff_refl : ∀ x, i x x
  indiff_symm : ∀ x y, i x y → i y x
  indiff_trans : TransitivePref i
  strict_indiff_trans : ∀ x y z, s x y → i y z → s x z
  indiff_strict_trans : ∀ x y z, i x y → s y z → s x z

/-- Weak preference as positive strict preference or positive indifference. -/
def PartialWeak (s i : X → X → Prop) (x y : X) : Prop := s x y ∨ i x y

/-- **Problem 1.17a**: strict preference excludes either direction of indifference. -/
theorem problem_1_17a {s i : X → X → Prop} (h : PartialPreferenceAxioms s i)
    {x y : X} (hxy : s x y) : ¬i y x ∧ ¬i x y := by
  have hnot : ¬i y x := by
    intro hyx
    have hxx := h.strict_indiff_trans x y x hxy hyx
    exact h.strict_asymm x x hxx hxx
  exact ⟨hnot, fun hi => hnot (h.indiff_symm x y hi)⟩

/-- **Problem 1.17b**: the constructed weak relation is reflexive and transitive. -/
theorem problem_1_17b {s i : X → X → Prop} (h : PartialPreferenceAxioms s i) :
    (∀ x, PartialWeak s i x x) ∧ TransitivePref (PartialWeak s i) := by
  refine ⟨fun x => Or.inr (h.indiff_refl x), ?_⟩
  rintro x y z (hxy | hxy) (hyz | hyz)
  · exact Or.inl (h.strict_trans x y z hxy hyz)
  · exact Or.inl (h.strict_indiff_trans x y z hxy hyz)
  · exact Or.inl (h.indiff_strict_trans x y z hxy hyz)
  · exact Or.inr (h.indiff_trans x y z hxy hyz)

/-- Pure equality, with no strict comparisons, satisfies all four conditions. -/
theorem equality_partial_axioms (X : Type*) :
    PartialPreferenceAxioms (fun _ _ : X => False) (· = ·) := by
  constructor
  · exact fun _ _ h => h.elim
  · exact fun _ _ _ h _ => h.elim
  · exact fun _ => rfl
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ hxy hyz => hxy.trans hyz
  · exact fun _ _ _ h _ => h.elim
  · exact fun _ _ _ _ h => h.elim

/-- **Problem 1.17b**: two distinct alternatives can remain incomparable. -/
theorem problem_1_17b_not_complete :
    ¬Complete (PartialWeak (fun _ _ : Bool => False) (· = ·)) := by
  intro hc
  have h := hc true false
  simp [PartialWeak] at h

/-- Reconstructing weak preference from its strict part and indifference recovers any relation. -/
theorem partialWeak_strict_indifferent (r : X → X → Prop) :
    PartialWeak (Strict r) (Indifferent r) = r := by
  funext x y
  apply propext
  simp only [PartialWeak, Strict, Indifferent]
  tauto

/-- **Problem 1.17c**: precisely reflexivity and transitivity of the primitive weak relation. -/
theorem problem_1_17c (r : X → X → Prop) :
    PartialPreferenceAxioms (Strict r) (Indifferent r) ↔
      (∀ x, r x x) ∧ TransitivePref r := by
  constructor
  · intro h
    refine ⟨fun x => (h.indiff_refl x).1, ?_⟩
    have ht := (problem_1_17b h).2
    rwa [partialWeak_strict_indifferent r] at ht
  · rintro ⟨href, ht⟩
    exact ⟨proposition_1_9b r, proposition_1_9h ht, fun x => ⟨href x, href x⟩,
      fun _ _ h => proposition_1_9e h,
      fun _ _ _ hxy hyz => proposition_1_9f ht hxy hyz,
      fun _ _ _ hxy hyz => strict_weak_trans ht hxy hyz.1,
      fun _ _ _ hxy hyz => weak_strict_trans ht hxy.1 hyz⟩

/-- Strict preference requires a utility improvement strictly greater than one. -/
def ThresholdPreference (u : X → ℝ) (x y : X) : Prop := u y + 1 < u x

/-- Positive indifference means equal utility, not merely a difference below the threshold. -/
def EqualUtility (u : X → ℝ) (x y : X) : Prop := u x = u y

/-- **Problem 1.17d**: the threshold model satisfies every proposed condition. -/
theorem problem_1_17d (u : X → ℝ) :
    PartialPreferenceAxioms (ThresholdPreference u) (EqualUtility u) := by
  constructor
  · intro x y hxy hyx
    dsimp [ThresholdPreference] at hxy hyx
    linarith
  · intro x y z hxy hyz
    dsimp [ThresholdPreference] at *
    linarith
  · exact fun _ => rfl
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ hxy hyz => hxy.trans hyz
  · intro x y z hxy hyz
    dsimp [ThresholdPreference, EqualUtility] at *
    linarith
  · intro x y z hxy hyz
    dsimp [ThresholdPreference, EqualUtility] at *
    linarith

/-- Two unrelated strict comparisons on four alternatives. -/
def TwoPlusTwo (x y : Fin 4) : Prop := (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = 3)

/-- The two-plus-two strict relation and identity indifference satisfy the proposed conditions. -/
theorem twoPlusTwo_axioms : PartialPreferenceAxioms TwoPlusTwo (· = ·) := by
  constructor
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [TwoPlusTwo]
  · rintro x y z (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) hyz <;> norm_num [TwoPlusTwo] at hyz
  · exact fun _ => rfl
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ hxy hyz => hxy.trans hyz
  · rintro x y z hxy rfl
    exact hxy
  · rintro x y z rfl hyz
    exact hyz

/-- Two-plus-two admits no fixed-threshold representation, irrespective of indifference. -/
theorem twoPlusTwo_not_threshold :
    ¬∃ u : Fin 4 → ℝ, ∀ x y, TwoPlusTwo x y ↔ ThresholdPreference u x y := by
  rintro ⟨u, hu⟩
  have h01 : u 1 + 1 < u 0 := (hu 0 1).mp (by simp [TwoPlusTwo])
  have h23 : u 3 + 1 < u 2 := (hu 2 3).mp (by simp [TwoPlusTwo])
  have h03 : u 0 ≤ u 3 + 1 := by
    apply le_of_not_gt
    intro h
    have hh := (hu 0 3).mpr h
    norm_num [TwoPlusTwo] at hh
  have h21 : u 2 ≤ u 1 + 1 := by
    apply le_of_not_gt
    intro h
    have hh := (hu 2 1).mpr h
    norm_num [TwoPlusTwo] at hh
  linarith

/-- **Problem 1.17e**, a complete counterexample to the requested representation. -/
theorem problem_1_17e : PartialPreferenceAxioms TwoPlusTwo (· = ·) ∧
    ¬∃ u : Fin 4 → ℝ,
      (∀ x y, x = y ↔ EqualUtility u x y) ∧
        (∀ x y, TwoPlusTwo x y ↔ ThresholdPreference u x y) :=
  ⟨twoPlusTwo_axioms, fun ⟨u, _, hs⟩ => twoPlusTwo_not_threshold ⟨u, hs⟩⟩

end Kreps.ChoicePreferenceUtility
