/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationCountableUtility
import Mathlib.Analysis.Real.Cardinality

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Lexicographic preferences have no real utility representation

Kreps I, Problem 1.10, p. 26. On the unit square these preferences are complete
and transitive. A putative representation would put disjoint nonempty utility
intervals above each first coordinate; selecting a rational inside each interval
would inject the uncountable unit interval into the rationals.
-/

namespace Kreps.ConsumerDemand.Representation

/-- The closed real unit interval, including both endpoints. -/
abbrev UnitSegment := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

/-- Lexicographic weak preference on the unit square. -/
def LexicographicPreference (x y : UnitSegment × UnitSegment) : Prop :=
  y.1.val < x.1.val ∨ y.1.val = x.1.val ∧ y.2.val ≤ x.2.val

/-- **Problem 1.10**, completeness and transitivity. -/
theorem lexicographic_rational : Rational LexicographicPreference := by
  constructor
  · intro x y
    rcases lt_trichotomy x.1.val y.1.val with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total y.2.val x.2.val with hyx | hxy
      · exact Or.inl (Or.inr ⟨h.symm, hyx⟩)
      · exact Or.inr (Or.inr ⟨h, hxy⟩)
    · exact Or.inl (Or.inl h)
  · rintro x y z (hxy | ⟨hexy, hxy⟩) (hyz | ⟨heyz, hyz⟩)
    · exact Or.inl (hyz.trans hxy)
    · left
      linarith
    · left
      linarith
    · exact Or.inr ⟨heyz.trans hexy, hyz.trans hxy⟩

/-- **Problem 1.10**, impossibility of any real-valued utility representation. -/
theorem lexicographic_not_representable :
    ¬∃ u : UnitSegment × UnitSegment → ℝ, Represents u LexicographicPreference := by
  classical
  rintro ⟨u, hu⟩
  let zero : UnitSegment := ⟨0, by constructor <;> norm_num⟩
  let one : UnitSegment := ⟨1, by constructor <;> norm_num⟩
  have hv (x : UnitSegment) : u (x, zero) < u (x, one) := by
    apply (strict_iff_utility_lt hu (x, one) (x, zero)).mp
    constructor
    · right
      exact ⟨rfl, by norm_num [zero, one]⟩
    · rintro (h | ⟨_, h⟩)
      · exact (lt_irrefl _) h
      · norm_num [zero, one] at h
  choose q hqlo hqhi using fun x => exists_rat_btwn (hv x)
  have hqmono : StrictMono q := by
    intro x y hxy
    have hxy' : x.val < y.val := hxy
    have hs : Strict LexicographicPreference (y, zero) (x, one) := by
      constructor
      · exact Or.inl hxy'
      · rintro (h | ⟨h, _⟩) <;> dsimp at h <;> linarith
    have hsep := (strict_iff_utility_lt hu (y, zero) (x, one)).mp hs
    have hq : (q x : ℝ) < (q y : ℝ) := (hqhi x).trans (hsep.trans (hqlo y))
    exact_mod_cast hq
  have hcount : Countable UnitSegment := hqmono.injective.countable
  have hset : (Set.Icc (0 : ℝ) 1).Countable := hcount
  have hbad := Cardinal.Real.Icc_countable_iff.mp hset
  norm_num at hbad

/-- **Problem 1.10**, its two requested conclusions together. -/
theorem problem_1_10 : Rational LexicographicPreference ∧
    ¬∃ u : UnitSegment × UnitSegment → ℝ, Represents u LexicographicPreference :=
  ⟨lexicographic_rational, lexicographic_not_representable⟩

end Kreps.ConsumerDemand.Representation
