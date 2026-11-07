/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Appendix 1: Mathematical Induction

Kreps I, Appendix 1, pp. 439-440. The book's ordinary and strong induction
principles are bridged to Lean's inductive natural numbers. Its even-or-odd example
is proved by induction, integer induction is established in both directions, and
the absence of an immediate next real number explains the final cautionary example.
-/

namespace Kreps.ChoicePreferenceUtility

/-- Ordinary induction starting at zero. -/
theorem appendix_A1_nat_induction (P : ℕ → Prop) (h0 : P 0)
    (hs : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

/-- The strong form used in the book, with all earlier cases in the induction hypothesis. -/
theorem appendix_A1_strong_induction (P : ℕ → Prop) (h0 : P 0)
    (hs : ∀ n, (∀ m ≤ n, P m) → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n => exact hs n (fun m hm => ih m (Nat.lt_succ_iff.mpr hm))

/-- Induction on positive integers starts with the case one. -/
theorem appendix_A1_positive_induction (P : ℕ → Prop) (h1 : P 1)
    (hs : ∀ n, 1 ≤ n → P n → P (n + 1)) : ∀ n, 1 ≤ n → P n := by
  intro n hn
  exact Nat.le_induction h1 (fun k hk ih => hs k hk ih) n hn

/-- The worked example on p. 439, with an explicit factor witnessing parity. -/
theorem appendix_A1_even_or_odd (n : ℕ) :
    (∃ m : ℕ, n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inr ⟨m, by omega⟩
    · exact Or.inl ⟨m + 1, by omega⟩

/-- The even and odd possibilities are mutually exclusive. -/
theorem appendix_A1_parity_exclusive (n : ℕ) :
    ¬((∃ m : ℕ, n = 2 * m) ∧ (∃ m : ℕ, n = 2 * m + 1)) := by
  rintro ⟨⟨m, hm⟩, ⟨k, hk⟩⟩
  omega

/-- Induction up and down from zero covers every integer, as described on pp. 439-440. -/
theorem appendix_A1_integer_induction (P : ℤ → Prop) (h0 : P 0)
    (hup : ∀ z, 0 ≤ z → P z → P (z + 1))
    (hdown : ∀ z, z ≤ 0 → P z → P (z - 1)) : ∀ z, P z := by
  have hp : ∀ n : ℕ, P (n : ℤ) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact hup (n : ℤ) (Int.natCast_nonneg n) ih
  have hn : ∀ n : ℕ, P (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have hh := hdown (-(n : ℤ)) (by omega) ih
      convert hh using 1
      push_cast
      ring
  intro z
  cases z with
  | ofNat n => exact hp n
  | negSucc n => exact hn (n + 1)

/-- There is no immediate next real number: every strict interval contains another real. -/
theorem appendix_A1_no_next_real (x y : ℝ) (hxy : x < y) : ∃ z : ℝ, x < z ∧ z < y :=
  exists_between hxy

/-- The cautionary example has a valid base case: zero is rational. -/
theorem appendix_A1_zero_rational : ∃ q : ℚ, (q : ℝ) = 0 := ⟨0, by norm_num⟩

/-- Nevertheless the proposed conclusion about all nonnegative reals is false. -/
theorem appendix_A1_not_all_nonnegative_rational :
    ¬∀ x : ℝ, 0 ≤ x → ∃ q : ℚ, (q : ℝ) = x := by
  intro h
  exact irrational_sqrt_two (h (Real.sqrt 2) (Real.sqrt_nonneg 2))

end Kreps.ChoicePreferenceUtility
