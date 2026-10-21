/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.PartialPreference
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# A chain criterion for fixed-threshold representation

Kreps I, Problem 1.17f, p. 29. The criterion uses only comparisons
and integer scores. Indifference steps preserve score; strict improvements earn
`m + 1`; a step not known to worsen the alternative can cost `m`. Scores start
at zero. `BoundedThresholdChains` says that some positive scale makes all finite
chain scores bounded above. It contains no real-valued representation hypothesis.

This module proves necessity and constructs integer potentials from the criterion.
The sufficiency argument additionally separates positive-indifference classes.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*} {s i : X → X → Prop} {m : ℕ} {B : ℤ}

/-- A step permitted by the primitive comparisons, with its integer score update. -/
def ThresholdStep (s i : X → X → Prop) (m : ℕ) (p q : X × ℤ) : Prop :=
  (i p.1 q.1 ∧ q.2 = p.2) ∨
    (s q.1 p.1 ∧ q.2 = p.2 + (m : ℤ) + 1) ∨
    (¬s p.1 q.1 ∧ q.2 = p.2 - (m : ℤ))

/-- A score reached by a finite comparison chain starting at zero at any alternative. -/
def ThresholdReachable (s i : X → X → Prop) (m : ℕ) (x : X) (n : ℤ) : Prop :=
  ∃ y, Relation.ReflTransGen (ThresholdStep s i m) (y, 0) (x, n)

/-- An additional condition stated entirely in terms of finite comparison chains. -/
def BoundedThresholdChains (s i : X → X → Prop) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ B : ℤ, ∀ x n, ThresholdReachable s i m x n → n ≤ B

/-- Zero is always reachable by an empty chain. -/
theorem thresholdReachable_zero (s i : X → X → Prop) (m : ℕ) (x : X) :
    ThresholdReachable s i m x 0 := ⟨x, Relation.ReflTransGen.refl⟩

/-- A permitted final step extends a reachable score. -/
theorem thresholdReachable_extend {x y : X} {n k : ℤ}
    (h : ThresholdReachable s i m x n) (hstep : ThresholdStep s i m (x, n) (y, k)) :
    ThresholdReachable s i m y k := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, hz.tail hstep⟩

/-- The greatest reachable integer score at an alternative. -/
noncomputable def ThresholdPotential (s i : X → X → Prop) (m : ℕ) (x : X) : ℤ :=
  sSup {n | ThresholdReachable s i m x n}

/-- Bounded integer scores have a greatest attained value. -/
theorem thresholdPotential_reachable
    (hB : ∀ x n, ThresholdReachable s i m x n → n ≤ B) (x : X) :
    ThresholdReachable s i m x (ThresholdPotential s i m x) :=
  Int.csSup_mem ⟨0, thresholdReachable_zero s i m x⟩ ⟨B, hB x⟩

/-- Every reachable score is bounded by the potential. -/
theorem thresholdReachable_le_potential
    (hB : ∀ x n, ThresholdReachable s i m x n → n ≤ B) {x : X} {n : ℤ}
    (h : ThresholdReachable s i m x n) : n ≤ ThresholdPotential s i m x :=
  le_csSup ⟨B, hB x⟩ h

/-- Positive indifference gives equal potentials. -/
theorem thresholdPotential_indifferent (ha : PartialPreferenceAxioms s i)
    (hB : ∀ x n, ThresholdReachable s i m x n → n ≤ B) {x y : X} (hxy : i x y) :
    ThresholdPotential s i m x = ThresholdPotential s i m y := by
  apply le_antisymm
  · exact thresholdReachable_le_potential hB
      (thresholdReachable_extend (thresholdPotential_reachable hB x) (Or.inl ⟨hxy, rfl⟩))
  · exact thresholdReachable_le_potential hB
      (thresholdReachable_extend (thresholdPotential_reachable hB y)
        (Or.inl ⟨ha.indiff_symm x y hxy, rfl⟩))

/-- A strict improvement forces a potential increase of at least `m + 1`. -/
theorem thresholdPotential_strict
    (hB : ∀ x n, ThresholdReachable s i m x n → n ≤ B) {x y : X} (hxy : s x y) :
    ThresholdPotential s i m y + (m : ℤ) + 1 ≤ ThresholdPotential s i m x :=
  thresholdReachable_le_potential hB
    (thresholdReachable_extend (thresholdPotential_reachable hB y) (Or.inr (Or.inl ⟨hxy, rfl⟩)))

/-- Absence of a strict comparison bounds the corresponding potential difference by `m`. -/
theorem thresholdPotential_not_strict
    (hB : ∀ x n, ThresholdReachable s i m x n → n ≤ B) {x y : X} (hxy : ¬s x y) :
    ThresholdPotential s i m x - (m : ℤ) ≤ ThresholdPotential s i m y :=
  thresholdReachable_le_potential hB
    (thresholdReachable_extend (thresholdPotential_reachable hB x) (Or.inr (Or.inr ⟨hxy, rfl⟩)))

/-- Finitely many strict utility gaps admit a common positive integer scale. -/
theorem exists_threshold_scale [Finite X] {u : X → ℝ}
    (hu : ∀ x y, s x y ↔ ThresholdPreference u x y) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y, s x y → (m : ℝ) + 1 ≤ (m : ℝ) * (u x - u y) := by
  classical
  have hex (p : X × X) : ∃ n : ℕ,
      s p.1 p.2 → (n : ℝ) + 1 ≤ (n : ℝ) * (u p.1 - u p.2) := by
    by_cases hp : s p.1 p.2
    · have hgap : 0 < u p.1 - u p.2 - 1 := by
        have hh := (hu p.1 p.2).mp hp
        dsimp [ThresholdPreference] at hh
        linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (u p.1 - u p.2 - 1))
      have hmul := (div_lt_iff₀ hgap).mp hn
      exact ⟨n, fun _ => by nlinarith⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose n hn using hex
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  intro x y hxy
  have hsmall := hn (x, y) hxy
  have hbound : n (x, y) ≤ N + 1 := (hN ⟨(x, y), rfl⟩).trans (Nat.le_succ N)
  have hbound' : (n (x, y) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hbound
  have hgap : 0 ≤ u x - u y - 1 := by
    have hh := (hu x y).mp hxy
    dsimp [ThresholdPreference] at hh
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hbound') hgap
  nlinarith

/-- A represented comparison bounds the score change of each permitted step. -/
theorem thresholdStep_utility_bound {u : X → ℝ}
    (hs : ∀ x y, s x y ↔ ThresholdPreference u x y)
    (hi : ∀ x y, i x y ↔ EqualUtility u x y)
    (hm : ∀ x y, s x y → (m : ℝ) + 1 ≤ (m : ℝ) * (u x - u y))
    {p q : X × ℤ} (h : ThresholdStep s i m p q) :
    (q.2 : ℝ) ≤ (p.2 : ℝ) + (m : ℝ) * (u q.1 - u p.1) := by
  rcases h with ⟨h, heq⟩ | ⟨h, heq⟩ | ⟨h, heq⟩
  · have hue : u p.1 = u q.1 := (hi p.1 q.1).mp h
    rw [heq, hue]
    simp
  · have hcast : (q.2 : ℝ) = (p.2 : ℝ) + (m : ℝ) + 1 := by exact_mod_cast heq
    have hgap := hm q.1 p.1 h
    linarith
  · have hcast : (q.2 : ℝ) = (p.2 : ℝ) - (m : ℝ) := by exact_mod_cast heq
    have hweak : u p.1 ≤ u q.1 + 1 := le_of_not_gt (fun hh => h ((hs p.1 q.1).mpr hh))
    have hmul := mul_le_mul_of_nonneg_left hweak (Nat.cast_nonneg (α := ℝ) m)
    nlinarith

/-- Score bounds telescope along a finite chain. -/
theorem thresholdChain_utility_bound {u : X → ℝ}
    (hs : ∀ x y, s x y ↔ ThresholdPreference u x y)
    (hi : ∀ x y, i x y ↔ EqualUtility u x y)
    (hm : ∀ x y, s x y → (m : ℝ) + 1 ≤ (m : ℝ) * (u x - u y))
    {p q : X × ℤ} (h : Relation.ReflTransGen (ThresholdStep s i m) p q) :
    (q.2 : ℝ) ≤ (p.2 : ℝ) + (m : ℝ) * (u q.1 - u p.1) := by
  induction h with
  | refl => simp
  | @tail y z _ hstep ih =>
    have hh := thresholdStep_utility_bound hs hi hm hstep
    nlinarith

/-- Necessity of the bounded-chain criterion in **Problem 1.17f**. -/
theorem boundedThresholdChains_of_representation [Finite X] {u : X → ℝ}
    (hs : ∀ x y, s x y ↔ ThresholdPreference u x y)
    (hi : ∀ x y, i x y ↔ EqualUtility u x y) : BoundedThresholdChains s i := by
  obtain ⟨m, hm, hscale⟩ := exists_threshold_scale hs
  obtain ⟨lo, hlo⟩ := (Set.finite_range u).bddBelow
  obtain ⟨up, hup⟩ := (Set.finite_range u).bddAbove
  refine ⟨m, hm, ⌈(m : ℝ) * (up - lo)⌉, ?_⟩
  intro x n hn
  obtain ⟨y, hpath⟩ := hn
  have hscore := thresholdChain_utility_bound hs hi hscale hpath
  simp only [Int.cast_zero, zero_add] at hscore
  have hdiff : u x - u y ≤ up - lo := by
    have hx := hup ⟨x, rfl⟩
    have hy := hlo ⟨y, rfl⟩
    linarith
  have hbound := hscore.trans (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (α := ℝ) m))
  have hceil := hbound.trans (Int.le_ceil ((m : ℝ) * (up - lo)))
  exact_mod_cast hceil

end Kreps.ChoicePreferenceUtility
