/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.ActSeparability

/-!
# Local comparisons and uniqueness of additive state utilities

Kreps I, pp. 104–108. Comparing acts that differ only in state `s` isolates that
state's utility difference. This identifies the state-specific additive constants
and gives the local comparison used to recover subjective probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- When acts agree off one state, their total utility difference is local to that state. -/
theorem stateAdditiveValue_difference (U : S → X → ℝ) (s : S) (h g : StateAct S X)
    (he : ∀ t, t ≠ s → h t = g t) :
    StateAdditiveValue U h - StateAdditiveValue U g = U s (h s) - U s (g s) := by
  classical
  simp only [StateAdditiveValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single s
  · intro t _ ht
    rw [he t ht, sub_self]
  · simp

/-- Representing rankings on acts by a sum identifies every one-state comparison. -/
theorem stateAdditive_local_comparison (U : S → X → ℝ) {r : StateAct S X → StateAct S X → Prop}
    (hU : ∀ h g, r h g ↔ StateAdditiveValue U g ≤ StateAdditiveValue U h)
    (s : S) (h g : StateAct S X) (he : ∀ t, t ≠ s → h t = g t) :
    r h g ↔ U s (g s) ≤ U s (h s) := by
  rw [hU]
  have hd := stateAdditiveValue_difference U s h g he
  constructor <;> intro hr <;> linarith

/-- A common affine scale for total utilities fixes the differences in every state. -/
theorem stateUtility_difference_of_affine (U V : S → X → ℝ) (A B : ℝ)
    (ha : ∀ h, StateAdditiveValue V h = A * StateAdditiveValue U h + B)
    (s : S) (x y : X) : V s x - V s y = A * (U s x - U s y) := by
  classical
  let g : StateAct S X := fun _ => y
  let h := Function.update g s x
  have he : ∀ t, t ≠ s → h t = g t := fun t ht => Function.update_of_ne ht x g
  have hu := stateAdditiveValue_difference U s h g he
  have hv := stateAdditiveValue_difference V s h g he
  rw [ha h, ha g] at hv
  simp only [h, g, Function.update_self] at hu hv
  rw [← hu]
  linarith

/-- Proposition 5.12's uniqueness formula, including the sum of the state shifts. -/
theorem stateUtility_shifts_of_affine (U V : S → X → ℝ) (A B : ℝ)
    (ha : ∀ h, StateAdditiveValue V h = A * StateAdditiveValue U h + B) (base : X) :
    ∃ b : S → ℝ, (∀ s x, V s x = A * U s x + b s) ∧ ∑ s, b s = B := by
  refine ⟨fun s => V s base - A * U s base, ?_, ?_⟩
  · intro s x
    have hd := stateUtility_difference_of_affine U V A B ha s x base
    linarith
  · have hc := ha (fun _ => base)
    simp only [StateAdditiveValue] at hc
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith

/-- Condition (f) of Proposition 5.13 compares each one-state change to constant acts. -/
def StateIndependentComparisons (r : StateAct S X → StateAct S X → Prop) : Prop :=
  ∀ (s : S) (h g : StateAct S X), (∀ t, t ≠ s → h t = g t) →
    (r (fun _ => h s) (fun _ => g s) ↔ r h g)

/-- A strictly positive probability vector makes local and constant comparisons agree. -/
theorem subjectiveActValue_stateIndependent (p : S → ℝ) (hp : ∀ s, 0 < p s)
    (hp₁ : ∑ s, p s = 1) (U : X → ℝ)
    {r : StateAct S X → StateAct S X → Prop}
    (hr : ∀ h g, r h g ↔ SubjectiveActValue p U g ≤ SubjectiveActValue p U h) :
    StateIndependentComparisons r := by
  intro s h g he
  have hs := stateAdditive_local_comparison (fun t x => p t * U x) hr s h g he
  rw [hr, hs]
  simp only [SubjectiveActValue, ← Finset.sum_mul, hp₁, one_mul]
  exact (mul_le_mul_iff_right₀ (hp s)).symm

/-- Constant acts recover the unweighted outcome utility for any normalized prior. -/
theorem subjectiveActValue_constant (p : S → ℝ) (hp : ∑ s, p s = 1) (U : X → ℝ) (x : X) :
    SubjectiveActValue p U (fun _ => x) = U x := by
  simp only [SubjectiveActValue, ← Finset.sum_mul, hp, one_mul]

/-- Nonconstant prizes identify the state probabilities from affine-equivalent total values. -/
theorem subjectiveProbabilities_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) (A B : ℝ) (hA : 0 < A)
    (ha : ∀ h, SubjectiveActValue q V h = A * SubjectiveActValue p U h + B)
    {x y : X} (hne : U x ≠ U y) : q = p := by
  have hconst (z : X) : V z = A * U z + B := by
    simpa only [subjectiveActValue_constant q hq, subjectiveActValue_constant p hp] using
      ha (fun _ => z)
  funext s
  have hd := stateUtility_difference_of_affine (fun t z => p t * U z)
    (fun t z => q t * V z) A B ha s x y
  rw [hconst x, hconst y] at hd
  have hn : A * (U x - U y) ≠ 0 := mul_ne_zero hA.ne' (sub_ne_zero.mpr hne)
  apply (mul_left_inj' hn).mp
  linarith only [hd]

end Kreps.ChoiceUnderUncertainty
