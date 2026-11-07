/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Tactic

/-!
# Acts, state separability and the Sure-Thing Principle

Kreps I, pp. 79–83 and 103–105. Acts assign consequences to states. Additive state
utility implies Savage's Sure-Thing Principle. For the converse construction used in
Proposition 5.12, a utility preserving pointwise midpoints separates into the sum of
its single-state changes from a reference act.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*}

/-- An act specifies the prize in each state of nature. -/
abbrev StateAct (S X : Type*) := S → X

/-- Equation (5.1), the sum of utilities evaluated in their respective states. -/
noncomputable def StateAdditiveValue [Fintype S] (U : S → X → ℝ) (h : StateAct S X) : ℝ :=
  ∑ s, U s (h s)

/-- Equation (5.2), the probability-weighted value of a state-independent utility. -/
noncomputable def SubjectiveActValue [Fintype S] (p : S → ℝ) (U : X → ℝ)
    (h : StateAct S X) : ℝ := ∑ s, p s * U (h s)

/-- Subjective expected utility is additive with state-specific utilities scaled by probability. -/
theorem subjectiveActValue_eq_stateAdditiveValue [Fintype S] (p : S → ℝ) (U : X → ℝ)
    (h : StateAct S X) :
    SubjectiveActValue p U h = StateAdditiveValue (fun s x => p s * U x) h := rfl

/-- Axiom 5.1. Changing the common consequences off an event preserves the ranking. -/
def SureThing (r : StateAct S X → StateAct S X → Prop) : Prop :=
  ∀ (T : Set S) (a a' b b' : StateAct S X),
    (∀ s ∈ T, a s = a' s ∧ b s = b' s) →
    (∀ s ∉ T, a s = b s ∧ a' s = b' s) → (r a b ↔ r a' b')

/-- An additive representation satisfies the Sure-Thing Principle for every event. -/
theorem sureThing_of_stateAdditive [Fintype S] (U : S → X → ℝ)
    {r : StateAct S X → StateAct S X → Prop}
    (hU : ∀ a b, r a b ↔ StateAdditiveValue U b ≤ StateAdditiveValue U a) : SureThing r := by
  intro T a a' b b' hin hout
  have hd : StateAdditiveValue U a - StateAdditiveValue U b =
      StateAdditiveValue U a' - StateAdditiveValue U b' := by
    simp only [StateAdditiveValue, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ T
    · rw [(hin s hs).1, (hin s hs).2]
    · rw [(hout s hs).1, (hout s hs).2, sub_self, sub_self]
  rw [hU, hU]
  constructor <;> intro h <;> linarith

/-- The utility contribution of replacing the reference consequence in one state. -/
noncomputable def StateIncrement [DecidableEq S] (u : StateAct S X → ℝ) (base : StateAct S X)
    (s : S) (x : X) : ℝ := u (Function.update base s x) - u base

/-- Midpoint affinity makes a single-state increment independent of the other coordinates. -/
theorem stateIncrement_independent [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) (s : S) (hs : h s = base s) (x : X) :
    u (Function.update h s x) - u h = StateIncrement u base s x := by
  have he : (fun t => m (Function.update h s x t) (base t)) =
      fun t => m (h t) (Function.update base s x t) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp [hs, hsym x (base s)]
    · simp [Function.update_of_ne ht]
  have h₁ := hu (Function.update h s x) base
  have h₂ := hu h (Function.update base s x)
  rw [he] at h₁
  unfold StateIncrement
  linarith

/-- The act that agrees with the chosen act on a finite event and the reference elsewhere. -/
noncomputable def PartialAct [DecidableEq S] (base h : StateAct S X) (T : Finset S) :
    StateAct S X := fun s => if s ∈ T then h s else base s

/-- Adding one state at a time sums its reference increments over any finite event. -/
theorem partialAct_value [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) (T : Finset S) :
    u (PartialAct base h T) - u base = ∑ s ∈ T, StateIncrement u base s (h s) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : PartialAct base h ∅ = base := by ext s; simp [PartialAct]
    rw [he]
    simp
  | @insert s T hst ih =>
    have he : PartialAct base h (insert s T) = Function.update (PartialAct base h T) s (h s) := by
      funext t
      by_cases ht : t = s
      · subst t
        simp [PartialAct]
      · simp [PartialAct, ht]
    have hi := stateIncrement_independent m hsym u hu base (PartialAct base h T) s
      (by simp [PartialAct, hst]) (h s)
    rw [he, Finset.sum_insert hst]
    linarith

/-- The normalized utility of a complete act is the sum of its single-state contributions. -/
theorem stateAct_decomposition [Fintype S] [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) :
    u h - u base = StateAdditiveValue (StateIncrement u base) h := by
  have he : PartialAct base h Finset.univ = h := by ext s; simp [PartialAct]
  simpa only [he, StateAdditiveValue] using partialAct_value m hsym u hu base h Finset.univ

end Kreps.ChoiceUnderUncertainty
