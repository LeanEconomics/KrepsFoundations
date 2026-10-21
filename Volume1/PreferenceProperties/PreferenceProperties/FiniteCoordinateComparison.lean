/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.UtilityEquivalence
import Mathlib.Data.Finset.Piecewise

/-!
# Finite chains of coordinate substitutions

The substitution argument in Kreps I, Proposition 2.12, p. 41. Weak improvements
in finitely many coordinates give a weak improvement overall; one strict step
makes the full chain strict. Equal coordinate scores leave the value unchanged.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Finite I] [DecidableEq I] {B : I → Type*}

/-- Coordinatewise weak score improvements can be substituted one at a time. -/
theorem finite_coordinate_mono {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, w i a ≤ w i b →
      F (Function.update z i a) ≤ F (Function.update z i b))
    (x y : ∀ i, B i) (hxy : ∀ i, w i (x i) ≤ w i (y i)) : F x ≤ F y := by
  let : Fintype I := Fintype.ofFinite I
  have hchain (s : Finset I) : F x ≤ F (s.piecewise y x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.piecewise_insert]
      apply ih.trans
      have hz : s.piecewise y x i = x i := s.piecewise_eq_of_notMem y x hi
      have hstep := hc i (s.piecewise y x) (s.piecewise y x i) (y i)
        (by rw [hz]; exact hxy i)
      simpa only [Function.update_eq_self] using hstep
  simpa only [Finset.piecewise_univ] using hchain Finset.univ

/-- Equal scores allow substitution in both directions. -/
theorem finite_coordinate_eq {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, w i a ≤ w i b →
      F (Function.update z i a) ≤ F (Function.update z i b))
    (x y : ∀ i, B i) (hxy : ∀ i, w i (x i) = w i (y i)) : F x = F y :=
  le_antisymm (finite_coordinate_mono hc x y (fun i => (hxy i).le))
    (finite_coordinate_mono hc y x (fun i => (hxy i).ge))

/-- One strict score improvement makes a finite weak-improvement chain strict. -/
theorem finite_coordinate_strict {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, F (Function.update z i a) ≤ F (Function.update z i b) ↔
      w i a ≤ w i b) (x y : ∀ i, B i)
    (hxy : ∀ i, w i (x i) ≤ w i (y i)) (hs : ∃ i, w i (x i) < w i (y i)) :
    F x < F y := by
  obtain ⟨i, hi⟩ := hs
  have hstep : F x < F (Function.update x i (y i)) := by
    have hn : ¬F (Function.update x i (y i)) ≤ F (Function.update x i (x i)) :=
      fun h => (not_le_of_gt hi) ((hc i x (y i) (x i)).mp h)
    simpa only [Function.update_eq_self] using lt_of_not_ge hn
  apply hstep.trans_le
  apply finite_coordinate_mono (fun i z a b h => (hc i z a b).mpr h)
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using hxy j

end Kreps.PreferenceProperties
