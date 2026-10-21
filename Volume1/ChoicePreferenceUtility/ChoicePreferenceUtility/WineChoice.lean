/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Basic

/-!
# The restaurant wine-choice counterexample

Kreps I, Problem 1.1, pp. 23-24. Three affordable white wines suffice: California
at 20, France at 30, and France at 10. With all three wines, the largest origin
category is France and price selects the bottle at 30. Removing the French bottle
at 10 makes the origin counts tie, so California wins and the bottle at 20 is chosen.
The definitions implement all five origin categories, all three colors and both
tie-breaking rules, even though only two origins and one color occur in this example.
-/

open scoped BigOperators

namespace Kreps.ChoicePreferenceUtility

/-- The three distinct prices in the finite counterexample universe. -/
def WinePrice (x : Fin 3) : ℕ := if x = 0 then 20 else if x = 1 then 30 else 10

/-- Origin priority: California, France, Italy, Spain, other. -/
def WineOrigin (x : Fin 3) : Fin 5 := if x = 0 then 0 else 1

/-- Color priority: white, red, rose. All three counterexample wines are white. -/
def WineColor (_ : Fin 3) : Fin 3 := 0

/-- Count entries in an origin category among the offered wines. -/
noncomputable def WineOriginCount (A : Set (Fin 3)) (o : Fin 5) : ℕ := by
  classical
  exact ∑ x : Fin 3, if x ∈ A ∧ WineOrigin x = o then 1 else 0

/-- Count entries of a color within an origin category. -/
noncomputable def WineColorCount (A : Set (Fin 3)) (o : Fin 5) (t : Fin 3) : ℕ := by
  classical
  exact ∑ x : Fin 3, if x ∈ A ∧ WineOrigin x = o ∧ WineColor x = t then 1 else 0

/-- The stated sequential rule, specialized to this finite universe of affordable wines. -/
def WineChoice (A : Set (Fin 3)) : Set (Fin 3) := {x | x ∈ A ∧
  (∀ o, WineOriginCount A o ≤ WineOriginCount A (WineOrigin x) ∧
    (WineOriginCount A o = WineOriginCount A (WineOrigin x) → WineOrigin x ≤ o)) ∧
  (∀ t, WineColorCount A (WineOrigin x) t ≤ WineColorCount A (WineOrigin x) (WineColor x) ∧
    (WineColorCount A (WineOrigin x) t = WineColorCount A (WineOrigin x) (WineColor x) →
      WineColor x ≤ t)) ∧
  ∀ y ∈ A, WineOrigin y = WineOrigin x → WineColor y = WineColor x → WinePrice y ≤ WinePrice x}

/-- All wines satisfy the price cap, and distinct wines have distinct descriptors. -/
theorem wine_universe_valid :
    (∀ x, WinePrice x ≤ 40) ∧
      Function.Injective (fun x => (WinePrice x, WineOrigin x, WineColor x)) := by
  constructor
  · intro x
    fin_cases x <;> norm_num [WinePrice]
  · intro x y h
    have hp := congrArg (fun a => a.1) h
    fin_cases x <;> fin_cases y <;> simp_all [WinePrice]

/-- The larger menu chooses the French bottle at 30. -/
theorem wineChoice_full : WineChoice Set.univ = {1} := by
  ext x
  fin_cases x <;>
    simp only [WineChoice, WineOriginCount, WineColorCount, Fin.sum_univ_succ] <;>
    norm_num [WinePrice, WineOrigin, WineColor, Fin.forall_fin_succ]

/-- The smaller menu chooses the Californian bottle at 20. -/
theorem wineChoice_pair : WineChoice {0, 1} = {0} := by
  ext x
  fin_cases x <;>
    simp only [WineChoice, WineOriginCount, WineColorCount, Fin.sum_univ_succ] <;>
    norm_num [WinePrice, WineOrigin, WineColor, Fin.forall_fin_succ]

/-- **Problem 1.1**: the stated wine-choice rule violates coherence. -/
theorem problem_1_1 : ¬Coherent WineChoice := by
  intro hc
  apply hc Set.univ {0, 1} 1 (by simp) 0 (by simp)
  · rw [wineChoice_full]
    simp
  · rw [wineChoice_full]
    simp
  · rw [wineChoice_pair]
    simp

/-- The wine rule is feasible on every menu. -/
theorem wineChoice_feasible : Feasible WineChoice := fun _ _ h => h.1

/-- The rule really makes a nonempty choice from every nonempty menu in the example universe. -/
theorem wineChoice_nonempty (A : Set (Fin 3)) (hA : A.Nonempty) : (WineChoice A).Nonempty := by
  classical
  have ha : 0 ∈ A ∨ 1 ∈ A ∨ 2 ∈ A := by
    simpa only [Set.Nonempty, Fin.exists_fin_succ, Fin.val_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Fin.exists_fin_zero, or_false] using hA
  change ∃ x : Fin 3, x ∈ WineChoice A
  simp only [WineChoice, WineOriginCount, WineColorCount, Fin.sum_univ_succ]
  by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A <;> by_cases h2 : 2 ∈ A <;>
    norm_num [WinePrice, WineOrigin, WineColor, Fin.forall_fin_succ, Fin.exists_fin_succ,
      h0, h1, h2] at *

end Kreps.ChoicePreferenceUtility
