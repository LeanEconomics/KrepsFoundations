/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Rationalization

/-!
# Observed choice and revealed preference

Kreps I, Problem 1.16c and Definition 1.22, p. 28.
The printed strict relation omits membership of the rejected alternative in the menu.
`printed_strict_counterexample` shows why that membership condition is necessary:
utility-maximizing choice can otherwise exhibit the forbidden two-alternative cycle.
The general rationalizability equivalence is proved in `proposition_1_23`
in the module `ChoicePreferenceUtility.SGARP`.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X I : Type*}

/-- Weak preference directly revealed by one observed menu and its chosen set. -/
def ObservedWeak (menus chosen : I → Set X) (x y : X) : Prop :=
  ∃ i, x ∈ chosen i ∧ y ∈ menus i

/-- Strict revealed preference, with the rejected alternative required to be feasible. -/
def ObservedStrict (menus chosen : I → Set X) (x y : X) : Prop :=
  ∃ i, x ∈ chosen i ∧ y ∈ menus i ∧ y ∉ chosen i

/-- The definition as printed on p. 28, without the required menu-membership condition. -/
def PrintedObservedStrict (chosen : I → Set X) (x y : X) : Prop :=
  ∃ i, x ∈ chosen i ∧ y ∉ chosen i

/-- With the domain condition restored, strict observed preference implies weak preference. -/
theorem observedStrict_implies_weak {menus chosen : I → Set X} {x y : X}
    (h : ObservedStrict menus chosen x y) : ObservedWeak menus chosen x y := by
  obtain ⟨i, hx, hy, _⟩ := h
  exact ⟨i, hx, hy⟩

/-- Two observed menus: the full pair and the singleton containing `false`. -/
def CounterexampleMenus (i : Bool) : Set Bool := if i then Set.univ else {false}

/-- Each observation chooses its index: `true` from the pair, `false` from its singleton. -/
def CounterexampleChoices (i : Bool) : Set Bool := {i}

/-- A strict ranking of the two alternatives. -/
def CounterexampleUtility (b : Bool) : ℝ := if b then 1 else 0

/-- Both observations are exactly utility maximizing, including their rejected alternatives. -/
theorem counterexampleChoices_rationalized (i : Bool) :
    CounterexampleChoices i = UtilityChoice CounterexampleUtility (CounterexampleMenus i) := by
  ext b
  cases i <;> cases b <;>
    simp [CounterexampleChoices, CounterexampleMenus, CounterexampleUtility,
      UtilityChoice, PrefChoice, UtilityPref]

/-- The printed strict definition falsely rejects a rationalizable data set. -/
theorem printed_strict_counterexample :
    Rational (UtilityPref CounterexampleUtility) ∧
      (∀ i, CounterexampleChoices i =
        PrefChoice (UtilityPref CounterexampleUtility) (CounterexampleMenus i)) ∧
      ObservedWeak CounterexampleMenus CounterexampleChoices true false ∧
      PrintedObservedStrict CounterexampleChoices false true ∧
      ¬ObservedStrict CounterexampleMenus CounterexampleChoices false true := by
  refine ⟨proposition_1_3a CounterexampleUtility, counterexampleChoices_rationalized,
    ⟨true, by simp [CounterexampleChoices], by simp [CounterexampleMenus]⟩,
    ⟨false, by simp [CounterexampleChoices], by simp [CounterexampleChoices]⟩, ?_⟩
  rintro ⟨i, hx, hy, _⟩
  cases i <;> simp [CounterexampleChoices, CounterexampleMenus] at hx hy

end Kreps.ChoicePreferenceUtility
