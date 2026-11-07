/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureRepresentation
import ChoiceUnderUncertainty.SubsetLotteries
import ChoiceUnderUncertainty.NumericalExercises
import ChoiceUnderUncertainty.SubjectiveLotteries

/-!
# Representations on alternative prize spaces

Kreps I, Problems 5.1(d,e), 5.4 and 5.5, pp. 117–119. These interfaces connect
the numerical trees to the chapter's representations and specialize the mixture
theorem to roulette-first acts, whole subsets and marginal inclusion probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The score computed from each Figure 5.11 tree is Equation (5.6). -/
theorem figure511Value_eq_horseValue (U : Fin 3 → (ℝ × ℝ) → ℝ) (h : HorseLottery (Fin 3) (ℝ × ℝ)) :
    Figure511Value U h = HorseValue U h := rfl

/-- The probability-weighted score of part (e) is Equation (5.8) on the very same trees. -/
theorem figure511Value_eq_subjective (h : HorseLottery (Fin 3) (ℝ × ℝ)) :
    Figure511Value Figure511WeightedUtility h =
      SubjectiveHorseValue Figure510Prob.mass Figure510CommonUtility h := by
  rw [subjectiveHorseValue_eq_horseValue]
  rfl

/-- **Problem 5.4:** roulette first gives expected utility with entire acts as prizes. -/
theorem problem_5_4 {S X : Type*} {r : SimpleLottery (S → X) → SimpleLottery (S → X) → Prop} :
    MixtureAxioms r ↔ ∃ U : (S → X) → ℝ, Represents (ExpectedUtility U) r := proposition_5_3

/-- **Problem 5.5, whole subsets:** each subset can have its own prize utility. -/
theorem problem_5_5_whole {X : Type*}
    {r : SimpleLottery (Finset X) → SimpleLottery (Finset X) → Prop} :
    MixtureAxioms r ↔ ∃ U : Finset X → ℝ, Represents (ExpectedUtility U) r := proposition_5_3

/-- Every prescribed utility on subsets gives such a lottery ranking, also on degenerate subsets. -/
theorem subsetUtility_unrestricted {X : Type*} (U : Finset X → ℝ) :
    MixtureAxioms (UtilityPref (ExpectedUtility U)) ∧
      ∀ a b, UtilityPref (ExpectedUtility U) (PureLottery a) (PureLottery b) ↔ U b ≤ U a := by
  refine ⟨proposition_5_3.mpr ⟨U, fun _ _ => Iff.rfl⟩, ?_⟩
  intro a b
  simp [UtilityPref, expectedUtility_pure]

/-- **Problem 5.5, marginals:** the primitive axioms give an item-additive ranking on subsets. -/
theorem problem_5_5_marginals {X : Type*} [Finite X] [DecidableEq X]
    {r : HorseLottery X Bool → HorseLottery X Bool → Prop} (hr : MixtureAxioms r) :
    ∃ U : X → ℝ, ∀ a b : Finset X, r (SubsetVertex a) (SubsetVertex b) ↔
      ∑ x ∈ b, U x ≤ ∑ x ∈ a, U x := by
  obtain ⟨F, hFr, hFa⟩ := proposition_5_4.mp hr
  obtain ⟨U, hu⟩ := subsetMargin_additive hFa
  refine ⟨U, fun a b => ?_⟩
  rw [hFr, ← hu a, ← hu b, sub_le_sub_iff_right]

/-- A represented preference compares distinct utility levels strictly. -/
theorem strict_of_exerciseValue {Y : Type*} {r : Y → Y → Prop} {u : Y → ℝ}
    (hr : Represents u r) {x y : Y} (h : u y < u x) : Strict r x y :=
  ⟨(hr x y).mpr h.le, fun hy => h.not_ge ((hr y x).mp hy)⟩

/-- Part (a) ranks the actual monetary lotteries, including the exact indifference. -/
theorem problem_5_1a_preference {r : SimpleLottery ℝ → SimpleLottery ℝ → Prop}
    (hr : Represents (ExpectedUtility Real.sqrt) r) :
    Strict r (Problem51Money 2) (Problem51Money 0) ∧
    Indifferent r (Problem51Money 0) (Problem51Money 1) := by
  obtain ⟨h₀, h₁, h₂⟩ := problem_5_1a
  refine ⟨strict_of_exerciseValue hr ?_, (hr _ _).mpr ?_, (hr _ _).mpr ?_⟩
  · change Problem51MoneyValue 0 < Problem51MoneyValue 2
    linarith
  · change Problem51MoneyValue 1 ≤ Problem51MoneyValue 0
    linarith
  · change Problem51MoneyValue 0 ≤ Problem51MoneyValue 1
    linarith

/-- Part (b) ranks the deterministic acts under the state-dependent representation. -/
theorem problem_5_1b_preference {r : StateAct (Fin 3) (ℝ × ℝ) → StateAct (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (StateAdditiveValue Figure510Utility) r) :
    Strict r (Figure510Act 2) (Figure510Act 0) ∧ Strict r (Figure510Act 0) (Figure510Act 1) := by
  obtain ⟨a, b, c⟩ := problem_5_1b
  refine ⟨strict_of_exerciseValue hr ?_, strict_of_exerciseValue hr ?_⟩
  · change Figure510AdditiveValue 0 < Figure510AdditiveValue 2
    linarith
  · change Figure510AdditiveValue 1 < Figure510AdditiveValue 0
    linarith

/-- Part (c) yields the same strict order under the common subjective utility. -/
theorem problem_5_1c_preference {r : StateAct (Fin 3) (ℝ × ℝ) → StateAct (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (SubjectiveActValue Figure510Prob.mass Figure510CommonUtility) r) :
    Strict r (Figure510Act 2) (Figure510Act 0) ∧ Strict r (Figure510Act 0) (Figure510Act 1) :=
  ⟨strict_of_exerciseValue hr problem_5_1c.1, strict_of_exerciseValue hr problem_5_1c.2⟩

/-- Part (d) gives strict preference for the left horse-race lottery. -/
theorem problem_5_1d_preference
    {r : HorseLottery (Fin 3) (ℝ × ℝ) → HorseLottery (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (HorseValue Figure510Utility) r) : Strict r Figure511Left Figure511Right := by
  apply strict_of_exerciseValue hr
  change Figure511Value _ Figure511Right < Figure511Value _ Figure511Left
  rw [problem_5_1d.1, problem_5_1d.2]
  norm_num

/-- Part (e) reverses the choice between the same two horse-race lotteries. -/
theorem problem_5_1e_preference
    {r : HorseLottery (Fin 3) (ℝ × ℝ) → HorseLottery (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (SubjectiveHorseValue Figure510Prob.mass Figure510CommonUtility) r) :
    Strict r Figure511Right Figure511Left := by
  apply strict_of_exerciseValue hr
  simpa only [← figure511Value_eq_subjective] using problem_5_1e

end Kreps.ChoiceUnderUncertainty
