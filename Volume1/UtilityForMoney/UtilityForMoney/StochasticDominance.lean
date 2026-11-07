/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.RiskyAssets

/-!
# Stochastic dominance for finite-support monetary distributions

Kreps I, Definition 6.13, pp. 132–134. Both orders test all the specified utility
functions on the real line. The lower-tail shortfall at a threshold will equal
the integral of the cumulative distribution function below that threshold.
-/

namespace Kreps.UtilityForMoney

/-- **Definition 6.13:** every nondecreasing prize utility weakly prefers the first lottery. -/
def FirstOrderDominates (p q : SimpleLottery ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ExpectedUtility U q ≤ ExpectedUtility U p

/-- **Definition 6.13:** every nondecreasing concave utility weakly prefers the first lottery. -/
def SecondOrderDominates (p q : SimpleLottery ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ Set.univ U → ExpectedUtility U q ≤ ExpectedUtility U p

/-- The cumulative probability at or below the threshold, including a possible atom there. -/
noncomputable def Cumulative (p : SimpleLottery ℝ) (r : ℝ) : ℝ :=
  ExpectedUtility (fun x => if x ≤ r then 1 else 0) p

/-- Expected shortfall below a fixed threshold. -/
noncomputable def ExpectedShortfall (p : SimpleLottery ℝ) (r : ℝ) : ℝ :=
  ExpectedUtility (fun x => max (r - x) 0) p

/-- First-order dominance entails second-order dominance. -/
theorem FirstOrderDominates.secondOrder {p q : SimpleLottery ℝ} (h : FirstOrderDominates p q) :
    SecondOrderDominates p q := fun U hi _ => h U hi

/-- **Problem 6.5(a):** first-order dominance orders the cumulative probabilities. -/
theorem cumulative_le_of_firstOrder {p q : SimpleLottery ℝ} (h : FirstOrderDominates p q)
    (r : ℝ) : Cumulative p r ≤ Cumulative q r := by
  let f : ℝ → ℝ := fun x => if x ≤ r then 1 else 0
  have hf : Monotone (fun x => (-1 : ℝ) * f x + 1) := by
    intro x y hxy
    dsimp [f]
    split_ifs <;> linarith
  have he := h _ hf
  rw [expectedUtility_affine_payoff, expectedUtility_affine_payoff] at he
  change ExpectedUtility f p ≤ ExpectedUtility f q
  linarith

/-- The capped utility used to probe second-order dominance is increasing and concave. -/
theorem cappedPrizeUtility_properties (r : ℝ) :
    Monotone (fun x : ℝ => min x r) ∧ ConcaveOn ℝ Set.univ (fun x : ℝ => min x r) := by
  refine ⟨fun _ _ h => min_le_min_right r h, convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left x r) ha)
      (mul_le_mul_of_nonneg_left (min_le_left y r) hb)
  · have h₁ := mul_le_mul_of_nonneg_left (min_le_right x r) ha
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right y r) hb
    nlinarith [congrArg (fun t : ℝ => t * r) hab]

/-- **Problem 6.6(a), shortfall form:** risk-averse dominance reduces each expected shortfall. -/
theorem expectedShortfall_le_of_secondOrder {p q : SimpleLottery ℝ}
    (h : SecondOrderDominates p q) (r : ℝ) : ExpectedShortfall p r ≤ ExpectedShortfall q r := by
  have he := h _ (cappedPrizeUtility_properties r).1 (cappedPrizeUtility_properties r).2
  have heq : (fun x : ℝ => min x r) = fun x => (-1 : ℝ) * max (r - x) 0 + r := by
    funext x
    rcases le_total x r with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
      ring
  rw [heq, expectedUtility_affine_payoff, expectedUtility_affine_payoff] at he
  unfold ExpectedShortfall
  linarith

end Kreps.UtilityForMoney
