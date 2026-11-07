/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.AffineUniqueness
import ChoiceUnderUncertainty.LotteryEvaluation
import ChoiceUnderUncertainty.StateComparisons

/-!
# Horse lotteries and state-dependent expected utility

Kreps I, Proposition 5.12, pp. 102–105. Every state delivers a simple roulette
lottery on the common prize space. An affine utility on horse lotteries is the
sum of state-specific expected utilities after subtracting its reference value.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {S X Z : Type*}

/-- A horse lottery specifies a roulette lottery for every possible state. -/
abbrev HorseLottery (S X : Type*) := S → SimpleLottery X

/-- Mixtures of acts operate separately in every state. -/
theorem mix_act_apply [ConvexSpace ℝ Z] (a : Weight) (h g : S → Z) (s : S) :
    Mix a h g s = Mix a (h s) (g s) := by simp [Mix]

/-- Equation (5.6), the sum over states of their expected prize utilities. -/
noncomputable def HorseValue [Fintype S] (U : S → X → ℝ) (h : HorseLottery S X) : ℝ :=
  StateAdditiveValue (fun s => ExpectedUtility (U s)) h

/-- State-dependent expected utility is affine on lotteries over acts. -/
theorem horseValue_affine [Fintype S] (U : S → X → ℝ) : AffineInMix (HorseValue U) := by
  intro a h g
  simp only [HorseValue, StateAdditiveValue, mix_act_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => expectedUtility_affine (U s) a (h s) (g s)

/-- A single-state contribution of an affine utility is affine on roulette lotteries. -/
theorem stateIncrement_affine [DecidableEq S] [ConvexSpace ℝ Z] {u : (S → Z) → ℝ}
    (hu : AffineInMix u) (base : S → Z) (s : S) : AffineInMix (StateIncrement u base s) := by
  intro a x y
  have he : Function.update base s (Mix a x y) =
      Mix a (Function.update base s x) (Function.update base s y) := by
    funext t
    rw [mix_act_apply]
    by_cases h : t = s
    · subst t
      simp
    · simp [Function.update_of_ne h, mix_self]
  simp only [StateIncrement, he]
  rw [hu]
  ring

/-- An affine index, normalized to zero at a reference act, has the state-additive EU form. -/
theorem horseValue_of_affine [Fintype S] [DecidableEq S] {u : HorseLottery S X → ℝ}
    (hu : AffineInMix u) (base h : HorseLottery S X) :
    u h - u base = HorseValue (fun s x => StateIncrement u base s (PureLottery x)) h := by
  let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
  have hsym (x y : SimpleLottery X) : Mix a x y = Mix a y x := by
    have he : Complement a = a := by ext; norm_num [a, Complement]
    rw [mix_swap a x y, he]
  have hmid (f g : HorseLottery S X) :
      2 * u (fun s => Mix a (f s) (g s)) = u f + u g := by
    have he : (fun s => Mix a (f s) (g s)) = Mix a f g :=
      funext fun s => (mix_act_apply a f g s).symm
    rw [he, hu]
    dsimp [a]
    ring
  rw [stateAct_decomposition (Mix a) hsym u hmid base h]
  unfold HorseValue StateAdditiveValue
  exact Finset.sum_congr rfl fun s _ => affineInMix_eq_expectedUtility
    (stateIncrement_affine hu base s) (h s)

/-- The state utilities can be recovered from any affine representation, including empty domains. -/
theorem horseRepresentation_of_affine [Fintype S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {u : HorseLottery S X → ℝ}
    (hur : Represents u r) (hu : AffineInMix u) : ∃ U : S → X → ℝ, Represents (HorseValue U) r := by
  classical
  cases isEmpty_or_nonempty (HorseLottery S X) with
  | inl he => exact ⟨fun _ _ => 0, fun h _ => isEmptyElim h⟩
  | inr he =>
    obtain ⟨base⟩ := he
    refine ⟨fun s x => StateIncrement u base s (PureLottery x), fun h g => ?_⟩
    rw [hur, ← horseValue_of_affine hu base h, ← horseValue_of_affine hu base g]
    exact (sub_le_sub_iff_right _).symm

/-- The uniqueness part of Proposition 5.12 gives one scale and one intercept per state. -/
theorem proposition_5_12_unique [Fintype S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {U V : S → X → ℝ}
    (hU : Represents (HorseValue U) r) (hV : Represents (HorseValue V) r) :
    ∃ A > 0, ∃ B : ℝ, ∃ b : S → ℝ, (∀ h, HorseValue V h = A * HorseValue U h + B) ∧
      (∀ s x, V s x = A * U s x + b s) ∧ ∑ s, b s = B := by
  cases isEmpty_or_nonempty X with
  | inl he =>
    have huv : V = U := by ext s x; exact isEmptyElim x
    subst V
    exact ⟨1, zero_lt_one, 0, fun _ => 0, by simp, fun s x => isEmptyElim x, by simp⟩
  | inr he =>
    obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
      (horseValue_affine U) (horseValue_affine V)
    have hdet (h : StateAct S X) : StateAdditiveValue V h = A * StateAdditiveValue U h + B := by
      simpa only [HorseValue, StateAdditiveValue, expectedUtility_pure] using
        ha (fun s => PureLottery (h s))
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨b, hb, hs⟩ := stateUtility_shifts_of_affine U V A B hdet x
    exact ⟨A, hA, B, b, ha, hb, hs⟩

end Kreps.ChoiceUnderUncertainty
