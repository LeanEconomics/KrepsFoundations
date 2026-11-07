/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.HorseLotteries

/-!
# Subjective probabilities and state-independent prize utility

Kreps I, Proposition 5.13, pp. 106–108. The comparison of constant acts with
single-state changes forces all state utilities onto a common positive affine scale.
Normalizing these scales gives a strictly positive probability distribution on a
nonempty finite state space. Nonconstant utility identifies its probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- Probability mass one makes expectation commute with affine changes of prize units. -/
theorem expectedUtility_affine_transform (U : X → ℝ) (A B : ℝ) (q : SimpleLottery X) :
    ExpectedUtility (fun x => A * U x + B) q = A * ExpectedUtility U q + B := by
  classical
  have ht : ∑ x ∈ q.weights.support, q.weights x = 1 := q.total
  unfold ExpectedUtility Finsupp.sum
  calc
    _ = ∑ x ∈ q.weights.support, (A * (q.weights x * U x) + q.weights x * B) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ht, one_mul]

/-- Equation (5.8), subjective expectation over states of objective roulette expectations. -/
noncomputable def SubjectiveHorseValue (p : S → ℝ) (U : X → ℝ) (h : HorseLottery S X) : ℝ :=
  SubjectiveActValue p (ExpectedUtility U) h

/-- The subjective index is the state-dependent index with prize utility scaled by probability. -/
theorem subjectiveHorseValue_eq_horseValue (p : S → ℝ) (U : X → ℝ) :
    SubjectiveHorseValue p U = HorseValue (fun s x => p s * U x) := by
  funext h
  apply Finset.sum_congr rfl
  intro s _
  simpa only [add_zero] using (expectedUtility_affine_transform U (p s) 0 (h s)).symm

/-- Subjective expected utility is affine under objective mixtures of acts. -/
theorem subjectiveHorseValue_affine (p : S → ℝ) (U : X → ℝ) :
    AffineInMix (SubjectiveHorseValue p U) := by
  rw [subjectiveHorseValue_eq_horseValue]
  exact horseValue_affine _

/-- Under condition (f), each state's expected utility represents the ranking of constant acts. -/
theorem constantActs_represented_in_each_state {r : HorseLottery S X → HorseLottery S X → Prop}
    {U : S → X → ℝ} (hr : Represents (HorseValue U) r) (hi : StateIndependentComparisons r)
    (s : S) : Represents (ExpectedUtility (U s)) (fun x y => r (fun _ => x) (fun _ => y)) := by
  classical
  intro x y
  let g : HorseLottery S X := fun _ => y
  let h : HorseLottery S X := Function.update g s x
  have he : ∀ t, t ≠ s → h t = g t := fun _ ht => Function.update_of_ne ht x g
  have hc := (hi s h g he).trans (stateAdditive_local_comparison
    (fun t => ExpectedUtility (U t)) hr s h g he)
  simpa only [h, g, Function.update_self] using hc

/-- The source's normalization of state-specific utility scales into subjective probabilities. -/
theorem subjectiveRepresentation_of_stateIndependent [Nonempty S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {V : S → X → ℝ}
    (hr : Represents (HorseValue V) r) (hi : StateIndependentComparisons r) :
    ∃ (p : S → ℝ) (U : X → ℝ), (∀ s, 0 < p s) ∧ ∑ s, p s = 1 ∧
      Represents (SubjectiveHorseValue p U) r := by
  classical
  let t : S := Classical.arbitrary S
  have hrat (s : S) := constantActs_represented_in_each_state hr hi s
  choose a ha b hab using fun s => proposition_5_4_unique (hrat t) (hrat s)
    (expectedUtility_affine (V t)) (expectedUtility_affine (V s))
  let N := ∑ s, a s
  have hN : 0 < N := Finset.sum_pos (fun s _ => ha s) Finset.univ_nonempty
  let p : S → ℝ := fun s => a s / N
  let U : X → ℝ := fun x => N * V t x
  have hv (h : HorseLottery S X) :
      HorseValue V h = SubjectiveHorseValue p U h + ∑ s, b s := by
    unfold HorseValue StateAdditiveValue SubjectiveHorseValue SubjectiveActValue
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    have he : ExpectedUtility U (h s) = N * ExpectedUtility (V t) (h s) := by
      simpa only [add_zero, U] using expectedUtility_affine_transform (V t) N 0 (h s)
    change ExpectedUtility (V s) (h s) = p s * ExpectedUtility U (h s) + b s
    rw [hab s, he]
    dsimp only [p]
    field_simp [hN.ne']
  refine ⟨p, U, fun s => div_pos (ha s) hN, ?_, fun h g => ?_⟩
  · change ∑ s, a s / N = 1
    rw [← Finset.sum_div, div_self hN.ne']
  · rw [hr, hv, hv]
    exact add_le_add_iff_right _

/-- Two subjective representations have positive affine-equivalent prize indices. -/
theorem subjective_prize_utility_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) {r : HorseLottery S X → HorseLottery S X → Prop}
    (hU : Represents (SubjectiveHorseValue p U) r) (hV : Represents (SubjectiveHorseValue q V) r) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, V x = A * U x + B := by
  obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
    (subjectiveHorseValue_affine p U) (subjectiveHorseValue_affine q V)
  refine ⟨A, hA, B, fun x => ?_⟩
  simpa only [SubjectiveHorseValue, subjectiveActValue_constant _ hp,
    subjectiveActValue_constant _ hq, expectedUtility_pure] using ha (fun _ => PureLottery x)

/-- Nonconstant prize utility identifies the probabilities, even when some outcomes are tied. -/
theorem subjective_probabilities_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) {r : HorseLottery S X → HorseLottery S X → Prop}
    (hU : Represents (SubjectiveHorseValue p U) r) (hV : Represents (SubjectiveHorseValue q V) r)
    {x y : X} (hne : U x ≠ U y) : q = p := by
  obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
    (subjectiveHorseValue_affine p U) (subjectiveHorseValue_affine q V)
  apply subjectiveProbabilities_unique p q hp hq (ExpectedUtility U) (ExpectedUtility V) A B hA ha
    (x := PureLottery x) (y := PureLottery y)
  simpa only [expectedUtility_pure] using hne

end Kreps.ChoiceUnderUncertainty
