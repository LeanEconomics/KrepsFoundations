/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EventDecomposition

/-!
# Conditional utility and finitely additive subjective odds

Kreps I, Problem 5.6(d,e), pp. 121–122. Conditional utility values every
roulette on an event relative to a constant reference. Its value at a globally
normalized better prize is finitely additive. Nonnegativity follows from its
*conditional* weak preference on every event.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- Value increment when roulette `q` replaces the reference roulette throughout one event. -/
noncomputable def EventLotteryIndex (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (q : SimpleLottery X) : ℝ :=
  EventContribution hA F base E hE (EventConstant hA q)

/-- Replacing a lottery by itself anywhere leaves the reference value unchanged. -/
theorem eventLotteryIndex_base (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) {E : Set S} (hE : E ∈ A) :
    EventLotteryIndex hA F base E hE base = 0 := by
  classical
  have he : EventCut hA base E hE (EventConstant hA base) = EventConstant hA base := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply, EventConstant]
  simp [EventLotteryIndex, EventContribution, he]

/-- Conditional utility is itself affine on roulette lotteries. -/
theorem eventLotteryIndex_affine (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) {E : Set S} (hE : E ∈ A) :
    AffineInMix (EventLotteryIndex hA F base E hE) := by
  classical
  intro a p q
  have he : EventCut hA base E hE (EventConstant hA (Mix a p q)) =
      EventMix hA a (EventCut hA base E hE (EventConstant hA p))
        (EventCut hA base E hE (EventConstant hA q)) := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E <;> simp [eventMix_apply, eventCut_apply, EventConstant, hs, mix_self]
  simp only [EventLotteryIndex, EventContribution, he]
  rw [ha a _ _]
  ring

/-- Event-specific prize utility is obtained by inserting a sure prize on that event. -/
noncomputable def EventPrizeUtility (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (x : X) : ℝ :=
  EventLotteryIndex hA F base E hE (PureLottery x)

/-- Every conditional roulette is evaluated by its event-specific expected prize utility. -/
theorem eventLotteryIndex_expectedUtility (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) {E : Set S} (hE : E ∈ A)
    (q : SimpleLottery X) :
    EventLotteryIndex hA F base E hE q = ExpectedUtility (EventPrizeUtility hA F base E hE) q :=
  affineInMix_eq_expectedUtility (eventLotteryIndex_affine hA ha base hE) q

/-- **Problem 5.6(d):** sum the event-specific expectations over any finite presentation. -/
theorem problem_5_6d {I : Type*} [Fintype I] (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (q : I → SimpleLottery X) (h : EventAct A X)
    (hh : ∀ s, h.val s = q (c s)) :
    F h - F (EventConstant hA base) =
      ∑ i, ExpectedUtility (EventPrizeUtility hA F base {s | c s = i} (hc i)) (q i) := by
  rw [problem_5_6b hA ha base c hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eventLotteryIndex_expectedUtility hA ha]
  apply eventContribution_congr_act
  intro s hs
  change h.val s = q i
  rw [hh s, show c s = i from hs]

/-- The eventwise ranking takes identical reference consequences outside the event. -/
def EventRanking (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (q t : SimpleLottery X) : Prop :=
  r (EventCut hA base E hE (EventConstant hA q)) (EventCut hA base E hE (EventConstant hA t))

/-- Subtracting the common reference value preserves every conditional comparison. -/
theorem eventLotteryIndex_represents (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (base : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) :
    Represents (EventLotteryIndex hA F base E hE) (EventRanking hA r base E hE) := by
  intro q t
  unfold EventRanking EventLotteryIndex EventContribution
  rw [hF, sub_le_sub_iff_right]

/-- The conditional ranking on every event satisfies the three primitive mixture axioms. -/
theorem eventRanking_mixtureAxioms (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (base : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) : MixtureAxioms (EventRanking hA r base E hE) := by
  obtain ⟨F, hFr, hFa⟩ := (problem_5_6a hA r).mp hr
  exact mixtureAxioms_of_representation (eventLotteryIndex_represents hA hFr base hE)
    (eventLotteryIndex_affine hA hFa base hE)

/-- The source's calibrated event weight, defined for every algebra event. -/
noncomputable def EventProbability (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base good : SimpleLottery X) (E : A) : ℝ := EventLotteryIndex hA F base E.val E.property good

/-- An event is null for the calibrating pair when the decision maker is indifferent on it. -/
def CalibrationNull (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop)
    (base good : SimpleLottery X) (E : A) : Prop :=
  Indifferent (EventRanking hA r base E.val E.property) good base

/-- A real-valued finitely additive probability on an event algebra. -/
def FinitelyAdditiveProbability (hA : IsSetAlgebra A) (p : A → ℝ) : Prop :=
  (∀ E, p E ∈ Set.Icc 0 1) ∧ p ⟨Set.univ, hA.univ_mem⟩ = 1 ∧ p ⟨∅, hA.empty_mem⟩ = 0 ∧
    ∀ E D : A, Disjoint E.val D.val →
      p ⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ = p E + p D

/-- Zero calibrated weight is exactly indifference on the event. -/
theorem eventProbability_zero_iff_null (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r)
    (base good : SimpleLottery X) (E : A) :
    EventProbability hA F base good E = 0 ↔ CalibrationNull hA r base good E := by
  have hr := eventLotteryIndex_represents hA hF base E.property
  unfold EventProbability CalibrationNull Indifferent
  rw [hr, hr, eventLotteryIndex_base]
  exact ⟨fun he => ⟨he.ge, he.le⟩, fun he => le_antisymm he.2 he.1⟩

/-- **Problem 5.6(e):** conditional weak preference makes the normalized weights probabilities. -/
theorem problem_5_6e (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (ha : EventAffine hA F)
    (base good : SimpleLottery X) (hn : F (EventConstant hA good) - F (EventConstant hA base) = 1)
    (hw : ∀ E : A, EventRanking hA r base E.val E.property good base) :
    FinitelyAdditiveProbability hA (EventProbability hA F base good) ∧
      ∀ E, EventProbability hA F base good E = 0 ↔ CalibrationNull hA r base good E := by
  let p := EventProbability hA F base good
  have whole : p ⟨Set.univ, hA.univ_mem⟩ = 1 :=
    (eventContribution_univ hA F base (EventConstant hA good)).trans hn
  have add (E D : A) (hd : Disjoint E.val D.val) :
      p ⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ = p E + p D :=
    eventContribution_union hA ha base E.property D.property hd (EventConstant hA good)
  have hnon (E : A) : 0 ≤ p E := by
    have h := (eventLotteryIndex_represents hA hF base E.property good base).mp (hw E)
    rwa [eventLotteryIndex_base] at h
  refine ⟨⟨fun E => ⟨hnon E, ?_⟩, whole, eventContribution_empty hA F base _, add⟩,
    eventProbability_zero_iff_null hA hF base good⟩
  let D : A := ⟨E.valᶜ, hA.compl_mem E.property⟩
  have hsum := add E D disjoint_compl_right
  have hset : (⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ : A) =
      ⟨Set.univ, hA.univ_mem⟩ := Subtype.ext (Set.union_compl_self _)
  rw [hset, whole] at hsum
  linarith [hnon D]

end Kreps.ChoiceUnderUncertainty
