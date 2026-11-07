/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EventProbabilities
import ChoiceUnderUncertainty.AffineUniqueness

/-!
# A common utility and subjective probabilities on an event algebra

Kreps I, Problem 5.6(e,f), pp. 121–122. Constant acts determine the common prize
utility. On each nonnull event affine uniqueness identifies the proportionality
factor by the two calibrating prizes. On null events indifference makes all
conditional expected utilities zero. The representation is independent of
the chosen finite partition and starts from the primitive mixture axioms.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- A strict pair can be normalized to zero and one within the primitive representation. -/
theorem eventRepresentation_normalized (hA : IsSetAlgebra A)
    {r : EventAct A X → EventAct A X → Prop} (hr : @MixtureAxioms _ (eventActConvexSpace hA) r)
    (b g : SimpleLottery X) (hs : Strict r (EventConstant hA g) (EventConstant hA b)) :
    ∃ F, Represents F r ∧ EventAffine hA F ∧
      F (EventConstant hA b) = 0 ∧ F (EventConstant hA g) = 1 := by
  let _ := eventActConvexSpace (X := X) hA
  obtain ⟨u, hur, hua⟩ := (problem_5_6a hA r).mp hr
  let lo := u (EventConstant hA b)
  let hi := u (EventConstant hA g)
  have hh : lo < hi := lt_of_not_ge (fun h => hs.2 ((hur _ _).mpr h))
  let a := (hi - lo)⁻¹
  have ha : 0 < a := inv_pos.mpr (sub_pos.mpr hh)
  have ht := positive_affine_representation hur hua a (-(a * lo)) ha
  refine ⟨_, ht.1, ht.2, by dsimp only [lo]; ring, ?_⟩
  change a * hi + -(a * lo) = 1
  calc
    _ = (hi - lo)⁻¹ * (hi - lo) := by dsimp only [a]; ring
    _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hh.ne')

/-- The source's null and common-ranking assumptions for conditional roulette lotteries. -/
def EventIndependentRankings (hA : IsSetAlgebra A)
    (r : EventAct A X → EventAct A X → Prop) (base good : SimpleLottery X) : Prop :=
  (∀ E : A, CalibrationNull hA r base good E → ∀ x : X,
    Indifferent (EventRanking hA r base E.val E.property) (PureLottery x) base) ∧
  ∀ E : A, ¬CalibrationNull hA r base good E → ∀ q t,
    EventRanking hA r base E.val E.property q t ↔ r (EventConstant hA q) (EventConstant hA t)

/-- The full-event index equals the original constant-act value less the common baseline. -/
theorem eventLotteryIndex_univ (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base q : SimpleLottery X) : EventLotteryIndex hA F base Set.univ hA.univ_mem q =
      F (EventConstant hA q) - F (EventConstant hA base) :=
  eventContribution_univ hA F base (EventConstant hA q)

/-- Local utility equals event probability times the global roulette index, also on null events. -/
theorem eventLotteryIndex_factor (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (ha : EventAffine hA F)
    (base good : SimpleLottery X) (hn : F (EventConstant hA good) - F (EventConstant hA base) = 1)
    (hi : EventIndependentRankings hA r base good) (E : A) (q : SimpleLottery X) :
    EventLotteryIndex hA F base E.val E.property q = EventProbability hA F base good E *
      EventLotteryIndex hA F base Set.univ hA.univ_mem q := by
  let G := EventLotteryIndex hA F base Set.univ hA.univ_mem
  let L := EventLotteryIndex hA F base E.val E.property
  have hr := eventLotteryIndex_represents hA hF base E.property
  have hLb : L base = 0 := eventLotteryIndex_base hA F base E.property
  have hGb : G base = 0 := eventLotteryIndex_base hA F base hA.univ_mem
  have hGg : G good = 1 := (eventLotteryIndex_univ hA F base good).trans hn
  by_cases hnull : CalibrationNull hA r base good E
  · have hz := (eventProbability_zero_iff_null hA hF base good E).mpr hnull
    have pure_zero (x : X) : EventPrizeUtility hA F base E.val E.property x = 0 := by
      have hpx := hi.1 E hnull x
      have he : L (PureLottery x) = L base :=
        le_antisymm ((hr _ _).mp hpx.2) ((hr _ _).mp hpx.1)
      exact he.trans hLb
    rw [hz, zero_mul, eventLotteryIndex_expectedUtility hA ha]
    simp [ExpectedUtility, pure_zero]
  · have hcmp (x y : SimpleLottery X) : G x ≤ G y ↔ L x ≤ L y := by
      change EventLotteryIndex hA F base Set.univ hA.univ_mem x ≤
        EventLotteryIndex hA F base Set.univ hA.univ_mem y ↔ _
      rw [eventLotteryIndex_univ, eventLotteryIndex_univ, sub_le_sub_iff_right]
      exact (hF _ _).symm.trans ((hi.2 E hnull y x).symm.trans (hr y x))
    obtain ⟨a, _, t, ht⟩ := affineInMix_unique (eventLotteryIndex_affine hA ha base hA.univ_mem)
      (eventLotteryIndex_affine hA ha base E.property) hcmp
    have hb : L base = a * G base + t := ht base
    have hg : L good = a * G good + t := ht good
    rw [hLb, hGb, mul_zero, zero_add] at hb
    rw [hGg, mul_one, ← hb, add_zero] at hg
    change L q = L good * G q
    exact (ht q).trans (by change a * G q + t = L good * G q; rw [← hb, hg, add_zero])

/-- **Problem 5.6(f):** primitive preferences on doubly simple acts admit finitely additive SEU. -/
theorem problem_5_6f (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (b g : X)
    (hs : Strict r (EventConstant hA (PureLottery g)) (EventConstant hA (PureLottery b)))
    (hw : ∀ E : A, EventRanking hA r (PureLottery b) E.val E.property (PureLottery g)
      (PureLottery b))
    (hi : EventIndependentRankings hA r (PureLottery b) (PureLottery g)) :
    ∃ (p : A → ℝ) (U : X → ℝ) (V : EventAct A X → ℝ),
      FinitelyAdditiveProbability hA p ∧ Represents V r ∧
      (∀ E, p E = 0 ↔ CalibrationNull hA r (PureLottery b) (PureLottery g) E) ∧
      ∀ (h : EventAct A X) (n : ℕ) (c : S → Fin n) (hc : ∀ i, {s | c s = i} ∈ A)
        (q : Fin n → SimpleLottery X), (∀ s, h.val s = q (c s)) →
          V h = ∑ i, p ⟨{s | c s = i}, hc i⟩ * ExpectedUtility U (q i) := by
  let base := PureLottery b
  let good := PureLottery g
  obtain ⟨F, hFr, hFa, hb, hg⟩ := eventRepresentation_normalized hA hr base good hs
  have hn : F (EventConstant hA good) - F (EventConstant hA base) = 1 := by rw [hb, hg, sub_zero]
  obtain ⟨hp, hz⟩ := problem_5_6e hA hFr hFa base good hn hw
  refine ⟨EventProbability hA F base good, EventPrizeUtility hA F base Set.univ hA.univ_mem,
    F, hp, hFr, hz, ?_⟩
  intro h n c hc q hh
  have H := problem_5_6d hA hFa base c hc q h hh
  rw [hb, sub_zero] at H
  rw [H]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eventLotteryIndex_expectedUtility hA hFa, ← eventLotteryIndex_expectedUtility hA hFa]
  exact eventLotteryIndex_factor hA hFr hFa base good hn hi ⟨_, hc i⟩ (q i)

/-- Omitting conditional nonnegativity admits signed unit-mass weights, even under the axioms. -/
theorem event_sign_counterexample :
    ∃ F : HorseLottery (Fin 2) Bool → ℝ, MixtureAxioms (UtilityPref F) ∧
      F (fun _ => PureLottery false) = 0 ∧ F (fun _ => PureLottery true) = 1 ∧
      F ![PureLottery true, PureLottery false] = -1 := by
  let U : Fin 2 → Bool → ℝ := ![fun b => if b then -1 else 0, fun b => if b then 2 else 0]
  refine ⟨HorseValue U, mixtureAxioms_of_representation (fun _ _ => Iff.rfl)
    (horseValue_affine U), ?_⟩
  norm_num [HorseValue, StateAdditiveValue, U, expectedUtility_pure, Fin.sum_univ_two]

end Kreps.ChoiceUnderUncertainty
