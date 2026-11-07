/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryMixtureRepresentation
import UtilityForMoney.RiskAttitudes

/-!
# Monetary utility from primitive preferences over lotteries

Kreps I, opening of Chapter 6 and pp. 123–127. The copied Chapter 5 mixture
theorem supplies the prize utility from primitive preferences. The numbered
money-utility tests use the same order, point masses, expectations and notion
of indifference. The mean payoff remains inside the original prize interval.
-/

namespace Kreps.UtilityForMoney

open Convexity

/-- The three primitive axioms supply the expected-utility representation used throughout
the chapter, on arbitrary prize types and arbitrary finite supports. -/
theorem monetary_representation_of_axioms {X : Type*} {r : SimpleLottery X → SimpleLottery X → Prop}
    (h : LotteryTheory.MixtureAxioms r) :
    ∃ U : X → ℝ, ∀ p q, r p q ↔ ExpectedUtility U q ≤ ExpectedUtility U p :=
  LotteryTheory.proposition_5_3.mp h

/-- Proposition 6.1 expressed in the primitive strict preference over sure lotteries. -/
theorem strictMono_iff_sure_preference {X : Type*} [Preorder X]
    {r : SimpleLottery X → SimpleLottery X → Prop} {U : X → ℝ}
    (h : LotteryTheory.Represents (ExpectedUtility U) r) :
    StrictMono U ↔ ∀ x y : X, x < y → LotteryTheory.Strict r (.single y) (.single x) := by
  unfold LotteryTheory.Represents at h
  simp only [LotteryTheory.Strict, h, expectedUtility_single, ← lt_iff_le_not_ge]
  exact ⟨fun hm _ _ hxy => hm hxy, fun hm _ _ hxy => hm _ _ hxy⟩

/-- A certainty equivalent is equivalently primitive indifference between a sure prize and the
original monetary lottery. -/
theorem isCertaintyEquivalent_iff_indifferent {X : Type*}
    {r : SimpleLottery X → SimpleLottery X → Prop} {U : X → ℝ}
    (h : LotteryTheory.Represents (ExpectedUtility U) r) (p : SimpleLottery X) (x : X) :
    IsCertaintyEquivalent U p x ↔ LotteryTheory.Indifferent r (.single x) p := by
  unfold LotteryTheory.Represents at h
  simp only [IsCertaintyEquivalent, LotteryTheory.Indifferent, h, expectedUtility_single]
  exact ⟨fun he => ⟨he.ge, he.le⟩, fun hh => hh.2.antisymm hh.1⟩

/-- Proposition 6.3 stated with the actual primitive ranking of the sure mean and the lottery. -/
theorem concave_iff_sure_mean_preferred {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    {r : SimpleLottery S → SimpleLottery S → Prop}
    (h : LotteryTheory.Represents (ExpectedUtility (fun x : S => U x)) r) :
    ConcaveOn ℝ S U ↔ ∀ p : SimpleLottery S,
      r (.single ⟨ExpectedUtility Subtype.val p,
        expectedUtility_mem_of_convex hS Subtype.val Subtype.property p⟩) p := by
  unfold LotteryTheory.Represents at h
  simpa only [h, expectedUtility_single] using proposition_6_3 hS U

/-- On an interval, risk aversion is equivalent to nonnegative premia for every lottery. -/
theorem concave_iff_nonnegative_premia {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hc : ContinuousOn U S) (hi : StrictMonoOn U S) :
    ConcaveOn ℝ S U ↔ ∀ (p : SimpleLottery S) (c : S),
      IsCertaintyEquivalent (fun x : S => U x) p c → 0 ≤ RiskPremium p c := by
  refine ⟨fun h _ _ he => riskPremium_nonneg h hi he, ?_⟩
  intro h
  apply (proposition_6_3 hS U).mpr
  intro p
  obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
  have hmean := expectedUtility_mem_of_convex hS Subtype.val Subtype.property p
  exact he.ge.trans (hi.monotoneOn c.property hmean (sub_nonneg.mp (h p c he)))

/-- Risk neutrality is equivalently a zero premium for every lottery on the monetary interval. -/
theorem riskNeutral_iff_zero_premia {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hc : ContinuousOn U S) (hi : StrictMonoOn U S) :
    (∀ p : SimpleLottery S,
      ExpectedUtility (fun x : S => U x) p = U (ExpectedUtility Subtype.val p)) ↔
    ∀ (p : SimpleLottery S) (c : S),
      IsCertaintyEquivalent (fun x : S => U x) p c → RiskPremium p c = 0 := by
  constructor
  · intro h p c he
    have hmean := expectedUtility_mem_of_convex hS Subtype.val Subtype.property p
    exact sub_eq_zero.mpr (hi.injOn c.property hmean (he.trans (h p))).symm
  · intro h p
    obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
    rw [sub_eq_zero.mp (h p c he)]
    exact he.symm

end Kreps.UtilityForMoney
