/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries
import Mathlib.Analysis.Convex.Continuous

/-!
# Risk attitudes and finite Jensen induction

Kreps I, pp. 125–127 and Problem 6.1(b). The induction combines one new prize
with the normalized remaining lottery. It permits zero weights. The same binary
tests distinguish risk seeking, risk neutrality and risk aversion on intervals.
-/

namespace Kreps.UtilityForMoney

/-- The center-of-mass form of the induction requested in Problem 6.1(b). -/
theorem jensen_by_support_induction {I : Type*} {S : Set ℝ} {U : ℝ → ℝ} (hc : ConcaveOn ℝ S U)
    (w x : I → ℝ) (T : Finset I) (hn : ∀ i ∈ T, 0 ≤ w i) (hp : 0 < ∑ i ∈ T, w i)
    (hs : ∀ i ∈ T, x i ∈ S) :
    T.centerMass w (fun i => U (x i)) ≤ U (T.centerMass w x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at hp
  | @insert i T hi ih =>
    have hnt (j) (hj : j ∈ T) := hn j (Finset.mem_insert_of_mem hj)
    have hst (j) (hj : j ∈ T) := hs j (Finset.mem_insert_of_mem hj)
    have hni := hn i (Finset.mem_insert_self _ _)
    have hxi := hs i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi] at hp
    have hnT := Finset.sum_nonneg hnt
    rcases hnT.eq_or_lt with ht | ht
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg hnt).mp ht.symm
      have hzero (f : I → ℝ) : ∑ j ∈ T, w j * f j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]
      have hw : w i ≠ 0 := by linarith
      simp only [Finset.centerMass, Finset.sum_insert hi, smul_eq_mul, ht.symm,
        hzero, add_zero, inv_mul_cancel_left₀ hw, le_refl]
    · rw [Finset.centerMass_insert _ _ _ hi ht.ne', Finset.centerMass_insert _ _ _ hi ht.ne']
      let a := w i / (w i + ∑ j ∈ T, w j)
      let b := (∑ j ∈ T, w j) / (w i + ∑ j ∈ T, w j)
      have ha : 0 ≤ a := div_nonneg hni hp.le
      have hb : 0 ≤ b := div_nonneg ht.le hp.le
      have hab : a + b = 1 := by
        dsimp [a, b]
        rw [← add_div, div_self hp.ne']
      have h := hc.2 hxi (hc.1.centerMass_mem hnt ht hst) ha hb hab
      exact (add_le_add_right (mul_le_mul_of_nonneg_left (ih hnt ht hst) hb)
        (a * U (x i))).trans h

/-- Problem 6.1(b). Normalized weights give Jensen's inequality for every finite list. -/
theorem problem_6_1b_induction {I : Type*} {S : Set ℝ} {U : ℝ → ℝ} (hc : ConcaveOn ℝ S U)
    (w x : I → ℝ) (T : Finset I) (hn : ∀ i ∈ T, 0 ≤ w i) (hp : ∑ i ∈ T, w i = 1)
    (hs : ∀ i ∈ T, x i ∈ S) : (∑ i ∈ T, w i * U (x i)) ≤ U (∑ i ∈ T, w i * x i) := by
  simpa only [Finset.centerMass, hp, inv_one, smul_eq_mul, one_mul] using
    jensen_by_support_induction hc w x T hn (hp.symm ▸ zero_lt_one) hs

/-- Risk seeking on an interval is equivalent to convex prize utility there. -/
theorem riskSeeking_iff_convex {S : Set ℝ} (hS : Convex ℝ S) (U : ℝ → ℝ) :
    ConvexOn ℝ S U ↔ ∀ p : SimpleLottery S,
      U (ExpectedUtility Subtype.val p) ≤ ExpectedUtility (fun x : S => U x) p := by
  constructor
  · intro h p
    simpa only [ExpectedUtility, Finsupp.sum, smul_eq_mul] using h.map_sum_le
      (t := p.weights.support) (w := fun x => p.weights x) (p := fun x : S => x.val)
      (fun x _ => p.nonneg x) p.total (fun x _ => x.property)
  · intro h
    refine ⟨hS, ?_⟩
    intro x hx y hy a b ha hb hab
    have hwt : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    simpa only [expectedUtility_binary, smul_eq_mul, show 1 - a = b by linarith] using
      h (BinaryLottery (⟨x, hx⟩ : S) ⟨y, hy⟩ a hwt)

/-- Risk neutrality is equivalently both Jensen inequalities, hence equality on every mixture. -/
theorem riskNeutral_iff_affine_mixes {S : Set ℝ} (hS : Convex ℝ S) (U : ℝ → ℝ) :
    (∀ p : SimpleLottery S,
      ExpectedUtility (fun x : S => U x) p = U (ExpectedUtility Subtype.val p)) ↔
    ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      U (a * x + b * y) = a * U x + b * U y := by
  constructor
  · intro h x hx y hy a b ha hb hab
    have hw : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    simpa only [expectedUtility_binary, show 1 - a = b by linarith] using
      (h (BinaryLottery (⟨x, hx⟩ : S) ⟨y, hy⟩ a hw)).symm
  · intro h
    have hc : ConcaveOn ℝ S U :=
      ⟨hS, fun x hx y hy a b ha hb hab => (h x hx y hy a b ha hb hab).ge⟩
    have hv : ConvexOn ℝ S U :=
      ⟨hS, fun x hx y hy a b ha hb hab => (h x hx y hy a b ha hb hab).le⟩
    exact fun p => le_antisymm ((proposition_6_3 hS U).mp hc p)
      ((riskSeeking_iff_convex hS U).mp hv p)

/-- Figure 6.1. The 60/40 lottery has a certainty equivalent no higher than its mean. -/
theorem figure_6_1 {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ} (hc : ContinuousOn U S)
    (hU : ConcaveOn ℝ S U) (hm : StrictMonoOn U S) (x y : S) :
    let p := BinaryLottery x y (3 / 5) (by constructor <;> norm_num)
    ∃ c : S, IsCertaintyEquivalent (fun z : S => U z) p c ∧
      U c = (3 / 5) * U x + (2 / 5) * U y ∧ (c : ℝ) ≤ (3 / 5) * x.val + (2 / 5) * y.val := by
  intro p
  obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
  have hce := riskPremium_nonneg hU hm he
  have hval := he
  change U c = ExpectedUtility (fun z : S => U z) p at hval
  have hb (f : S → ℝ) : ExpectedUtility f p = (3 / 5) * f x + (2 / 5) * f y := by
    simpa only [show (1 : ℝ) - 3 / 5 = 2 / 5 by norm_num] using
      expectedUtility_binary f x y (3 / 5) (by constructor <;> norm_num)
  rw [hb] at hval
  unfold RiskPremium at hce
  rw [hb] at hce
  exact ⟨c, he, hval, by linarith⟩

/-- Concavity guarantees continuity at the interior monetary prizes. -/
theorem concaveUtility_continuousOn_interior {S : Set ℝ} {U : ℝ → ℝ} (h : ConcaveOn ℝ S U) :
    ContinuousOn U (interior S) := h.continuousOn_interior

end Kreps.UtilityForMoney
