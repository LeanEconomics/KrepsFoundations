/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.DemandIndirectUtility
import UtilityForMoney.LotteryMixtureRepresentation
import UtilityForMoney.MonetaryLotteries

/-!
# Income risk resolved before consumption choice

Kreps I, Proposition 6.16, pp. 135–137. Each realized nonnegative income finances
a utility-maximizing bundle. Pushing a lottery through any optimal selection
induces the same expected indirect utility. The copied Chapter 3 results supply
actual budget maxima, continuity and exhaustion.
-/

namespace Kreps.UtilityForMoney

open scoped NNReal
open Convexity

variable {k : ℕ}

/-- Push a simple lottery through the deterministic rule selecting a consumption bundle. -/
theorem expectedUtility_map {X Y : Type*} (U : Y → ℝ) (f : X → Y) (p : SimpleLottery X) :
    ExpectedUtility U (p.map f) = ExpectedUtility (fun x => U (f x)) p := by
  rw [expectedUtility_eq_affine, expectedUtility_eq_affine, StdSimplex.affineMapMk_apply,
    StdSimplex.affineMapMk_apply, iConvexComb_map]

/-- Income lotteries are ranked by the lotteries of bundles bought after income is observed. -/
def InducedIncomePreference
    (r : SimpleLottery (Demand.NonnegativeOrthant k) → SimpleLottery (Demand.NonnegativeOrthant k) →
      Prop) (f : ℝ≥0 → Demand.NonnegativeOrthant k) (p q : SimpleLottery ℝ≥0) : Prop :=
  r (p.map f) (q.map f)

/-- All optimal selections yield expected indirect utility for an income lottery. -/
theorem incomeLottery_value {U : Demand.NonnegativeOrthant k → ℝ} (p : Demand.PositivePrices k)
    (f : ℝ≥0 → Demand.NonnegativeOrthant k) (hf : ∀ y, f y ∈ Demand.MarshallianDemand U p y)
    (q : SimpleLottery ℝ≥0) :
    ExpectedUtility U (q.map f) = ExpectedUtility (Demand.IndirectUtility U p) q := by
  rw [expectedUtility_map]
  exact congrArg (fun g => ExpectedUtility g q)
    (funext fun y => (Demand.indirectUtility_eq_of_mem (hf y)).symm)

/-- Proposition 6.16. Every optimal choice rule induces the three mixture axioms on income risk. -/
theorem proposition_6_16 {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    {r : SimpleLottery (Demand.NonnegativeOrthant k) → SimpleLottery (Demand.NonnegativeOrthant k) →
      Prop} (hr : LotteryTheory.Represents (ExpectedUtility U) r) (p : Demand.PositivePrices k) :
    (∃ f : ℝ≥0 → Demand.NonnegativeOrthant k, ∀ y, f y ∈ Demand.MarshallianDemand U p y) ∧
      ∀ f : ℝ≥0 → Demand.NonnegativeOrthant k, (∀ y, f y ∈ Demand.MarshallianDemand U p y) →
        LotteryTheory.Represents (ExpectedUtility (Demand.IndirectUtility U p))
          (InducedIncomePreference r f) ∧
          LotteryTheory.MixtureAxioms (InducedIncomePreference r f) := by
  constructor
  · exact Classical.axiomOfChoice (fun y => Demand.proposition_3_1b hU p y)
  · intro f hf
    have hi : LotteryTheory.Represents (ExpectedUtility (Demand.IndirectUtility U p))
        (InducedIncomePreference r f) := by
      intro q t
      change r (q.map f) (t.map f) ↔ _
      rw [hr, incomeLottery_value p f hf, incomeLottery_value p f hf]
    exact ⟨hi, LotteryTheory.proposition_5_3.mpr ⟨_, hi⟩⟩

/-- Part (a). Indirect utility is continuous in nonnegative income, including at the origin. -/
theorem proposition_6_16a {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (p : Demand.PositivePrices k) : Continuous (Demand.IndirectUtility U p) :=
  (Demand.proposition_3_3c hU).comp (continuous_const.prodMk continuous_id)

/-- Part (b). Local insatiability rules out equal values at two strictly ordered incomes. -/
theorem proposition_6_16b {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hi : Demand.LocallyInsatiable (Demand.UtilityPref U)) (p : Demand.PositivePrices k) :
    StrictMono (Demand.IndirectUtility U p) := by
  intro y z hyz
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hU p y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hU p z
  rw [Demand.indirectUtility_eq_of_mem hx, Demand.indirectUtility_eq_of_mem hw]
  apply lt_of_not_ge
  intro hle
  have hy : Demand.Expenditure p x ≤ (y : ℝ) := hx.1
  have hxz : x ∈ Demand.MarshallianDemand U p z :=
    ⟨hy.trans (show (y : ℝ) ≤ (z : ℝ) from hyz.le),
      fun t ht => (show U t ≤ U w from hw.2 t ht).trans hle⟩
  have he := Demand.proposition_3_1d hi p z hxz
  exact (show (y : ℝ) < (z : ℝ) from hyz).not_ge (he ▸ hy)

/-- Part (c). A mixture of two optimal bundles is affordable at the corresponding mixed income. -/
theorem proposition_6_16c {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (p : Demand.PositivePrices k) : ConcaveOn ℝ (Set.Ici 0)
      (fun y : ℝ => Demand.IndirectUtility U p y.toNNReal) := by
  refine ⟨convex_Ici _, ?_⟩
  intro y hy z hz a b ha hb hab
  let Y : ℝ≥0 := ⟨y, hy⟩
  let Z : ℝ≥0 := ⟨z, hz⟩
  let m := a * y + b * z
  have hm : 0 ≤ m := add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hz)
  let M : ℝ≥0 := ⟨m, hm⟩
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hU p Y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hU p Z
  obtain ⟨t, ht⟩ := Demand.proposition_3_1b hU p M
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
  let v := Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x w a ha'
  have hv : v ∈ Demand.BudgetSet p M := by
    change Demand.Expenditure p v ≤ m
    rw [show Demand.Expenditure p v = _ from Demand.expenditure_mix p x w a ha',
      show 1 - a = b by linarith]
    exact add_le_add (mul_le_mul_of_nonneg_left (show Demand.Expenditure p x ≤ y from hx.1) ha)
      (mul_le_mul_of_nonneg_left (show Demand.Expenditure p w ≤ z from hw.1) hb)
  have huv := hc x w a ha'
  have huv' : a * U x + b * U w ≤ U v := by simpa only [← show 1 - a = b by linarith] using huv
  have hco (c : ℝ) (h : 0 ≤ c) : c.toNNReal = ⟨c, h⟩ := NNReal.eq (Real.coe_toNNReal c h)
  change a * Demand.IndirectUtility U p y.toNNReal + b * Demand.IndirectUtility U p z.toNNReal ≤
    Demand.IndirectUtility U p m.toNNReal
  rw [hco y hy, hco z hz, hco m hm, Demand.indirectUtility_eq_of_mem hx,
    Demand.indirectUtility_eq_of_mem hw, Demand.indirectUtility_eq_of_mem ht]
  exact huv'.trans (ht.2 v hv)

/-- Concavity gives the income risk-aversion comparison at every finite-support lottery. -/
theorem incomeLottery_risk_averse {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (p : Demand.PositivePrices k) (q : SimpleLottery ℝ≥0) :
    ExpectedUtility (Demand.IndirectUtility U p) q ≤
      Demand.IndirectUtility U p (ExpectedUtility (fun y : ℝ≥0 => (y : ℝ)) q).toNNReal := by
  simpa only [Real.toNNReal_coe] using expectedUtility_jensen (proposition_6_16c hU hc p)
    (fun y : ℝ≥0 => (y : ℝ)) (fun y => y.property) q

end Kreps.UtilityForMoney
