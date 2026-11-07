/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.IncomeChoice

/-!
# Joint price and income risk

Kreps I, pp. 137–138. Draw income and prices independently from finite-support
lotteries, then choose an optimal bundle after observing both. The induced income
index is the price-weighted indirect utility. The source's two correlated
couplings of incomes 10,000 and 20,000 demonstrate why the marginal laws alone
do not determine the consumer's purchasing power.
-/

namespace Kreps.UtilityForMoney

open scoped NNReal
open Convexity

variable {k : ℕ}

/-- Draw one income, then use the same conditional price law at every income. -/
noncomputable def IndependentPriceIncome (P : SimpleLottery (Demand.PositivePrices k))
    (Q : SimpleLottery ℝ≥0) : SimpleLottery (Demand.PositivePrices k × ℝ≥0) :=
  Q.iConvexComb fun y => P.map fun p => (p, y)

/-- For a fixed independent price lottery, the income index averages indirect utility. -/
noncomputable def PriceAveragedValue (U : Demand.NonnegativeOrthant k → ℝ)
    (P : SimpleLottery (Demand.PositivePrices k)) (y : ℝ≥0) : ℝ :=
  ExpectedUtility (fun p => Demand.IndirectUtility U p y) P

/-- The expected value of the product draw is the iterated expected indirect utility. -/
theorem independent_price_income_value (U : Demand.NonnegativeOrthant k → ℝ)
    (P : SimpleLottery (Demand.PositivePrices k)) (Q : SimpleLottery ℝ≥0) :
    ExpectedUtility (fun py => Demand.IndirectUtility U py.1 py.2) (IndependentPriceIncome P Q) =
      ExpectedUtility (PriceAveragedValue U P) Q := by
  let g : Demand.PositivePrices k × ℝ≥0 → ℝ := fun py => Demand.IndirectUtility U py.1 py.2
  change ExpectedUtility g _ = _
  rw [expectedUtility_eq_affine, IndependentPriceIncome,
    (StdSimplex.affineMapMk g).isAffineMap.map_iConvexComb, iConvexComb_eq_sum]
  apply Finset.sum_congr rfl
  intro y _
  change _ * StdSimplex.affineMapMk g (P.map fun p => (p, y)) = _
  rw [← expectedUtility_eq_affine, expectedUtility_map]
  rfl

/-- Independent price risk preserves continuity in nonnegative income. -/
theorem priceAveragedValue_continuous {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (P : SimpleLottery (Demand.PositivePrices k)) : Continuous (PriceAveragedValue U P) := by
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (proposition_6_16a hu p)

/-- Positive support weights preserve strict increase of the income index. -/
theorem priceAveragedValue_strictMono {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (hi : Demand.LocallyInsatiable (Demand.UtilityPref U))
    (P : SimpleLottery (Demand.PositivePrices k)) : StrictMono (PriceAveragedValue U P) := by
  intro y z hyz
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum_of_nonempty P.support_weights_nonempty
  intro p hp
  have hpos := lt_of_le_of_ne (P.nonneg p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  exact mul_lt_mul_of_pos_left (proposition_6_16b hu hi p hyz) hpos

/-- Independent price risk preserves concavity of indirect utility in income. -/
theorem priceAveragedValue_concave {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (P : SimpleLottery (Demand.PositivePrices k)) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => PriceAveragedValue U P y.toNNReal) := by
  refine ⟨convex_Ici _, ?_⟩
  intro y hy z hz a b ha hb hab
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have he := (proposition_6_16c hu hc p).2 hy hz ha hb hab
  simp only [smul_eq_mul] at he
  calc
    _ = P.weights p * (a * Demand.IndirectUtility U p y.toNNReal +
        b * Demand.IndirectUtility U p z.toNNReal) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (P.nonneg p)

/-- A finite price lottery at fixed income is valued by indirect utility at each price. -/
theorem fixed_income_price_lottery_value {U : Demand.NonnegativeOrthant k → ℝ} (y : ℝ≥0)
    (P : SimpleLottery (Demand.PositivePrices k)) (buy : Demand.PositivePrices k →
      Demand.NonnegativeOrthant k) (hb : ∀ p, buy p ∈ Demand.MarshallianDemand U p y) :
    ExpectedUtility U (P.map buy) = PriceAveragedValue U P y := by
  rw [expectedUtility_map]
  exact congrArg (fun g => ExpectedUtility g P)
    (funext fun p => (Demand.indirectUtility_eq_of_mem (hb p)).symm)

/-- At fixed income indirect utility is continuous in the positive prices. -/
theorem indirectUtility_continuous_prices {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (y : ℝ≥0) : Continuous (fun p => Demand.IndirectUtility U p y) :=
  (Demand.proposition_3_3c hu).comp (continuous_id.prodMk continuous_const)

/-- Increasing any prices weakly shrinks the budget and weakly lowers attained indirect utility. -/
theorem indirectUtility_antitone_prices {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (y : ℝ≥0) {p q : Demand.PositivePrices k} (hpq : p.val ≤ q.val) :
    Demand.IndirectUtility U q y ≤ Demand.IndirectUtility U p y := by
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hu q y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hu p y
  rw [Demand.indirectUtility_eq_of_mem hx, Demand.indirectUtility_eq_of_mem hw]
  apply hw.2 x
  apply le_trans _ (show Demand.Expenditure q x ≤ (y : ℝ) from hx.1)
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hpq i) (x.property i))

/-- Doubling prices and income preserves purchasing power; reversing their pairing does not. -/
theorem two_price_income_couplings (p : Demand.PositivePrices k) :
    Demand.BudgetSet (Demand.ScalePrices 2 (by norm_num) p) 20000 = Demand.BudgetSet p 10000 ∧
    Demand.BudgetSet (Demand.ScalePrices 2 (by norm_num) p) 10000 = Demand.BudgetSet p 5000 := by
  constructor
  · ext x
    change Demand.Expenditure _ x ≤ (20000 : ℝ) ↔ Demand.Expenditure p x ≤ (10000 : ℝ)
    rw [Demand.expenditure_scalePrices]
    constructor <;> intro h <;> linarith
  · ext x
    change Demand.Expenditure _ x ≤ (10000 : ℝ) ↔ Demand.Expenditure p x ≤ (5000 : ℝ)
    rw [Demand.expenditure_scalePrices]
    constructor <;> intro h <;> linarith

/-- The equal-probability purchasing-power lottery is constant or ranges from 5,000 to 20,000. -/
theorem two_price_income_values (U : Demand.NonnegativeOrthant k → ℝ)
    (p : Demand.PositivePrices k) :
    let q := Demand.ScalePrices 2 (by norm_num) p
    let v := fun py : Demand.PositivePrices k × ℝ≥0 => Demand.IndirectUtility U py.1 py.2
    ExpectedUtility v (BinaryLottery (p, 10000) (q, 20000) (1 / 2) (by norm_num)) =
        Demand.IndirectUtility U p 10000 ∧
      ExpectedUtility v (BinaryLottery (q, 10000) (p, 20000) (1 / 2) (by norm_num)) =
        (Demand.IndirectUtility U p 5000 + Demand.IndirectUtility U p 20000) / 2 := by
  dsimp only
  rw [expectedUtility_binary, expectedUtility_binary]
  simp only [Demand.IndirectUtility, two_price_income_couplings p |>.1,
    two_price_income_couplings p |>.2]
  constructor <;> ring

/-- Mapping a binary draw transforms each branch and keeps its probability. -/
theorem priceRisk_map_binary {X Y : Type*} (f : X → Y) (x z : X)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    (BinaryLottery x z a ha).map f = BinaryLottery (f x) (f z) a ha := by
  unfold BinaryLottery
  rw [(StdSimplex.isAffineMap_map ℝ f).map_convexCombPair, StdSimplex.map_single,
    StdSimplex.map_single]

/-- The two source couplings have exactly the same marginal distributions of prices and income. -/
theorem two_price_income_marginals (p : Demand.PositivePrices k) :
    let q := Demand.ScalePrices 2 (by norm_num) p
    let joint₁ := BinaryLottery (p, (10000 : ℝ≥0)) (q, 20000) (1 / 2) (by norm_num)
    let joint₂ := BinaryLottery (q, (10000 : ℝ≥0)) (p, 20000) (1 / 2) (by norm_num)
    joint₁.map Prod.fst = joint₂.map Prod.fst ∧ joint₁.map Prod.snd = joint₂.map Prod.snd := by
  dsimp only
  simp only [priceRisk_map_binary, and_true]
  unfold BinaryLottery
  rw [convexCombPair_symm]
  norm_num

end Kreps.UtilityForMoney
