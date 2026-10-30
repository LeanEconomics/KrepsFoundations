/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import ConsumerDemand.CobbDouglasDemand

/-!
# Marginal utility per dollar and expenditure shares

Kreps I, pp. 60-62. Consumed goods have equal marginal utility per dollar;
no unconsumed good has a larger ratio. Cross-multiplied identities remain valid
when the multiplier is zero. A ratio of marginal utilities is asserted only
when its denominator is nonzero, rather than giving `0/0` an economic meaning.
The Cobb-Douglas corollaries include the source's ten-percent illustration.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Combined optimality gives a common upper bound on marginal utility per dollar. -/
theorem combinedOptimality_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m) :
    ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j / p.val j ≤ l) ∧
      (∀ j, 0 < x.val j → m j / p.val j = l) := by
  obtain ⟨_, l, hl, hm, he, _⟩ := ho
  refine ⟨l, hl, fun j => (div_le_iff₀ (p.property j)).mpr (hm j), ?_⟩
  intro j hj
  exact (div_eq_iff (ne_of_gt (p.property j))).mpr (he j hj)

/-- No good offers a higher marginal return per dollar than a consumed good. -/
theorem consumed_good_maximizes_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hj : 0 < x.val j) : m i / p.val i ≤ m j / p.val j := by
  obtain ⟨l, _, hm, he⟩ := combinedOptimality_bangForBuck ho
  rw [he j hj]
  exact hm i

/-- Consumed goods have equal marginal returns per dollar, even when both returns vanish. -/
theorem consumed_goods_equal_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) :
    m i / p.val i = m j / p.val j :=
  le_antisymm (consumed_good_maximizes_bangForBuck ho i j hj)
    (consumed_good_maximizes_bangForBuck ho j i hi)

/-- The price/marginal identity without division by a possibly zero marginal. -/
theorem consumed_goods_marginal_cross_product {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) :
    m i * p.val j = m j * p.val i := by
  have h := consumed_goods_equal_bangForBuck ho i j hi hj
  exact (div_eq_div_iff (ne_of_gt (p.property i)) (ne_of_gt (p.property j))).mp h

/-- The marginal-utility ratio equals the price ratio when the marginal denominator is nonzero. -/
theorem consumed_goods_marginal_ratio {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) (hmj : m j ≠ 0) :
    m i / m j = p.val i / p.val j := by
  apply (div_eq_div_iff hmj (ne_of_gt (p.property j))).mpr
  simpa only [mul_comm] using consumed_goods_marginal_cross_product ho i j hi hj

/-- Each Cobb-Douglas expenditure is precisely its exponent's fraction of total income. -/
theorem cobbDouglas_expenditure_share {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    p.val j * (CobbDouglasBundle a ha p y).val j = (a j / ∑ i, a i) * (y : ℝ) := by
  dsimp only [CobbDouglasBundle]
  field_simp [ne_of_gt (p.property j)]

/-- Changing other prices leaves Cobb-Douglas demand for a fixed-price good unchanged. -/
theorem cobbDouglas_other_prices_irrelevant {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p q : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : p.val j = q.val j) :
    (CobbDouglasBundle a ha p y).val j = (CobbDouglasBundle a ha q y).val j := by
  simp only [CobbDouglasBundle, hj]

/-- The literal ten-percent share illustration on p. 60. -/
theorem cobbDouglas_ten_percent {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : a j / (∑ i, a i) = 1 / 10) :
    (CobbDouglasBundle a ha p y).val j = (y : ℝ) / (10 * p.val j) := by
  simp only [CobbDouglasBundle, hj]
  ring

end Kreps.ConsumerDemand
