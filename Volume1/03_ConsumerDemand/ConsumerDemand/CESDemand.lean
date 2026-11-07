/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CESSupport
import ConsumerDemand.ConsumerProblem

/-!
# The CES consumer's demand

Kreps I, Problem 3.7, pp. 64-65. The full nonnegative orthant is retained.
For a negative exponent the utility is extended by zero whenever any commodity
quantity is zero, as required by the limiting interior formula. Positive income
has the unique interior demand proportional to `(a j / p j) ^ (1 / (1 - mu))`.
The proof compares every affordable alternative using strict support inequalities.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The power sum inside the CES utility. -/
noncomputable def CESPowerSum {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∑ j, a j * x.val j ^ mu

/-- CES utility, with its zero boundary extension for negative exponents. -/
noncomputable def CESUtility {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (x : NonnegativeOrthant k) : ℝ :=
  if mu < 0 ∧ ∃ j, x.val j = 0 then 0 else CESPowerSum a mu x ^ (1 / mu)

/-- The positive price-adjusted power weight in the CES demand formula. -/
noncomputable def CESWeight {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (p : PositivePrices k) (j : Fin k) : ℝ := (a j / p.val j) ^ (1 / (1 - mu))

/-- The expenditure needed to buy one unit of the vector of CES weights. -/
noncomputable def CESDenominator {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (p : PositivePrices k) : ℝ := ∑ j, p.val j * CESWeight a mu p j

/-- Every CES weight is positive when its primitive coefficient and price are positive. -/
theorem cesWeight_pos {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) (j : Fin k) : 0 < CESWeight a mu p j :=
  Real.rpow_pos_of_pos (div_pos (ha j) (p.property j)) _

/-- The CES denominator is strictly positive in a nonempty commodity space. -/
theorem cesDenominator_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) :
    0 < CESDenominator a mu p :=
  Finset.sum_pos (fun j _ => mul_pos (p.property j) (cesWeight_pos a ha mu p j))
    Finset.univ_nonempty

/-- The CES demand formula, scaled to exhaust the given income. -/
noncomputable def CESBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) :
    NonnegativeOrthant k :=
  ⟨fun j => ((y : ℝ) / CESDenominator a mu p) * CESWeight a mu p j,
    fun j => mul_nonneg (div_nonneg y.property (cesDenominator_pos a ha mu p).le)
      (cesWeight_pos a ha mu p j).le⟩

/-- Every coordinate of the formula is positive at positive income. -/
theorem cesBundle_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) (j : Fin k) :
    0 < (CESBundle a ha mu p y).val j :=
  mul_pos (div_pos hy (cesDenominator_pos a ha mu p)) (cesWeight_pos a ha mu p j)

/-- The explicit CES bundle exhausts income. -/
theorem expenditure_cesBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (CESBundle a ha mu p y) = (y : ℝ) := by
  unfold Expenditure CESBundle
  simp only
  simp_rw [mul_left_comm (p.val _), ← Finset.mul_sum]
  exact div_mul_cancel₀ _ (cesDenominator_pos a ha mu p).ne'

/-- The normalized power marginal has the same ratio to price in every coordinate. -/
theorem cesBundle_marginal_ratio {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (j : Fin k) :
    a j * (CESBundle a ha mu p y).val j ^ (mu - 1) =
      ((y : ℝ) / CESDenominator a mu p) ^ (mu - 1) * p.val j := by
  have hbase := div_pos (ha j) (p.property j)
  have hscale := div_pos hy (cesDenominator_pos a ha mu p)
  have he : 1 / (1 - mu) * (mu - 1) = -1 := by
    field_simp [ne_of_gt (sub_pos.mpr hmu)]
    ring
  change a j * (((y : ℝ) / CESDenominator a mu p) *
    (a j / p.val j) ^ (1 / (1 - mu))) ^ (mu - 1) = _
  rw [Real.mul_rpow hscale.le (Real.rpow_nonneg hbase.le _),
    ← Real.rpow_mul hbase.le, he, Real.rpow_neg_one]
  field_simp [ne_of_gt (ha j), ne_of_gt (p.property j)]

/-- Strict coordinate support inequalities sum to a strict budget comparison. -/
theorem cesPowerSum_strict_support {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) {x z : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j) (hz : mu < 0 → ∀ j, 0 < z.val j) (hne : z ≠ x) :
    (CESPowerSum a mu z - CESPowerSum a mu x) / mu <
      ∑ j, (a j * x.val j ^ (mu - 1)) * (z.val j - x.val j) := by
  have he : (CESPowerSum a mu z - CESPowerSum a mu x) / mu =
      ∑ j, a j * ((z.val j ^ mu - x.val j ^ mu) / mu) := by
    simp only [CESPowerSum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Finset.sum_lt_sum
  · intro j _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (normalizedPower_tangent_le hmu hm0 (hx j) (z.property j) (fun hm => hz hm j))
      (ha j).le
  · have hcoord : ∃ j, z.val j ≠ x.val j := by
      by_contra hn
      push Not at hn
      exact hne (Subtype.ext (funext hn))
    obtain ⟨j, hj⟩ := hcoord
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simpa only [mul_assoc] using mul_lt_mul_of_pos_left
      (normalizedPower_tangent_lt hmu hm0 (hx j) (z.property j)
        (fun hm => hz hm j) hj) (ha j)

/-- Every power sum is nonnegative on the full orthant. -/
theorem cesPowerSum_nonneg {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (x : NonnegativeOrthant k) : 0 ≤ CESPowerSum a mu x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (ha j).le (Real.rpow_nonneg (x.property j) _))

/-- Every power sum at an interior bundle is strictly positive. -/
theorem cesPowerSum_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    0 < CESPowerSum a mu x :=
  Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _))
    Finset.univ_nonempty

/-- The boundary clause does not affect the formula on the positive orthant. -/
theorem cesUtility_of_positive {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    CESUtility a mu x = CESPowerSum a mu x ^ (1 / mu) := by
  have hn : ¬∃ j, x.val j = 0 := fun ⟨j, hj⟩ => (hx j).ne' hj
  simp [CESUtility, hn]

/-- Interior CES utility is positive, for either sign of the exponent. -/
theorem cesUtility_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    0 < CESUtility a mu x := by
  rw [cesUtility_of_positive a mu hx]
  exact Real.rpow_pos_of_pos (cesPowerSum_pos a ha mu hx) _

/-- Every distinct affordable alternative has a smaller normalized power sum. -/
theorem cesPowerSum_strict_budget {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hzp : mu < 0 → ∀ j, 0 < z.val j) (hne : z ≠ CESBundle a ha mu p y) :
    (CESPowerSum a mu z - CESPowerSum a mu (CESBundle a ha mu p y)) / mu < 0 := by
  have hs := cesPowerSum_strict_support a ha hmu hm0
    (cesBundle_pos a ha mu p y hy) hzp hne
  simp_rw [cesBundle_marginal_ratio a ha hmu p y hy, mul_assoc,
    ← Finset.mul_sum] at hs
  have he : (∑ j, p.val j * (z.val j - (CESBundle a ha mu p y).val j)) =
      Expenditure p z - Expenditure p (CESBundle a ha mu p y) := by
    simp only [Expenditure, mul_sub, Finset.sum_sub_distrib]
  rw [he, expenditure_cesBundle] at hs
  exact hs.trans_le (mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_pos_of_pos (div_pos hy (cesDenominator_pos a ha mu p)) _).le
    (sub_nonpos.mpr hz))

/-- The explicit CES bundle strictly beats every other affordable bundle, including axes. -/
theorem cesUtility_strict_budget {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hne : z ≠ CESBundle a ha mu p y) :
    CESUtility a mu z < CESUtility a mu (CESBundle a ha mu p y) := by
  have hx := cesBundle_pos a ha mu p y hy
  by_cases hb : mu < 0 ∧ ∃ j, z.val j = 0
  · rw [CESUtility, ite_eq_left hb]
    exact cesUtility_pos a ha mu hx
  have hzp : mu < 0 → ∀ j, 0 < z.val j := by
    intro hm j
    exact lt_of_le_of_ne (z.property j) (fun he => hb ⟨hm, j, he.symm⟩)
  have hs := cesPowerSum_strict_budget a ha hmu hm0 p y hy hz hzp hne
  rw [CESUtility, ite_eq_right hb, cesUtility_of_positive a mu hx]
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · have hsum : CESPowerSum a mu (CESBundle a ha mu p y) < CESPowerSum a mu z := by
      have h := (div_lt_iff_of_neg hm).mp hs
      linarith
    exact Real.rpow_lt_rpow_of_neg (cesPowerSum_pos a ha mu hx) hsum
      (one_div_neg.mpr hm)
  · have hsum : CESPowerSum a mu z < CESPowerSum a mu (CESBundle a ha mu p y) := by
      have h := (div_lt_iff₀ hm).mp hs
      linarith
    exact Real.rpow_lt_rpow (cesPowerSum_nonneg a ha mu z) hsum (one_div_pos.mpr hm)

/-- The CES demand formula is the unique maximizer at positive income. -/
theorem ces_demand_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    MarshallianDemand (CESUtility a mu) p y = {CESBundle a ha mu p y} := by
  have hbudget : CESBundle a ha mu p y ∈ BudgetSet p y :=
    (expenditure_cesBundle a ha mu p y).le
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact not_lt_of_ge (hz.2 _ hbudget)
      (cesUtility_strict_budget a ha hmu hm0 p y hy hz.1 hne)
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst z
    refine ⟨hbudget, fun z hz => ?_⟩
    by_cases he : z = CESBundle a ha mu p y
    · change CESUtility a mu z ≤ CESUtility a mu (CESBundle a ha mu p y)
      exact (congrArg (CESUtility a mu) he).le
    · exact (cesUtility_strict_budget a ha hmu hm0 p y hy hz he).le

/-- At zero income the CES formula gives the origin. -/
theorem cesBundle_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) : CESBundle a ha mu p 0 = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [CESBundle, ZeroBundle]

/-- **Problem 3.7:** the full CES demand correspondence for every nonnegative income. -/
theorem problem_3_7 {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (CESUtility a mu) p y = {CESBundle a ha mu p y} := by
  by_cases hy : 0 < (y : ℝ)
  · exact ces_demand_pos a ha hmu hm0 p y hy
  · have he : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
    subst y
    rw [marshallianDemand_zero, cesBundle_zero]

end Kreps.ConsumerDemand
