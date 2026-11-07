/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.TimingExamples
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified numerical optimum values for precommitted consumption

Kreps I, Problem 6.7, pp. 142–143. Combine logarithms into the log of a positive
product. Rescale each product by a power of two and apply the fourth-order
logarithm remainder bound and Mathlib's rational bounds on log two. The
three-state product is enclosed throughout the proven narrow optimizer interval.
-/

namespace Kreps.UtilityForMoney

/-- At feasible positive consumptions, combine the statewise logs into one product. -/
theorem timingValue_eq_log_product {n : ℕ} (N : Fin n → ℝ) {w : ℝ} (hw : w ∈ TimingMenu N) :
    TimingValue N w = Real.log (w ^ n * ∏ i, (N i - w)) / n := by
  have hp : 0 < w := zero_lt_one.trans_le hw.1
  have hpos (i) : 0 < N i - w := by linarith [hw.2 i]
  rw [TimingValue, Real.log_mul (pow_ne_zero _ hp.ne') (Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hpos i).ne')), Real.log_pow, Real.log_prod (fun i _ => (hpos i).ne')]

/-- Rescaling a logarithm by a power of two gives an explicit finite Taylor error certificate. -/
theorem timing_log_certificate (k : ℕ) (p : ℝ) (hp : 0 < p)
    (h : |1 - p / 2 ^ k| < 1) :
    |(∑ i ∈ Finset.range 4, (1 - p / 2 ^ k) ^ (i + 1) / (i + 1)) +
      (Real.log p - (k : ℝ) * Real.log 2)| ≤ |1 - p / 2 ^ k| ^ 5 / (1 - |1 - p / 2 ^ k|) := by
  have he := Real.abs_log_sub_add_sum_range_le h 4
  rwa [sub_sub_cancel, Real.log_div hp.ne' (by positivity), Real.log_pow] at he

/-- Binary-income optimum utility rounds to 8.3325 to four places. -/
theorem timing_two_value_bounds :
    8.33252 < TimingValue TimingTwo 60 ∧ TimingValue TimingTwo 60 < 8.33254 := by
  rw [timingValue_eq_log_product TimingTwo timing_two_optimum.1]
  norm_num [TimingTwo, Fin.prod_univ_two]
  have he := timing_log_certificate 24 17280000 (by norm_num) (by norm_num)
  rw [abs_le] at he
  norm_num [Finset.sum_range_succ] at he
  constructor <;> linarith [he.1, he.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Certain-income optimum utility also rounds to 8.3325 to four places. -/
theorem timing_sure_value_bounds :
    8.33252 < TimingValue TimingSure 64.4741959095 ∧
      TimingValue TimingSure 64.4741959095 < 8.33254 := by
  rw [timingValue_eq_log_product TimingSure timing_sure_optimum.1]
  have he := timing_log_certificate 12 (64.4741959095 ^ 2) (by norm_num) (by norm_num)
  rw [abs_le] at he
  norm_num [Finset.sum_range_succ] at he
  norm_num [TimingSure, Fin.prod_univ_one]
  constructor <;> linarith [he.1, he.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The three-state log-product lies within these rational bounds throughout the root bracket. -/
theorem timing_three_product_bounds {w : ℝ}
    (hw : w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610) :
    71581699040 ≤ w ^ 3 * ∏ i, (TimingThree i - w) ∧
      w ^ 3 * ∏ i, (TimingThree i - w) ≤ 71581699060 := by
  let L : ℝ := 61.2389938609
  let H : ℝ := 61.2389938610
  have hlo : L ≤ w := hw.1
  have hhi : w ≤ H := hw.2
  have hpos : 0 ≤ w := by linarith [hw.1]
  have h₁ : 0 ≤ 100 - w := by linarith [hw.2]
  have h₂ : 0 ≤ 180 - w := by linarith [hw.2]
  have h₃ : 0 ≤ 128.948391819 - w := by linarith [hw.2]
  have h₄ := mul_nonneg (mul_nonneg h₁ h₂) h₃
  simp only [Fin.prod_univ_three, TimingThree, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  constructor
  · calc
      71581699040 ≤ L ^ 3 * ((100 - H) * (180 - H) * (128.948391819 - H)) := by norm_num [L, H]
      _ ≤ _ := by gcongr
  · calc
      _ ≤ H ^ 3 * ((100 - L) * (180 - L) * (128.948391819 - L)) := by
        gcongr
      _ ≤ 71581699060 := by norm_num [L, H]

/-- The maximal three-state utility rounds to 8.3314 to four places. -/
theorem timing_three_value_bounds {w : ℝ}
    (hw : w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610) (hm : w ∈ TimingMenu TimingThree) :
    8.33136 < TimingValue TimingThree w ∧ TimingValue TimingThree w < 8.33138 := by
  obtain ⟨hl, hu⟩ := timing_three_product_bounds hw
  have hL := timing_log_certificate 36 71581699040 (by norm_num) (by norm_num)
  have hU := timing_log_certificate 36 71581699060 (by norm_num) (by norm_num)
  rw [abs_le] at hL hU
  norm_num [Finset.sum_range_succ] at hL hU
  rw [timingValue_eq_log_product TimingThree hm]
  norm_num only [Nat.cast_ofNat]
  have hlogL := Real.log_le_log (by norm_num : (0 : ℝ) < 71581699040) hl
  have hlogU := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 71581699040) hl) hu
  constructor <;> linarith [hL.1, hU.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

end Kreps.UtilityForMoney
