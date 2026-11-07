/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.WealthRiskClassification
import UtilityForMoney.ConstantAbsoluteRisk
import Mathlib.Algebra.Field.GeomSum

/-!
# The numerical CARA calibration of Problem 6.2

Kreps I, pp. 140–141. Writing `q = exp (-200 * k)` turns the $2,400
certainty-equivalent restriction into a polynomial equation. Removing its
extraneous risk-neutral root yields a monotone comparison of geometric sums.
The numerical brackets and all three choice comparisons use exact rationals.
-/

namespace Kreps.UtilityForMoney

/-- A monotone rescaling of the calibration polynomial on the positive unit interval. -/
noncomputable def CalibrationGap (q : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 13, q ^ i) - q⁻¹ * ∑ i ∈ Finset.range 12, q⁻¹ ^ i

/-- The rescaled expression has the same zero as the indifference equation for positive risk. -/
theorem calibrationGap_identity {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    q ^ 12 * (1 - q) * CalibrationGap q = 2 * q ^ 12 - 1 - q ^ 25 := by
  have hi : 1 < q⁻¹ := (one_lt_inv₀ hq.1).mpr hq.2
  rw [CalibrationGap, geom_sum_eq hq.2.ne, geom_sum_eq hi.ne']
  field_simp [hq.1.ne', sub_ne_zero.mpr hq.2.ne, sub_ne_zero.mpr hi.ne']
  field_simp [sub_ne_zero.mpr hq.2.ne']
  ring

/-- Monotonicity of the rescaling follows from opposite movements of two geometric sums. -/
theorem calibrationGap_monotone : MonotoneOn CalibrationGap (Set.Ioi 0) := by
  intro a ha b hb hab
  have hi : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab
  have hp (n : ℕ) : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha.le hab n
  have hq (n : ℕ) : b⁻¹ ^ n ≤ a⁻¹ ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hi n
  apply sub_le_sub (Finset.sum_le_sum fun i _ => hp i)
  apply mul_le_mul hi (Finset.sum_le_sum fun i _ => hq i)
  · exact Finset.sum_nonneg fun _ _ => pow_nonneg (inv_nonneg.mpr hb.le) _
  · exact inv_nonneg.mpr ha.le

/-- Exact rational bounds isolate every positive-risk solution of the calibration equation. -/
theorem calibration_bounds {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (he : 2 * q ^ 12 = 1 + q ^ 25) : (9936/10000 : ℝ) < q ∧ q < (9937/10000 : ℝ) := by
  have hgap : CalibrationGap q = 0 := by
    have h := calibrationGap_identity hq
    rw [he] at h
    have hp : 0 < q ^ 12 * (1 - q) := mul_pos (pow_pos hq.1 _) (sub_pos.mpr hq.2)
    have hz : q ^ 12 * (1 - q) * CalibrationGap q = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hp.ne'
  have hlo : CalibrationGap (9936/10000) < 0 := by norm_num [CalibrationGap, Finset.sum_range_succ]
  have hhi : 0 < CalibrationGap (9937/10000) := by norm_num [CalibrationGap, Finset.sum_range_succ]
  constructor
  · by_contra! h
    have hh := calibrationGap_monotone hq.1 (by norm_num : (9936/10000 : ℝ) ∈ Set.Ioi 0) h
    linarith
  · by_contra! h
    have hh := calibrationGap_monotone (by norm_num : (9937/10000 : ℝ) ∈ Set.Ioi 0) hq.1 h
    linarith

/-- The calibration is attainable for a strictly positive coefficient. -/
theorem calibrated_root_exists :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, 2 * q ^ 12 = 1 + q ^ 25 := by
  let f := fun t : ℝ => 2 * t ^ 12 - 1 - t ^ 25
  have hc : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨q, hq, he⟩ := intermediate_value_Icc (f := f)
    (show (9936/10000 : ℝ) ≤ 9937/10000 by norm_num) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f (9936/10000)) (f (9937/10000)) by constructor <;> norm_num [f])
  exact ⟨q, ⟨lt_of_lt_of_le (by norm_num) hq.1, lt_of_le_of_lt hq.2 (by norm_num)⟩, by
    dsimp [f] at he
    linarith⟩

/-- At any calibrated coefficient alternative B has the lowest disutility, followed by C and A. -/
theorem calibrated_disutility_rankings {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (he : 2 * q ^ 12 = 1 + q ^ 25) :
    3/5 * q ^ 25 + 2/5 / q ^ 5 < 2/5 * q ^ 25 + 3/10 + 3/10 * q ^ 5 ∧
      2/5 * q ^ 25 + 3/10 + 3/10 * q ^ 5 < q ^ 10 := by
  obtain ⟨hl, hh⟩ := calibration_bounds hq he
  have hlo (n : ℕ) := pow_le_pow_left₀ (by norm_num : 0 ≤ (9936/10000 : ℝ)) hl.le n
  have hhi (n : ℕ) := pow_le_pow_left₀ hq.1.le hh.le n
  have hinv := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2/5)
    (show 0 < (9936 / 10000 : ℝ) ^ 5 by norm_num) (hlo 5))
  constructor
  · linarith [hlo 25, hlo 5, hhi 25, hinv]
  · linarith [hhi 25, hhi 5, hlo 10]

/-- Utility of the three alternatives as actually offered, including the negative prize. -/
def CalibratedChoicesRanked (U : ℝ → ℝ) : Prop :=
  U 2000 < 2/5 * U 5000 + 3/10 * U 0 + 3/10 * U 1000 ∧
    2/5 * U 5000 + 3/10 * U 0 + 3/10 * U 1000 < 3/5 * U 5000 + 2/5 * U (-1000)

/-- Exponential disutilities at all five prizes are integer powers of the $200 discount factor. -/
theorem exponential_calibration_prizes (k : ℝ) :
    let q := Real.exp (-200 * k)
    ExponentialUtility k 0 = -1 ∧ ExponentialUtility k 1000 = -q ^ 5 ∧
      ExponentialUtility k 2000 = -q ^ 10 ∧ ExponentialUtility k 2400 = -q ^ 12 ∧
      ExponentialUtility k 5000 = -q ^ 25 ∧ ExponentialUtility k (-1000) = -(q ^ 5)⁻¹ := by
  dsimp only
  have hex (n : ℕ) : Real.exp (-k * (200 * (n : ℝ))) = Real.exp (-200 * k) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold ExponentialUtility
  norm_num at *
  have h5 := hex 5
  have h10 := hex 10
  have h12 := hex 12
  have h25 := hex 25
  norm_num at h5 h10 h12 h25
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [← h5, ← Real.exp_neg]
  congr 2
  ring

/-- **Problem 6.2:** positive affine rescalings of the calibrated exponential utility rank
the risky $5,000/$−1,000 alternative above C, and C above $2,000 for certain. -/
theorem problem_6_2 {U : ℝ → ℝ} {A B k : ℝ} (hB : 0 < B) (hk : 0 < k)
    (hU : ∀ x ∈ Set.Icc (-1000 : ℝ) 5000, U x = A + B * ExponentialUtility k x)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  let q := Real.exp (-200 * k)
  have hq : q ∈ Set.Ioo 0 1 := ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  obtain ⟨h0, h1, h2, h24, h5, hn⟩ := exponential_calibration_prizes k
  change ExponentialUtility k 2400 = -q ^ 12 at h24
  change ExponentialUtility k 5000 = -q ^ 25 at h5
  have hcal : 2 * q ^ 12 = 1 + q ^ 25 := by
    rw [hU 5000 (by norm_num), hU 0 (by norm_num), hU 2400 (by norm_num), h5, h0, h24] at he
    apply (mul_right_injective₀ hB.ne')
    linarith
  have hr := calibrated_disutility_rankings hq hcal
  unfold CalibratedChoicesRanked
  rw [hU 2000 (by norm_num), hU 5000 (by norm_num), hU 0 (by norm_num),
    hU 1000 (by norm_num), hU (-1000) (by norm_num), h2, h5, h0, h1, hn]
  change ExponentialUtility k 2000 = -q ^ 10 at h2
  change ExponentialUtility k 1000 = -q ^ 5 at h1
  change ExponentialUtility k (-1000) = -(q ^ 5)⁻¹ at hn
  dsimp only [q] at hr ⊢
  simp only [div_eq_mul_inv] at hr ⊢
  constructor <;> nlinarith [mul_pos hB (sub_pos.mpr hr.1), mul_pos hB (sub_pos.mpr hr.2)]

end Kreps.UtilityForMoney
