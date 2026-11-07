/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CARACalibration

/-!
# Behavioral calibration and attainability of Problem 6.2

Kreps I, Problem 6.2, pp. 140–141. Preferences with constant absolute risk
aversion on the stated prize interval select B, then C, then A. Concavity
forces a nonnegative coefficient, and the reported certainty equivalent excludes
the affine risk-neutral case. A positive exponential coefficient satisfying the
reported indifference exists.
-/

namespace Kreps.UtilityForMoney

/-- The range on which the consumer reports constant absolute risk aversion. -/
def CalibrationInterval : Set ℝ := Set.Icc (-1000) 5000

/-- **Problem 6.2 from primitive utility properties:** classification of CARA preferences
and the certainly-equivalent dollar amount imply the strict ranking of the three offers. -/
theorem problem_6_2_behavioral {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ConcaveOn ℝ CalibrationInterval U) (hs : ∀ x ∈ CalibrationInterval, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ CalibrationInterval, 0 < deriv U x)
    (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  have h₁ (x : ℝ) (hx : x ∈ CalibrationInterval) := (hs x hx).differentiableAt (by norm_num)
  have h₂ (x : ℝ) (hx : x ∈ CalibrationInterval) :=
    ((hs x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one
  obtain ⟨k, hk⟩ := (proposition_6_12_constant (convex_Icc _ _) ⟨0, hz⟩ hi hs hp).mp hC
  have hneg := (hc.antitoneOn_deriv h₁).derivWithin_nonpos (x := 0)
  rw [derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)] at hneg
  have hnonneg := absoluteRiskAversion_nonneg (hp 0 (interior_subset hz)) hneg
  rw [hk 0 (interior_subset hz)] at hnonneg
  rcases hnonneg.eq_or_lt with hzero | hpos
  · subst k
    obtain ⟨A, B, hB, hrep⟩ := proposition_6_12_affine hc.1 ⟨0, interior_subset hz⟩ h₁ h₂ hp hk
    rw [hrep 5000 (by norm_num [CalibrationInterval]), hrep 0 (by norm_num [CalibrationInterval]),
      hrep 2400 (by norm_num [CalibrationInterval])] at he
    linarith
  · obtain ⟨A, B, hB, hrep⟩ :=
      proposition_6_12_exponential hc.1 ⟨0, interior_subset hz⟩ h₁ h₂ hp hpos hk
    exact problem_6_2 hB hpos hrep he

/-- Some strictly risk-averse exponential consumer actually reports the specified certainty
equivalent and makes the predicted choices. -/
theorem problem_6_2_compatible_consumer :
    ∃ k > 0, ConstantRiskAversion CalibrationInterval (ExponentialUtility k) ∧
      ((ExponentialUtility k 5000 + ExponentialUtility k 0) / 2 = ExponentialUtility k 2400) ∧
      CalibratedChoicesRanked (ExponentialUtility k) := by
  obtain ⟨q, hq, hcal⟩ := calibrated_root_exists
  let k := -(Real.log q) / 200
  have hk : 0 < k := div_pos (neg_pos.mpr (Real.log_neg hq.1 hq.2)) (by norm_num)
  have heq : Real.exp (-200 * k) = q := by
    rw [show -200 * k = Real.log q by dsimp [k]; ring, Real.exp_log hq.1]
  obtain ⟨h0, _, _, h24, h5, _⟩ := exponential_calibration_prizes k
  have he : (ExponentialUtility k 5000 + ExponentialUtility k 0) / 2 =
      ExponentialUtility k 2400 := by
    rw [h5, h24, h0, heq]
    linarith
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  refine ⟨k, hk, ?_, he, ?_⟩
  · apply (proposition_6_12_constant (convex_Icc _ _) ⟨0, hz⟩
      ((exponentialUtility_strictMono hk).strictMonoOn CalibrationInterval)
      (fun x _ => by unfold ExponentialUtility; fun_prop)
      (fun x _ => by rw [(exponentialUtility_hasDerivAt k x).deriv]; positivity)).mpr
    exact ⟨k, fun x _ => absoluteRiskAversion_exponential hk.ne' x⟩
  · apply problem_6_2 (A := 0) (B := 1) zero_lt_one hk _ he
    exact fun x _ => by simp

end Kreps.UtilityForMoney
