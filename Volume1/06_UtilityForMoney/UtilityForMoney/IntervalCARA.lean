/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.IntervalWealthShifts
import UtilityForMoney.CARACalibrationPreferences

/-!
# Constant risk aversion on the original monetary interval

Kreps I, Proposition 6.12 and Problem 6.2, pp. 130–131 and 140–141. The
differential equation is integrated in the interior. Continuity determines
the utility at each included endpoint without using its exterior values.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Two continuous functions agreeing inside a nondegenerate interval agree at its endpoints. -/
theorem eqOn_interval_of_eqOn_interior {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {f g : ℝ → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (he : (interior S).EqOn f g) : S.EqOn f g := by
  intro x hx
  have hcl : x ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have := mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono interior_subset)
    ((hg x hx).mono interior_subset) (Filter.mem_of_superset self_mem_nhdsWithin he)

/-- **Proposition 6.12, relative CARA classification:** constant nonnegative curvature on the
whole interval determines the exponential or affine utility, including its boundary values. -/
theorem cara_representation_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hU : ContDiffOn ℝ 2 U S) (hp : ∀ x ∈ S, 0 < derivWithin U S x)
    (k : ℝ) (hk : ∀ x ∈ S, IntervalRiskAversion S U x = k) :
    (0 < k → ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * ExponentialUtility k x) ∧
      (k = 0 → ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * x) := by
  have hs (x : ℝ) (hx : x ∈ interior S) : ContDiffAt ℝ 2 U x :=
    (hU x (interior_subset hx)).contDiffAt (mem_interior_iff_mem_nhds.mp hx)
  have hd (x : ℝ) (hx : x ∈ interior S) := (hs x hx).differentiableAt (by norm_num)
  have hd' (x : ℝ) (hx : x ∈ interior S) :=
    ((hs x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hp' (x : ℝ) (hx : x ∈ interior S) : 0 < deriv U x := by
    rw [← derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)]
    exact hp x (interior_subset hx)
  have hk' (x : ℝ) (hx : x ∈ interior S) : AbsoluteRiskAversion U x = k := by
    rw [← intervalRiskAversion_eq_of_interior U hx]
    exact hk x (interior_subset hx)
  constructor
  · intro hpos
    obtain ⟨A, B, hB, he⟩ := proposition_6_12_exponential hS.interior hI hd hd' hp' hpos hk'
    refine ⟨A, B, hB, fun x hx => ?_⟩
    apply eqOn_interval_of_eqOn_interior hS hI hU.continuousOn _ (g := fun z =>
      A + B * ExponentialUtility k z) (fun _ hz => he _ hz) hx
    unfold ExponentialUtility
    fun_prop
  · rintro rfl
    obtain ⟨A, B, hB, he⟩ := proposition_6_12_affine hS.interior hI hd hd' hp' hk'
    refine ⟨A, B, hB, fun x hx => ?_⟩
    apply eqOn_interval_of_eqOn_interior hS hI hU.continuousOn _ (g := fun z =>
      A + B * z) (fun _ hz => he _ hz) hx
    fun_prop

/-- **Problem 6.2 on the exact prize interval:** one-sided endpoint smoothness suffices for
the personality and calibrated certainty equivalent to imply the complete ranking. -/
theorem problem_6_2_within {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ConcaveOn ℝ CalibrationInterval U) (hs : ContDiffOn ℝ 2 U CalibrationInterval)
    (hp : ∀ x ∈ CalibrationInterval, 0 < derivWithin U CalibrationInterval x)
    (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  have hI := Set.nonempty_of_mem hz
  obtain ⟨k, hk⟩ := (proposition_6_12_within hc.1 hI hi hs hp).2.2.mp hC
  have hneg := (hc.antitoneOn_derivWithin (hs.differentiableOn (by norm_num))).derivWithin_nonpos
    (x := 0)
  have hnn : 0 ≤ IntervalRiskAversion CalibrationInterval U 0 :=
    div_nonneg (neg_nonneg.mpr hneg) (hp 0 (interior_subset hz)).le
  rw [hk 0 (interior_subset hz)] at hnn
  have hrep := cara_representation_within hc.1 hI hs hp k hk
  rcases hnn.eq_or_lt with hz' | hpos
  · obtain ⟨A, B, hB, h⟩ := hrep.2 hz'.symm
    rw [h 5000 (by norm_num [CalibrationInterval]), h 0 (by norm_num [CalibrationInterval]),
      h 2400 (by norm_num [CalibrationInterval])] at he
    linarith
  · obtain ⟨A, B, hB, h⟩ := hrep.1 hpos
    exact problem_6_2 hB hpos h he

end Kreps.UtilityForMoney
