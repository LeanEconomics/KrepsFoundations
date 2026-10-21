/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.QuasiLinearIdentification
import PreferenceProperties.TransformationExamples

/-!
# One quasi-linear curve need not identify the whole preference

Kreps I, Problem 2.13, p. 48. On two nonnegative goods, `x + m` and
`max x (2*x - 1) + m` give continuous, strictly monotone, quasi-linear preferences.
Their indifference curves through `(0,1)` agree. Their rankings of `(2,0)` and
`(0,5/2)` differ. The observed goods projection is precisely `[0,1]`.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The piecewise linear transformation is the maximum of its two affine branches. -/
theorem convexWarp_eq_max (t : ℝ) : ConvexWarp t = max t (2 * t - 1) := by
  unfold ConvexWarp
  split_ifs with h
  · exact (max_eq_left (by linarith)).symm
  · exact (max_eq_right (by linarith)).symm

/-- The branches meet continuously at one. -/
theorem convexWarp_continuous : Continuous ConvexWarp := by
  have he : ConvexWarp = fun t : ℝ => max t (2 * t - 1) := funext convexWarp_eq_max
  rw [he]
  exact continuous_id.max ((continuous_const.mul continuous_id).sub continuous_const)

/-- Linear utility in the non-money good and money. -/
def LinearMoneyUtility : (ℝ≥0 × ℝ≥0) → ℝ := QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ))

/-- The marginal value of the first good rises at one, while money's coefficient stays one. -/
noncomputable def WarpedMoneyUtility : (ℝ≥0 × ℝ≥0) → ℝ :=
  QuasiLinearUtility (fun x : ℝ≥0 => ConvexWarp (x : ℝ))

/-- Both utility functions satisfy continuity and strict product-order monotonicity. -/
theorem linear_warped_utilities_regular :
    Continuous LinearMoneyUtility ∧ StrictMono LinearMoneyUtility ∧
      Continuous WarpedMoneyUtility ∧ StrictMono WarpedMoneyUtility := by
  have hcoe : StrictMono (fun x : ℝ≥0 => (x : ℝ)) := fun _ _ h => NNReal.coe_lt_coe.mpr h
  exact ⟨quasiLinearUtility_continuous NNReal.continuous_coe,
    quasiLinearUtility_strictMono hcoe,
    quasiLinearUtility_continuous (convexWarp_continuous.comp NNReal.continuous_coe),
    quasiLinearUtility_strictMono (convexWarp_strictMono.comp hcoe)⟩

/-- The two preferences have exactly the same indifference curve through `(0,1)`. -/
theorem linear_warped_same_curve :
    IndifferenceClass (UtilityPref LinearMoneyUtility) (0, 1) =
      IndifferenceClass (UtilityPref WarpedMoneyUtility) (0, 1) := by
  have hu : Represents LinearMoneyUtility (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  have hv : Represents WarpedMoneyUtility (UtilityPref WarpedMoneyUtility) := fun _ _ => Iff.rfl
  ext q
  change Indifferent (UtilityPref LinearMoneyUtility) q (0, 1) ↔
    Indifferent (UtilityPref WarpedMoneyUtility) q (0, 1)
  rw [indifferent_iff_utility_eq hu, indifferent_iff_utility_eq hv]
  change (q.1 : ℝ) + (q.2 : ℝ) = 0 + 1 ↔
    ConvexWarp (q.1 : ℝ) + (q.2 : ℝ) = ConvexWarp 0 + 1
  have hv0 : ConvexWarp 0 = 0 := by norm_num [ConvexWarp]
  rw [hv0, zero_add]
  have hm : 0 ≤ (q.2 : ℝ) := q.2.property
  constructor
  · intro h
    have hx : (q.1 : ℝ) ≤ 1 := by linarith
    simpa only [ConvexWarp, ite_eq_left hx] using h
  · intro h
    have hg : (q.1 : ℝ) ≤ ConvexWarp (q.1 : ℝ) := by
      rw [convexWarp_eq_max]
      exact le_max_left _ _
    have hx : (q.1 : ℝ) ≤ 1 := by linarith
    simpa only [ConvexWarp, ite_eq_left hx] using h

/-- The observed goods range ends at one because money cannot be negative. -/
theorem linear_curve_goods :
    CurveGoods (UtilityPref LinearMoneyUtility) (0, 1) = Set.Iic (1 : ℝ≥0) := by
  have hu : Represents (QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ)))
      (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  ext x
  rw [curveGoods_iff_subutility_le hu]
  change (x : ℝ) ≤ (0 : ℝ) + 1 ↔ x ≤ 1
  simpa only [zero_add, NNReal.coe_one] using
    (show (x : ℝ) ≤ ((1 : ℝ≥0) : ℝ) ↔ x ≤ 1 from NNReal.coe_le_coe)

/-- **Problem 2.13:** even continuous, strictly monotone quasi-linear preferences
can share a nonzero indifference curve and disagree on other comparisons. -/
theorem problem_2_13_quasiLinear_nonidentification :
    ∃ r s : (ℝ≥0 × ℝ≥0) → (ℝ≥0 × ℝ≥0) → Prop,
      Rational r ∧ Rational s ∧ ContinuousPreference r ∧ ContinuousPreference s ∧
      StrictlyMonotonePreference r ∧ StrictlyMonotonePreference s ∧
      QuasiLinear r ∧ QuasiLinear s ∧ IndifferenceClass r (0, 1) = IndifferenceClass s (0, 1) ∧
      ¬r (2, 0) (0, 5 / 2) ∧ s (2, 0) (0, 5 / 2) := by
  have hu : Represents LinearMoneyUtility (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  have hv : Represents WarpedMoneyUtility (UtilityPref WarpedMoneyUtility) := fun _ _ => Iff.rfl
  obtain ⟨huc, hum, hvc, hvm⟩ := linear_warped_utilities_regular
  refine ⟨UtilityPref LinearMoneyUtility, UtilityPref WarpedMoneyUtility,
    proposition_1_3a _, proposition_1_3a _, proposition_2_9_forward hu huc,
    proposition_2_9_forward hv hvc, (proposition_2_2_strict hu).mpr hum,
    (proposition_2_2_strict hv).mpr hvm, ⟨_, hu⟩, ⟨_, hv⟩, linear_warped_same_curve, ?_, ?_⟩
  · norm_num [UtilityPref, LinearMoneyUtility, QuasiLinearUtility]
  · norm_num [UtilityPref, WarpedMoneyUtility, QuasiLinearUtility, ConvexWarp]

end Kreps.PreferenceProperties
