/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CESDemand
import ConsumerDemand.CobbDouglasDemand
import ConsumerDemand.LinearDemand

/-!
# The linear and Cobb-Douglas limits of CES demand

Kreps I, Problem 3.7, pp. 64-65. At exponent one the entire linear-demand
face is retained, including ties. As the exponent approaches zero, the unique
CES demand converges to Cobb-Douglas expenditure shares. No normalization of
the positive coefficients is needed for this demand limit; a literal finite
limit of the unnormalized utility itself would need additional normalization.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal Topology
open Filter

/-- At exponent one CES utility is exactly linear utility, including on the boundary. -/
theorem cesUtility_one {k : ℕ} (a : Fin k → ℝ) : CESUtility a 1 = LinearUtility a := by
  funext x
  simp [CESUtility, CESPowerSum, LinearUtility]

/-- **Problem 3.7, exponent one:** all spending goes to goods with maximal utility-price ratio. -/
theorem problem_3_7_one {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand (CESUtility a 1) p y ↔
      Expenditure p x = (y : ℝ) ∧
        ∀ i, 0 < x.val i → ∀ j, a j / p.val j ≤ a i / p.val i := by
  rw [cesUtility_one]
  exact problem_3_6a a ha p y x

/-- The CES price-adjusted weights vary continuously with the exponent at zero. -/
theorem cesWeight_continuousAt_zero {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (j : Fin k) : ContinuousAt (fun mu => CESWeight a mu p j) 0 := by
  unfold CESWeight
  apply (Real.continuousAt_const_rpow (div_pos (ha j) (p.property j)).ne').comp
  exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)

/-- At exponent zero, the denominator of the demand formula is the sum of coefficients. -/
theorem cesDenominator_zero {k : ℕ} (a : Fin k → ℝ) (p : PositivePrices k) :
    CESDenominator a 0 p = ∑ j, a j := by
  unfold CESDenominator CESWeight
  simp only [sub_zero, div_one, Real.rpow_one]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(p.property j).ne']

/-- The CES denominator is continuous in the exponent at zero. -/
theorem cesDenominator_continuousAt_zero {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) :
    ContinuousAt (fun mu => CESDenominator a mu p) 0 := by
  have hw := cesWeight_continuousAt_zero a ha p
  unfold CESDenominator
  fun_prop

/-- The continuous extension of the CES demand formula at zero is the Cobb-Douglas formula. -/
theorem cesBundle_at_zero_exponent {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    CESBundle a ha 0 p y = CobbDouglasBundle a ha p y := by
  apply Subtype.ext
  funext j
  simp only [CESBundle, CESWeight, cesDenominator_zero, CobbDouglasBundle,
    sub_zero, div_one, Real.rpow_one]
  ring

/-- **Problem 3.7, zero limit:** the actual CES demand quantities converge to Cobb-Douglas. -/
theorem problem_3_7_zero_limit {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Tendsto (fun mu => (CESBundle a ha mu p y).val) (𝓝 0)
      (𝓝 (CobbDouglasBundle a ha p y).val) := by
  rw [← cesBundle_at_zero_exponent a ha p y]
  apply tendsto_pi_nhds.mpr
  intro j
  apply ContinuousAt.tendsto
  exact (continuousAt_const.div (cesDenominator_continuousAt_zero a ha p)
    (cesDenominator_pos a ha 0 p).ne').mul (cesWeight_continuousAt_zero a ha p j)

/-- The limit also holds along precisely the admissible nonzero CES exponents below one. -/
theorem cesDemand_tendsto_cobbDouglas {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Tendsto (fun mu => (CESBundle a ha mu p y).val)
      (𝓝[{mu : ℝ | mu < 1 ∧ mu ≠ 0}] 0) (𝓝 (CobbDouglasBundle a ha p y).val) :=
  (problem_3_7_zero_limit a ha p y).mono_left nhdsWithin_le_nhds

end Kreps.ConsumerDemand
