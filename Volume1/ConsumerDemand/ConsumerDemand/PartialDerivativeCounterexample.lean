/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import ConsumerDemand.CappedAbsoluteDerivatives

/-!
# Coordinate partial derivatives do not imply common multipliers

Kreps I, Problem 3.13, p. 65, asks for necessary conditions when continuous
utility has one-sided coordinate derivatives. This constructed example shows
why those derivatives cannot simply replace a multivariate derivative in the
usual common-multiplier conditions. The source does not assert that replacement.
At its unique optimum both ordinary coordinate derivatives exist, but the
derivative along a budget-preserving exchange is not their linear combination.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- A continuous piecewise linear utility with incompatible coordinate marginal ratios. -/
def PartialDerivativeUtility (z : Fin 2 → ℝ) : ℝ :=
  z 0 + 2 * z 1 - 2 * min |z 0 - 1| |z 1 - 1|

/-- The strictly positive unit prices for the coordinate-derivative example. -/
def PartialDerivativePrices : PositivePrices 2 := ⟨![1, 1], by intro j; fin_cases j <;> norm_num⟩

/-- The candidate with one unit of each good. -/
def PartialDerivativeBundle : NonnegativeOrthant 2 :=
  ⟨![1, 1], by intro j; fin_cases j <;> norm_num⟩

/-- The counterexample utility is continuous on the whole ambient commodity space. -/
theorem partialDerivativeUtility_continuous : Continuous PartialDerivativeUtility := by
  unfold PartialDerivativeUtility
  fun_prop

/-- Every coordinate slice has finite left and right derivatives at every ambient point. -/
theorem partialDerivativeUtility_one_sided (x : Fin 2 → ℝ) (j : Fin 2) :
    DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
        (Iic (x j)) (x j) ∧
      DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
        (Ici (x j)) (x j) := by
  have hl (A B c t : ℝ) :
      DifferentiableWithinAt ℝ (fun r => A * r + B - 2 * min |r - 1| c) (Iic t) t ∧
        DifferentiableWithinAt ℝ (fun r => A * r + B - 2 * min |r - 1| c) (Ici t) t := by
    have hlin : Differentiable ℝ (fun r : ℝ => A * r + B) := by fun_prop
    exact ⟨hlin.differentiableAt.differentiableWithinAt.sub
      ((cappedAbs_one_sided 1 c t).1.const_mul 2),
      hlin.differentiableAt.differentiableWithinAt.sub
        ((cappedAbs_one_sided 1 c t).2.const_mul 2)⟩
  fin_cases j
  · convert! hl 1 (2 * x 1) |x 1 - 1| (x 0) using 1 <;>
      simp [PartialDerivativeUtility]
  · convert! hl 2 (x 0) |x 0 - 1| (x 1) using 1 <;>
      simp [PartialDerivativeUtility, min_comm, add_comm]

/-- The candidate exhausts income two and gives utility three. -/
theorem partialDerivativeBundle_values :
    Expenditure PartialDerivativePrices PartialDerivativeBundle = 2 ∧
      PartialDerivativeUtility PartialDerivativeBundle.val = 3 := by
  norm_num [Expenditure, PartialDerivativePrices, PartialDerivativeBundle,
    PartialDerivativeUtility, Fin.sum_univ_two]

/-- Every affordable bundle has utility at most three, with equality only at the candidate. -/
theorem partialDerivativeUtility_budget_bound {z : NonnegativeOrthant 2}
    (hz : z ∈ BudgetSet PartialDerivativePrices 2) :
    PartialDerivativeUtility z.val ≤ 3 ∧
      (3 ≤ PartialDerivativeUtility z.val → z = PartialDerivativeBundle) := by
  have hb : z.val 0 + z.val 1 ≤ 2 := by
    simpa [BudgetSet, Expenditure, PartialDerivativePrices, Fin.sum_univ_two] using hz
  have hm : 0 ≤ min |z.val 0 - 1| |z.val 1 - 1| :=
    le_min (abs_nonneg _) (abs_nonneg _)
  by_cases h1 : z.val 1 ≤ 1
  · constructor
    · unfold PartialDerivativeUtility
      linarith
    · intro hu
      have he1 : z.val 1 = 1 := by unfold PartialDerivativeUtility at hu; linarith
      have he0 : z.val 0 = 1 := by
        simp only [PartialDerivativeUtility, he1, sub_self, abs_zero,
          min_eq_right (abs_nonneg (z.val 0 - 1))] at hu
        linarith
      apply Subtype.ext
      funext j
      fin_cases j
      · simpa [PartialDerivativeBundle] using he0
      · simpa [PartialDerivativeBundle] using he1
  · have h1' : 1 < z.val 1 := lt_of_not_ge h1
    have h0 : z.val 0 < 1 := by linarith
    have hmin : min |z.val 0 - 1| |z.val 1 - 1| = z.val 1 - 1 := by
      rw [abs_of_neg (sub_neg.mpr h0), abs_of_pos (sub_pos.mpr h1')]
      apply min_eq_right
      linarith
    have hu : PartialDerivativeUtility z.val < 3 := by
      rw [PartialDerivativeUtility, hmin]
      linarith
    exact ⟨hu.le, fun hh => (not_lt_of_ge hh hu).elim⟩

/-- The example has the displayed unique global demand on the entire nonnegative budget. -/
theorem partialDerivativeUtility_demand :
    MarshallianDemand (fun x => PartialDerivativeUtility x.val) PartialDerivativePrices 2 =
      {PartialDerivativeBundle} := by
  have hf : PartialDerivativeBundle ∈ BudgetSet PartialDerivativePrices 2 :=
    partialDerivativeBundle_values.1.le
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    apply (partialDerivativeUtility_budget_bound hz.1).2
    have h := hz.2 PartialDerivativeBundle hf
    simpa only [UtilityPref, partialDerivativeBundle_values.2] using h
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst z
    refine ⟨hf, fun z hz => ?_⟩
    change PartialDerivativeUtility z.val ≤ PartialDerivativeUtility PartialDerivativeBundle.val
    rw [partialDerivativeBundle_values.2]
    exact (partialDerivativeUtility_budget_bound hz).1

/-- At the optimum the first coordinate slice is the affine function with slope one. -/
theorem partialDerivativeUtility_first_slice (t : ℝ) :
    PartialDerivativeUtility (Function.update PartialDerivativeBundle.val 0 t) = t + 2 := by
  simp [PartialDerivativeUtility, PartialDerivativeBundle]

/-- At the optimum the second coordinate slice is the affine function with slope two. -/
theorem partialDerivativeUtility_second_slice (t : ℝ) :
    PartialDerivativeUtility (Function.update PartialDerivativeBundle.val 1 t) = 1 + 2 * t := by
  simp [PartialDerivativeUtility, PartialDerivativeBundle]

/-- Both ordinary coordinate derivatives exist at the optimum and equal one and two. -/
theorem partialDerivativeUtility_partials (j : Fin 2) :
    HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val j t)) (![1, 2] j) 1 := by
  fin_cases j
  · change HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val 0 t)) 1 1
    convert (hasDerivAt_id (1 : ℝ)).add_const 2 using 1
    funext t
    exact partialDerivativeUtility_first_slice t
  · change HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val 1 t)) 2 1
    convert ((hasDerivAt_id (1 : ℝ)).const_mul 2).const_add 1 using 1
    · funext t
      exact partialDerivativeUtility_second_slice t
    · norm_num

/-- The actual coordinate derivatives cannot satisfy the common-multiplier conditions. -/
theorem partialDerivativeUtility_no_common_multiplier :
    ¬CombinedOptimality PartialDerivativePrices 2 PartialDerivativeBundle ![1, 2] := by
  rintro ⟨_, l, _, _, heq, _⟩
  have h0 := heq 0 (by norm_num [PartialDerivativeBundle])
  have h1 := heq 1 (by norm_num [PartialDerivativeBundle])
  norm_num [PartialDerivativePrices] at h0 h1
  linarith

/-- On a budget-preserving exchange the utility has a kink invisible to the partials. -/
theorem partialDerivativeUtility_exchange (t : ℝ) :
    PartialDerivativeUtility ![1 - t, 1 + t] = 3 + t - 2 * |t| := by
  have h0 : 1 - t - 1 = -t := by ring
  have h1 : 1 + t - 1 = t := by ring
  simp only [PartialDerivativeUtility, Matrix.cons_val_zero, Matrix.cons_val_one,
    h0, h1, abs_neg, min_self]
  ring

/-- The right exchange derivative is minus one, rather than the partial-based prediction one. -/
theorem partialDerivativeUtility_exchange_right :
    HasDerivWithinAt (fun t => PartialDerivativeUtility ![1 - t, 1 + t]) (-1) (Ici 0) 0 := by
  have hd : HasDerivWithinAt (fun t : ℝ => 3 - t) (-1) (Ici 0) 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (3 : ℝ)).sub (hasDerivAt_id 0)).hasDerivWithinAt using 1
    norm_num
  apply hd.congr_of_mem _ (by simp)
  intro t ht
  rw [partialDerivativeUtility_exchange, abs_of_nonneg ht]
  ring

/-- **Problem 3.13 limitation:** its primitive regularity does not imply common multipliers
formed from the coordinate derivatives, even at a unique interior optimum. -/
theorem problem_3_13_coordinate_multiplier_limitation :
    Continuous PartialDerivativeUtility ∧
      (∀ x : Fin 2 → ℝ, ∀ j : Fin 2,
        DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
            (Iic (x j)) (x j) ∧
          DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
            (Ici (x j)) (x j)) ∧
      MarshallianDemand (fun x => PartialDerivativeUtility x.val) PartialDerivativePrices 2 =
        {PartialDerivativeBundle} ∧
      (∀ j : Fin 2, HasDerivAt (fun t => PartialDerivativeUtility
        (Function.update PartialDerivativeBundle.val j t)) (![1, 2] j) 1) ∧
      ¬CombinedOptimality PartialDerivativePrices 2 PartialDerivativeBundle ![1, 2] :=
  ⟨partialDerivativeUtility_continuous, partialDerivativeUtility_one_sided,
    partialDerivativeUtility_demand, partialDerivativeUtility_partials,
    partialDerivativeUtility_no_common_multiplier⟩

end Kreps.ConsumerDemand
