/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.ConstantAbsoluteRisk
import UtilityForMoney.MonetaryLotteries
import UtilityForMoney.LotterySimpleLottery
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Full coverage with an imperfect fair policy

Kreps I, Problem 6.9, pp. 143–144. Starting wealth is one. No loss occurs with
probability one half. Conditional on loss, the loss is either one or three,
equally likely. Coverage pays their mean, two, and costs one. Full insurance
therefore leaves wealth at zero, one or minus one. A necessary and sufficient
marginal-utility test in this example gives both answers within increasing,
strictly concave differentiable utility.
-/

namespace Kreps.UtilityForMoney

/-- The three loss amounts with the probabilities in the example. -/
noncomputable def ImperfectLoss : SimpleLottery ℝ :=
  LotteryTheory.Mix ⟨1 / 2, by norm_num⟩ (LotteryTheory.PureLottery 0)
    (BinaryLottery 1 3 (1 / 2) (by norm_num))

/-- The expected conditional loss is two, yielding an actuarially fair premium of one. -/
theorem imperfect_policy_fair :
    ExpectedUtility id (BinaryLottery 1 3 (1 / 2) (by norm_num)) = 2 ∧
      (1 / 2 : ℝ) * 2 = 1 := by rw [expectedUtility_binary]; norm_num

/-- Expected utility under coverage `a` for this imperfect but fairly priced indemnity. -/
noncomputable def ImperfectValue (V : ℝ → ℝ) (a : ℝ) : ℝ :=
  (2 * V (1 - a) + V a + V (a - 2)) / 4

/-- The displayed objective is the expected utility of final wealth under the actual loss law. -/
theorem imperfectValue_expectedUtility (V : ℝ → ℝ) (a : ℝ) :
    ExpectedUtility (fun t => V (1 - t + (if t = 0 then 0 else 2 * a) - a)) ImperfectLoss =
      ImperfectValue V a := by
  let g := fun t : ℝ => V (1 - t + (if t = 0 then 0 else 2 * a) - a)
  change LotteryTheory.ExpectedUtility g _ = _
  rw [ImperfectLoss, LotteryTheory.expectedUtility_affine, LotteryTheory.expectedUtility_pure]
  change _ + _ * ExpectedUtility g (BinaryLottery ..) = _
  rw [expectedUtility_binary]
  norm_num [g, ImperfectValue]
  ring_nf

/-- At full coverage only the three marginal utilities at residual wealth enter the derivative. -/
theorem imperfectValue_hasDerivAt (V : ℝ → ℝ) (hd : Differentiable ℝ V) :
    HasDerivAt (ImperfectValue V) ((-2 * deriv V 0 + deriv V 1 + deriv V (-1)) / 4) 1 := by
  have h₀ := (hasDerivAt_id' (1 : ℝ)).const_sub 1
  have h₂ := (hasDerivAt_id' (1 : ℝ)).sub_const 2
  have hd₀ : HasDerivAt V (deriv V 0) (1 - 1) := by simpa using (hd 0).hasDerivAt
  have hd₂ : HasDerivAt V (deriv V (-1)) (1 - 2) := by
    convert (hd (-1)).hasDerivAt using 1
    norm_num
  convert ((((hd₀.comp 1 h₀).const_mul 2).add (hd 1).hasDerivAt).add (hd₂.comp 1 h₂)).div_const 4
    using 1
  · rfl
  · ring

/-- A global concave differentiable function lies below each of its tangent lines. -/
theorem wealth_concave_tangent {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hd : Differentiable ℝ V) (x z : ℝ) : V z - V x ≤ deriv V x * (z - x) := by
  rcases lt_trichotomy x z with hh | rfl | hh
  · have he := hc.slope_le_deriv (Set.mem_univ _) (Set.mem_univ _) hh (hd x)
    rw [slope_def_field] at he
    exact (div_le_iff₀ (sub_pos.mpr hh)).mp he
  · simp
  · have he := hc.deriv_le_slope (Set.mem_univ _) (Set.mem_univ _) hh (hd x)
    rw [slope_def_field] at he
    linarith only [(le_div_iff₀ (sub_pos.mpr hh)).mp he]

/-- Full coverage in this imperfect policy is optimal exactly at the marginal-utility equality. -/
theorem imperfect_full_iff {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hd : Differentiable ℝ V) :
    (∀ a, ImperfectValue V a ≤ ImperfectValue V 1) ↔
      deriv V 1 + deriv V (-1) = 2 * deriv V 0 := by
  constructor
  · intro hm
    have hmax : IsLocalMax (ImperfectValue V) (1 : ℝ) := Filter.Eventually.of_forall hm
    have he := hmax.hasDerivAt_eq_zero (imperfectValue_hasDerivAt V hd)
    linarith
  · intro he a
    obtain h₀ := wealth_concave_tangent hc hd 0 (1 - a)
    obtain h₁ := wealth_concave_tangent hc hd 1 a
    obtain h₂ := wealth_concave_tangent hc hd (-1) (a - 2)
    unfold ImperfectValue
    norm_num
    nlinarith only [h₀, h₁, h₂, he, congrArg (fun q : ℝ => q * a) he]

/-- Smooth utility whose marginal utilities at opposite wealth levels sum to one. -/
noncomputable def BalancedMarginalUtility (x : ℝ) : ℝ := x - Real.log (1 + Real.exp x)

/-- The exact marginal utility, strictly positive and strictly decreasing. -/
theorem balancedMarginal_derivative (x : ℝ) :
    HasDerivAt BalancedMarginalUtility (1 / (1 + Real.exp x)) x := by
  have h := (hasDerivAt_id' x).sub (((Real.hasDerivAt_exp x).const_add 1).log (by positivity))
  convert h using 1
  · rfl
  · field_simp
    ring

/-- This balanced marginal example is strictly increasing and strictly concave on all wealth. -/
theorem balancedMarginal_regular :
    StrictMono BalancedMarginalUtility ∧ StrictConcaveOn ℝ Set.univ BalancedMarginalUtility ∧
      Differentiable ℝ BalancedMarginalUtility := by
  have hd : Differentiable ℝ BalancedMarginalUtility := fun x =>
    (balancedMarginal_derivative x).differentiableAt
  refine ⟨strictMono_of_deriv_pos (fun x => by
    rw [(balancedMarginal_derivative x).deriv]
    positivity),
    StrictAnti.strictConcaveOn_univ_of_deriv hd.continuous ?_, hd⟩
  intro x y hxy
  rw [(balancedMarginal_derivative x).deriv, (balancedMarginal_derivative y).deriv]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith [Real.exp_lt_exp.mpr hxy])

/-- **Problem 6.9:** a genuinely imperfect fair policy can make full coverage optimal. -/
theorem problem_6_9_full : ∀ a, ImperfectValue BalancedMarginalUtility a ≤
    ImperfectValue BalancedMarginalUtility 1 := by
  apply (imperfect_full_iff balancedMarginal_regular.2.1.concaveOn balancedMarginal_regular.2.2).mpr
  rw [(balancedMarginal_derivative 1).deriv, (balancedMarginal_derivative (-1)).deriv,
    (balancedMarginal_derivative 0).deriv, Real.exp_neg, Real.exp_zero]
  field_simp
  ring

/-- **Problem 6.9:** the same imperfect fair policy does not make full coverage optimal for CARA. -/
theorem problem_6_9_not_full :
    ¬∀ a, ImperfectValue (ExponentialUtility 1) a ≤ ImperfectValue (ExponentialUtility 1) 1 := by
  intro hm
  have he := (imperfect_full_iff (exponentialUtility_strictConcave zero_lt_one).concaveOn
    (fun x => (exponentialUtility_hasDerivAt 1 x).differentiableAt)).mp hm
  rw [(exponentialUtility_hasDerivAt 1 1).deriv, (exponentialUtility_hasDerivAt 1 (-1)).deriv,
    (exponentialUtility_hasDerivAt 1 0).deriv] at he
  norm_num at he
  linarith [Real.exp_one_gt_two, Real.exp_pos (-1)]

end Kreps.UtilityForMoney
