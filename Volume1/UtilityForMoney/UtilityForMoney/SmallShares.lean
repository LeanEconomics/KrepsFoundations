/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CARAPortfolio
import UtilityForMoney.PriceRiskExamples
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Buying a small share of a favorable gamble

Kreps I, Problem 6.13, pp. 145–146. The first-order gain is the expected product
of statewise marginal utility and net payoff. It factors at fixed wealth or
under independence. A kink at initial wealth and dependence on background
wealth can each reverse the comparison.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Expected utility of adding a fractional net gain to possibly random initial wealth. -/
noncomputable def ShareValue {I : Type*} (V : ℝ → ℝ) (p : SimpleLottery I)
    (w g : I → ℝ) (a : ℝ) : ℝ := ExpectedUtility (fun i => V (w i + a * g i)) p

/-- The marginal value is the expectation of marginal utility times the net gain. -/
theorem shareValue_hasDerivAt_zero {I : Type*} (V : ℝ → ℝ) (p : SimpleLottery I)
    (w g : I → ℝ) (hd : ∀ i, DifferentiableAt ℝ V (w i)) :
    HasDerivAt (ShareValue V p w g) (ExpectedUtility (fun i => deriv V (w i) * g i) p) 0 := by
  unfold ShareValue ExpectedUtility Finsupp.sum
  apply HasDerivAt.fun_sum
  intro i _
  have hw : HasDerivAt (fun a : ℝ => w i + a * g i) (g i) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const (g i)).const_add (w i))
  have hv : HasDerivAt V (deriv V (w i)) (w i + 0 * g i) := by simpa using (hd i).hasDerivAt
  exact ((hv.comp 0 hw).const_mul (p.weights i))

/-- **Problem 6.13(a):** at fixed wealth every sufficiently small positive share is desirable. -/
theorem problem_6_13a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    (p : SimpleLottery ℝ) (w b : ℝ) (hw : DifferentiableAt ℝ V w)
    (hE : 0 < ExpectedUtility id p) (hb : b < 1) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), V w < ShareValue V p (fun _ => w)
      (fun x => x - b * ExpectedUtility id p) a := by
  let E := ExpectedUtility id p
  have hd := shareValue_hasDerivAt_zero V p (fun _ => w) (fun x => x - b * E) (fun _ => hw)
  have he : ExpectedUtility (fun x => deriv V w * (x - b * E)) p = deriv V w * ((1 - b) * E) := by
    rw [show (fun x => deriv V w * (x - b * E)) = fun x => deriv V w * id x +
      (-(deriv V w * b * E)) by funext x; dsimp; ring, expectedUtility_affine_payoff]
    dsimp [E]
    ring
  rw [he] at hd
  have hg := improves_small_positive hd
    (mul_pos (deriv_pos_of_concave_strictMono hc hi hw) (mul_pos (sub_pos.mpr hb) hE))
  simpa only [ShareValue, zero_mul, add_zero, expectedUtility_const] using hg

/-- The result persists with independent finite background wealth by conditioning on its value. -/
theorem small_share_independent_wealth {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) (hd : Differentiable ℝ V) (p q : SimpleLottery ℝ) (b : ℝ)
    (hE : 0 < ExpectedUtility id p) (hb : b < 1) : ∀ᶠ a in 𝓝[>] (0 : ℝ),
    ExpectedUtility V q < ExpectedUtility (fun w => ShareValue V p (fun _ => w)
      (fun x => x - b * ExpectedUtility id p) a) q := by
  have he := (Filter.eventually_all_finset q.weights.support).mpr
    (fun w _ => problem_6_13a hc hi p w b (hd w) hE hb)
  filter_upwards [he] with a ha
  unfold ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum_of_nonempty q.support_weights_nonempty
  intro w hw
  exact mul_lt_mul_of_pos_left (ha w hw) (lt_of_le_of_ne (q.nonneg w)
    (Ne.symm (Finsupp.mem_support_iff.mp hw)))

/-- A fair binary draw with net gains minus one or plus three has mean plus one. -/
noncomputable def SmallShareLaw : SimpleLottery ℝ :=
  BinaryLottery (-1) 3 (1 / 2) (by norm_num)

/-- The exact positive mean of the small-share example. -/
theorem smallShareLaw_mean : ExpectedUtility id SmallShareLaw = 1 := by
  rw [SmallShareLaw, expectedUtility_binary]
  norm_num

/-- A kink at initial wealth gives a strict loss for every positive share of the favorable draw. -/
theorem small_share_kink {a : ℝ} (ha : 0 < a) :
    ShareValue (KinkedPriceUtility 0 (1 / 4)) SmallShareLaw (fun _ => 0) id a <
      KinkedPriceUtility 0 (1 / 4) 0 := by
  rw [ShareValue, SmallShareLaw, expectedUtility_binary]
  simp only [id_eq, KinkedPriceUtility, zero_add, sub_zero, mul_zero, min_self, mul_neg, mul_one]
  rw [min_eq_left (by linarith), min_eq_right (by linarith)]
  linarith

/-- The counterexample's utility is increasing and concave and genuinely lacks the derivative. -/
theorem small_share_kink_nondifferentiable :
    StrictMono (KinkedPriceUtility 0 (1 / 4)) ∧
    ConcaveOn ℝ Set.univ (KinkedPriceUtility 0 (1 / 4)) ∧
    ¬DifferentiableAt ℝ (KinkedPriceUtility 0 (1 / 4)) 0 := by
  have hi := kinkedPriceUtility_strictMono (c := 0) (by norm_num : (0 : ℝ) < 1 / 4)
  have hc := kinkedPriceUtility_concave 0 (1 / 4)
  refine ⟨hi, hc, fun hd => ?_⟩
  have h := problem_6_13a hc hi SmallShareLaw 0 0 hd (by rw [smallShareLaw_mean]; norm_num)
    (by norm_num)
  have hp : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hv⟩ := (hp.and h).exists
  simp only [zero_mul, sub_zero] at hv
  exact (small_share_kink ha).not_gt hv

/-- An adverse wealth correlation reverses the small-share comparison even with smooth utility. -/
theorem small_share_correlated_loss :
    let wealth := fun x : ℝ => if x = -1 then 0 else 2
    ∀ᶠ a in 𝓝[>] (0 : ℝ), ShareValue (ExponentialUtility 1) SmallShareLaw wealth id a <
      ShareValue (ExponentialUtility 1) SmallShareLaw wealth id 0 := by
  intro wealth
  have hd := (shareValue_hasDerivAt_zero (ExponentialUtility 1) SmallShareLaw wealth id
    (fun i => (exponentialUtility_hasDerivAt 1 _).differentiableAt)).neg
  apply (improves_small_positive hd ?_).mono
  · intro a ha
    exact neg_lt_neg_iff.mp ha
  · rw [SmallShareLaw, expectedUtility_binary]
    simp only [(exponentialUtility_hasDerivAt 1 _).deriv, wealth, id_eq]
    norm_num
    rw [show Real.exp (-2) = (Real.exp 2)⁻¹ by rw [Real.exp_neg]]
    have he : 3 < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two]
    have he' := (div_lt_one (Real.exp_pos 2)).mpr he
    rw [div_eq_mul_inv] at he'
    linarith

end Kreps.UtilityForMoney
