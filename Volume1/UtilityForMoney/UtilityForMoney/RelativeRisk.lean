/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.WealthRiskClassification
import UtilityForMoney.ConstantAbsoluteRisk

/-!
# Proportional gambles and relative risk aversion

Kreps I, pp. 131–132. With strictly positive wealth and gross returns, the
certainty-equivalent rate is the sure gross return that matches the lottery.
The printed equivalence on p. 132 has a reversed monotonicity direction for
the relative Arrow–Pratt coefficient.
-/

namespace Kreps.UtilityForMoney

/-- Derivatives of a utility scaled in its wealth input. -/
theorem deriv_scaled_wealth (U : ℝ → ℝ) (w x : ℝ) :
    deriv (fun t => U (w * t)) x = deriv U (w * x) * w := by
  simpa [mul_comm] using deriv_comp_mul_left (f := U) w x

/-- Absolute risk with respect to the rate equals relative wealth risk divided by the rate. -/
theorem absoluteRiskAversion_scaled {U : ℝ → ℝ} {w t : ℝ} (hw : 0 < w) (ht : 0 < t)
    (h₂ : DifferentiableAt ℝ (deriv U) (w * t)) :
    AbsoluteRiskAversion (fun z => U (w * z)) t = RelativeRiskAversion U (w * t) / t := by
  have hd := funext (deriv_scaled_wealth U w)
  have he := (h₂.hasDerivAt.comp t ((hasDerivAt_id' t).const_mul w)).mul_const w
  have h₂eq : deriv (fun x => deriv U (w * x) * w) t =
      deriv (deriv U) (w * t) * w * w := by
    simpa only [mul_one, Function.comp_def] using he.deriv
  rw [AbsoluteRiskAversion, hd, h₂eq]
  unfold RelativeRiskAversion AbsoluteRiskAversion
  field_simp

/-- The riskier gross return yields a weakly lower certainty-equivalent rate at higher wealth. -/
def NonincreasingCertaintyReturn (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → u ≤ v → ∀ (p : SimpleLottery (Set.Ioi (0 : ℝ)))
    (c d : Set.Ioi (0 : ℝ)),
    IsCertaintyEquivalent (fun t : Set.Ioi (0 : ℝ) => U (u * t)) p c →
    IsCertaintyEquivalent (fun t : Set.Ioi (0 : ℝ) => U (v * t)) p d → d ≤ c

/-- Reversing the certainty-equivalent rates is equivalent to comparing all acceptance decisions. -/
theorem nonincreasingCertaintyReturn_iff {U : ℝ → ℝ} (hi : StrictMonoOn U (Set.Ioi 0))
    (hc : ContinuousOn U (Set.Ioi 0)) :
    NonincreasingCertaintyReturn U ↔ ∀ u v : ℝ, 0 < u → u ≤ v →
      MoreRiskAverse (Set.Ioi 0) (fun t => U (v * t)) (fun t => U (u * t)) := by
  have hm (w : ℝ) (hw : 0 < w) : StrictMonoOn (fun t => U (w * t)) (Set.Ioi 0) :=
    fun _ hx _ hy h => hi (mul_pos hw hx) (mul_pos hw hy) (mul_lt_mul_of_pos_left h hw)
  have hcont (w : ℝ) (hw : 0 < w) : ContinuousOn (fun t => U (w * t)) (Set.Ioi 0) :=
    hc.comp (continuous_const.mul continuous_id).continuousOn (fun _ ht => mul_pos hw ht)
  constructor
  · intro h u v hu huv
    apply (premiumOrder_iff_moreRiskAverse (convex_Ioi _) (hm v (hu.trans_le huv))
      (hm u hu) (hcont v (hu.trans_le huv)) (hcont u hu)).mp
    intro p d c hd hc'
    have hdc : (d : ℝ) ≤ c := h u v hu huv p c d hc' hd
    exact sub_le_sub_left hdc _
  · intro h u v hu huv p c d hc' hd
    have he := (premiumOrder_iff_moreRiskAverse (convex_Ioi _) (hm v (hu.trans_le huv))
      (hm u hu) (hcont v (hu.trans_le huv)) (hcont u hu)).mpr (h u v hu huv) p d c hd hc'
    unfold RiskPremium at he
    change (d : ℝ) ≤ c
    linarith

/-- Corrected p. 132 equivalence: falling certainty-equivalent rates correspond to *rising*
relative risk aversion as wealth increases. -/
theorem nonincreasingCertaintyReturn_iff_relative {U : ℝ → ℝ} (hi : StrictMonoOn U (Set.Ioi 0))
    (hU : ∀ x > 0, ContDiffAt ℝ 2 U x) (hp : ∀ x > 0, 0 < deriv U x) :
    NonincreasingCertaintyReturn U ↔ MonotoneOn (RelativeRiskAversion U) (Set.Ioi 0) := by
  have hc : ContinuousOn U (Set.Ioi 0) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  rw [nonincreasingCertaintyReturn_iff hi hc]
  have hsm (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      ContDiffAt ℝ 2 (fun z => U (w * z)) t :=
    (hU _ (mul_pos hw ht)).comp t (contDiffAt_const.mul contDiffAt_id)
  have hpos (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      0 < deriv (fun z => U (w * z)) t := by
    rw [deriv_scaled_wealth]
    exact mul_pos (hp _ (mul_pos hw ht)) hw
  have hder (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : 0 < t) :=
    absoluteRiskAversion_scaled (U := U) hw ht
      (((hU _ (mul_pos hw ht)).derivWithin (m := 1) (by norm_num)).differentiableAt_one)
  have hiff (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :=
    proposition_6_8 (convex_Ioi (0 : ℝ)) (by simp : (interior (Set.Ioi (0 : ℝ))).Nonempty)
      (hsm v hv) (hsm u hu) (fun _ hx _ hy h =>
        hi (mul_pos hu hx) (mul_pos hu hy) (mul_lt_mul_of_pos_left h hu)) (hpos v hv) (hpos u hu)
  constructor
  · intro h u hu v hv huv
    have he := (hiff u v hu hv).mp (h u v hu huv) 1 (by norm_num)
    simpa [hder u hu 1 (by norm_num), hder v hv 1 (by norm_num)] using he
  · intro h u v hu huv
    apply (hiff u v hu (hu.trans_le huv)).mpr
    intro t ht
    rw [hder u hu t ht, hder v (hu.trans_le huv) t ht]
    exact div_le_div_of_nonneg_right (h (mul_pos hu ht) (mul_pos (hu.trans_le huv) ht)
      (mul_le_mul_of_nonneg_right huv ht.le)) ht.le

/-- Exact counterexample to the printed direction: negative exponential utility has increasing
relative risk aversion and nonincreasing certainty-equivalent gross returns. -/
theorem relativeRisk_printed_counterexample :
    NonincreasingCertaintyReturn (ExponentialUtility 1) ∧
      ¬ AntitoneOn (RelativeRiskAversion (ExponentialUtility 1)) (Set.Ioi 0) := by
  have he (x : ℝ) : RelativeRiskAversion (ExponentialUtility 1) x = x := by
    rw [RelativeRiskAversion, absoluteRiskAversion_exponential one_ne_zero, mul_one]
  refine ⟨?_, ?_⟩
  · apply (nonincreasingCertaintyReturn_iff_relative
      ((exponentialUtility_strictMono zero_lt_one).strictMonoOn _)
      (fun x _ => by unfold ExponentialUtility; fun_prop)
      (fun x _ => by rw [(exponentialUtility_hasDerivAt 1 x).deriv]; positivity)).mpr
    intro x _ y _ h
    simpa [he] using h
  · intro h
    have hh := h (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rw [he, he] at hh
    norm_num at hh

end Kreps.UtilityForMoney
