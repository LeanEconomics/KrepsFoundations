/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.DominanceInterpolation
import UtilityForMoney.SupermartingaleCoupling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrated distribution functions and downside risk

Kreps I, Proposition 6.14(b) and Problem 6.6(a,c), pp. 132–133 and 141–142.
Integrating the step distribution above a zero-mass cutoff yields its expected
shortfall. The capped-utility characterization then gives the full converse and
the joint law with conditionally nonpositive supplements.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory Set

/-- A zero cumulative mass means that the threshold is strictly below each support prize. -/
theorem cumulative_zero_iff (p : SimpleLottery ℝ) (b : ℝ) :
    Cumulative p b = 0 ↔ ∀ x ∈ p.weights.support, b < x := by
  classical
  constructor
  · intro hz x hx
    by_contra! hle
    have hn (t : ℝ) : 0 ≤ p.weights t * (if t ≤ b then 1 else 0 : ℝ) :=
      mul_nonneg (p.nonneg t) (by split <;> norm_num)
    have h := Finset.single_le_sum (s := p.weights.support)
      (f := fun t => p.weights t * (if t ≤ b then 1 else 0 : ℝ)) (fun t _ => hn t) hx
    change p.weights x * _ ≤ Cumulative p b at h
    simp only [hz, hle, ↓reduceIte, mul_one] at h
    exact (Finsupp.mem_support_iff.mp hx) (le_antisymm h (p.nonneg x))
  · intro hs
    unfold Cumulative ExpectedUtility Finsupp.sum
    apply Finset.sum_eq_zero
    intro x hx
    simp [(hs x hx).not_ge]

/-- The integral of one atom's cumulative step is its mass times its shortfall. -/
theorem atom_cdf_integral (m x b r : ℝ) (hb : b < x) (hr : b ≤ r) :
    (∫ z in b..r, m * (if x ≤ z then 1 else 0 : ℝ)) = m * max (r - x) 0 := by
  have he : (fun z : ℝ => m * (if x ≤ z then 1 else 0 : ℝ)) =
      (Ici x).indicator (fun _ => m) := by
    funext z
    by_cases h : x ≤ z <;> simp [indicator, h]
  have hi : Ioc b r ∩ Ici x = Icc x r := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hb.trans_le h.1, h.2⟩, h.1⟩⟩
  rw [he, intervalIntegral.integral_of_le hr, setIntegral_indicator measurableSet_Ici, hi,
    setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_comm]

/-- An integrated cumulative distribution equals the support sum of shortfalls. -/
theorem integrated_cumulative_eq_shortfall (p : SimpleLottery ℝ) {b r : ℝ}
    (hb : Cumulative p b = 0) (hr : b ≤ r) :
    (∫ z in b..r, Cumulative p z) = ExpectedShortfall p r := by
  classical
  unfold Cumulative ExpectedShortfall ExpectedUtility Finsupp.sum
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun x hx =>
      atom_cdf_integral _ _ _ _ ((cumulative_zero_iff p b).mp hb x hx) hr
  · intro x _
    change IntervalIntegrable (fun z : ℝ => p.weights x * (if x ≤ z then 1 else 0 : ℝ))
      volume b r
    have hi : IntervalIntegrable ((Ici x).indicator (fun _ : ℝ => p.weights x)) volume b r :=
      intervalIntegrable_iff.mpr (intervalIntegrable_const.def'.indicator measurableSet_Ici)
    convert hi using 1
    funext z
    by_cases h : x ≤ z <;> simp [indicator, h]

/-- All shortfalls are zero below any common lower support bound. -/
theorem expectedShortfall_zero_of_le {p : SimpleLottery ℝ} {b r : ℝ}
    (hb : Cumulative p b = 0) (hr : r ≤ b) : ExpectedShortfall p r = 0 := by
  unfold ExpectedShortfall ExpectedUtility Finsupp.sum
  apply Finset.sum_eq_zero
  intro x hx
  have h := hr.trans ((cumulative_zero_iff p b).mp hb x hx).le
  simp [sub_nonpos.mpr h]

/-- Proposition 6.14(b). Weak integrated-CDF comparisons characterize second-order dominance. -/
theorem proposition_6_14b (p q : SimpleLottery ℝ) (b : ℝ)
    (hp : Cumulative p b = 0) (hq : Cumulative q b = 0) :
    SecondOrderDominates p q ↔ ∀ r, b ≤ r →
      (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z := by
  rw [secondOrder_iff_shortfalls]
  constructor
  · intro h r hr
    simpa only [integrated_cumulative_eq_shortfall p hp hr,
      integrated_cumulative_eq_shortfall q hq hr] using h r
  · intro h r
    rcases le_or_gt r b with hle | hgt
    · rw [expectedShortfall_zero_of_le hp hle, expectedShortfall_zero_of_le hq hle]
    · simpa only [integrated_cumulative_eq_shortfall p hp hgt.le,
        integrated_cumulative_eq_shortfall q hq hgt.le] using h r hgt.le

/-- Problem 6.6(a). The integrated comparison holds above any strict lower support bound. -/
theorem problem_6_6a {p q : SimpleLottery ℝ} (h : SecondOrderDominates p q) (b : ℝ)
    (hp : ∀ x ∈ p.weights.support, b < x) (hq : ∀ x ∈ q.weights.support, b < x) :
    ∀ r, b < r → (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z :=
  fun r hr => (proposition_6_14b p q b ((cumulative_zero_iff p b).mpr hp)
    ((cumulative_zero_iff q b).mpr hq)).mp h r hr.le

/-- Problem 6.6(c). The stated integrated-CDF comparisons produce the required joint variables. -/
theorem problem_6_6c {p q : SimpleLottery ℝ} (b : ℝ)
    (hp : ∀ x ∈ p.weights.support, b < x) (hq : ∀ x ∈ q.weights.support, b < x)
    (h : ∀ r, b ≤ r → (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z) :
    ∃ C : FiniteCoupling p q, ∀ i, C.conditionalDrift i ≤ 0 := by
  obtain ⟨C, hc⟩ := supermartingaleCoupling_of_dominance
    ((proposition_6_14b p q b ((cumulative_zero_iff p b).mpr hp)
      ((cumulative_zero_iff q b).mpr hq)).mpr h)
  exact ⟨C, C.nonpositiveDrift_iff.mp hc⟩

end Kreps.UtilityForMoney
