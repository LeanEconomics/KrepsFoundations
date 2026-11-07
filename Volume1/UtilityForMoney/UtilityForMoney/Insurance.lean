/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# Insurance at fair and unfair premiums

Kreps I, Proposition 6.17, pp. 138–140. Coverage is a real number, so both
negative coverage and overinsurance are allowed. Jensen's inequality bounds
the entire objective, and the derivative at full coverage excludes it when
the premium is unfair.
-/

namespace Kreps.UtilityForMoney

/-- Expected utility of buying coverage `a` at premium `d` per unit of coverage. -/
def InsuranceUtility (V : ℝ → ℝ) (p y z d a : ℝ) : ℝ :=
  p * V (y - a * d) + (1 - p) * V (z + a * (y - z) - a * d)

/-- Full insurance makes income certain in both states. -/
theorem insuranceUtility_one (V : ℝ → ℝ) (p y z d : ℝ) :
    InsuranceUtility V p y z d 1 = V (y - d) := by
  unfold InsuranceUtility
  rw [one_mul, one_mul, show z + (y - z) - d = y - d by ring]
  ring

/-- Concavity bounds insurance utility by the utility of mean net income. -/
theorem insuranceUtility_le_mean {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d a : ℝ) :
    InsuranceUtility V p y z d a ≤
      V (p * y + (1 - p) * z + a * ((1 - p) * (y - z) - d)) := by
  have h := hc.2 (Set.mem_univ (y - a * d)) (Set.mem_univ (z + a * (y - z) - a * d))
    hp.1 (sub_nonneg.mpr hp.2) (show p + (1 - p) = 1 by ring)
  simp only [smul_eq_mul] at h
  unfold InsuranceUtility
  convert h using 2
  ring

/-- **Proposition 6.17(a):** full coverage attains a global maximum at a fair premium. -/
theorem proposition_6_17a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z : ℝ) (a : ℝ) :
    InsuranceUtility V p y z ((1 - p) * (y - z)) a ≤
      InsuranceUtility V p y z ((1 - p) * (y - z)) 1 := by
  rw [insuranceUtility_one]
  convert insuranceUtility_le_mean hc hp y z ((1 - p) * (y - z)) a using 2
  ring

/-- Strict increase and concavity make the marginal utility of real wealth positive. -/
theorem deriv_pos_of_concave_strictMono {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) {w : ℝ} (hd : DifferentiableAt ℝ V w) : 0 < deriv V w := by
  have hw : w < w + 1 := by linarith
  have h := hc.slope_le_deriv (Set.mem_univ w) (Set.mem_univ (w + 1)) hw hd
  rw [slope_def_field] at h
  exact (div_pos (sub_pos.mpr (hi hw)) (sub_pos.mpr hw)).trans_le h

/-- At full coverage the marginal benefit is the actuarial discount times marginal utility. -/
theorem insuranceUtility_hasDerivAt_one {V : ℝ → ℝ} (p y z d : ℝ)
    (hd : DifferentiableAt ℝ V (y - d)) :
    HasDerivAt (InsuranceUtility V p y z d)
      (((1 - p) * (y - z) - d) * deriv V (y - d)) 1 := by
  have h₁ : HasDerivAt (fun a : ℝ => y - a * d) (-d) 1 := by
    simpa using ((hasDerivAt_id' 1).mul_const d).const_sub y
  have h₂ : HasDerivAt (fun a : ℝ => z + a * (y - z) - a * d) (y - z - d) 1 := by
    convert (((hasDerivAt_id' (1 : ℝ)).mul_const (y - z)).const_add z).sub
      ((hasDerivAt_id' 1).mul_const d) using 1
    ring
  have h₃ : HasDerivAt V (deriv V (y - d)) (y - 1 * d) := by simpa using hd.hasDerivAt
  have h₄ : HasDerivAt V (deriv V (y - d)) (z + 1 * (y - z) - 1 * d) := by
    convert hd.hasDerivAt using 1
    ring
  convert ((h₃.comp 1 h₁).const_mul p).add ((h₄.comp 1 h₂).const_mul (1 - p)) using 1
  · rfl
  · ring

/-- **Proposition 6.17(b):** every optimum under an unfair premium is below full coverage. -/
theorem proposition_6_17b {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) {p y z d a : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hd : DifferentiableAt ℝ V (y - d)) (hunfair : (1 - p) * (y - z) < d)
    (hmax : ∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a) : a < 1 := by
  by_contra! ha
  rcases ha.eq_or_lt with he | hlt
  · subst a
    have hm : IsLocalMax (InsuranceUtility V p y z d) 1 := Filter.Eventually.of_forall hmax
    have hzero := hm.hasDerivAt_eq_zero (insuranceUtility_hasDerivAt_one p y z d hd)
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hunfair)
      (deriv_pos_of_concave_strictMono hc hi hd)
    linarith
  · have hmean := insuranceUtility_le_mean hc hp y z d a
    have h := mul_lt_mul_of_neg_right hlt (sub_neg.mpr hunfair)
    have hlt' : p * y + (1 - p) * z + a * ((1 - p) * (y - z) - d) < y - d := by
      nlinarith
    have hcontra := hmax 1
    rw [insuranceUtility_one] at hcontra
    exact (not_lt_of_ge hcontra) (hmean.trans_lt (hi hlt'))

end Kreps.UtilityForMoney
