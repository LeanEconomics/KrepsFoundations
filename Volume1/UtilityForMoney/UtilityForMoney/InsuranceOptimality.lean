/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.Insurance

/-!
# Marginal insurance incentives and the unrestricted coverage domain

Kreps I, equation (6.2) and footnotes 13–14, pp. 139–140. The first-order
equation is equivalent to optimality on the entire real line. At a fair premium
a risk-neutral consumer is indifferent across all coverage levels. If the
premium covers or exceeds the loss and the no-loss event has positive probability,
reducing one's position strictly improves expected utility.
-/

namespace Kreps.UtilityForMoney

/-- Concavity survives evaluation at affine wealth and averaging across the two loss states. -/
theorem insuranceUtility_concave {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d : ℝ) :
    ConcaveOn ℝ Set.univ (InsuranceUtility V p y z d) := by
  have hlin (s t : ℝ) : ConcaveOn ℝ Set.univ (fun a : ℝ => V (s + a*t)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ w _ a b ha hb hab
    have h := hc.2 (Set.mem_univ (s+x*t)) (Set.mem_univ (s+w*t)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    convert h using 2
    linear_combination -s * hab
  have h := (ConcaveOn.smul hp.1 (hlin y (-d))).add
    (ConcaveOn.smul (sub_nonneg.mpr hp.2) (hlin z (y-z-d)))
  convert h using 1
  funext a
  change p * V (y-a*d) + (1-p) * V (z+a*(y-z)-a*d) =
    p * V (y+a*(-d)) + (1-p) * V (z+a*(y-z-d))
  rw [show y-a*d = y+a*(-d) by ring, show z+a*(y-z)-a*d = z+a*(y-z-d) by ring]

/-- The derivative is marginal insurance benefit less marginal premium cost. -/
theorem insuranceUtility_hasDerivAt {V : ℝ → ℝ} (hd : Differentiable ℝ V) (p y z d a : ℝ) :
    HasDerivAt (InsuranceUtility V p y z d)
      ((1-p) * (y-z-d) * deriv V (z+a*(y-z)-a*d) - p*d*deriv V (y-a*d)) a := by
  have h₁ := ((hasDerivAt_id' a).mul_const d).const_sub y
  have h₂ := (((hasDerivAt_id' a).mul_const (y-z)).const_add z).sub
    ((hasDerivAt_id' a).mul_const d)
  convert (((hd _).hasDerivAt.comp a h₁).const_mul p).add
    (((hd _).hasDerivAt.comp a h₂).const_mul (1-p)) using 1
  · rfl
  · dsimp
    ring

/-- Equation (6.2) is necessary and sufficient for global optimality. -/
theorem insurance_optimal_iff_marginals {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hd : Differentiable ℝ V) {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d a : ℝ) :
    (∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a) ↔
      p * d * deriv V (y-a*d) = (1-p) * (y-z-d) * deriv V (z+a*(y-z)-a*d) := by
  have hv := insuranceUtility_hasDerivAt hd p y z d a
  constructor
  · intro hm
    have hloc : IsLocalMax (InsuranceUtility V p y z d) a := Filter.Eventually.of_forall hm
    exact (sub_eq_zero.mp (hloc.hasDerivAt_eq_zero hv)).symm
  · intro he b
    rw [he, sub_self] at hv
    have hconc := insuranceUtility_concave hc hp y z d
    rcases lt_trichotomy a b with h | rfl | h
    · have hh := hconc.slope_le_of_hasDerivAt (Set.mem_univ a) (Set.mem_univ b) h hv
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h), zero_mul] at hh
      linarith
    · exact le_rfl
    · have hh := hconc.le_slope_of_hasDerivAt (Set.mem_univ b) (Set.mem_univ a) h hv
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h), zero_mul] at hh
      linarith

/-- Footnote 13. Fair insurance leaves a risk-neutral consumer indifferent over all positions. -/
theorem fair_affine_insurance (A B p y z a b : ℝ) :
    InsuranceUtility (fun x => A*x+B) p y z ((1-p)*(y-z)) a =
      InsuranceUtility (fun x => A*x+B) p y z ((1-p)*(y-z)) b := by
  unfold InsuranceUtility
  ring

/-- Footnote 14. A sufficiently costly contract admits no maximizer with unrestricted positions. -/
theorem expensive_insurance_no_maximum {V : ℝ → ℝ} (hi : StrictMono V) {p y z d : ℝ}
    (hp : p ∈ Set.Ioc 0 1) (hy : z < y) (hd : y - z ≤ d) :
    ¬∃ a, ∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a := by
  rintro ⟨a, h⟩
  have h₁ := mul_lt_mul_of_pos_left
    (hi (show y-a*d < y-(a-1)*d by nlinarith)) hp.1
  have h₂ := mul_le_mul_of_nonneg_left (hi.monotone
    (show z+a*(y-z)-a*d ≤ z+(a-1)*(y-z)-(a-1)*d by nlinarith)) (sub_nonneg.mpr hp.2)
  exact (not_lt_of_ge (h (a-1))) (add_lt_add_of_lt_of_le h₁ h₂)

end Kreps.UtilityForMoney
