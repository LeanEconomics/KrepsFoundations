/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.RiskMeasures
import UtilityForMoney.Insurance

/-!
# The constant-absolute-risk-aversion utility family

Kreps I, Proposition 6.12, p. 131. Solving the constant-coefficient differential
equation on the monetary interval gives a positive affine transform of negative
exponential utility. At coefficient zero the solution is positive affine in wealth.
-/

namespace Kreps.UtilityForMoney

/-- Negative exponential utility for a consumer with absolute risk aversion `k`. -/
noncomputable def ExponentialUtility (k x : ℝ) : ℝ := -Real.exp (-k * x)

/-- Derivative of exponential utility at any wealth. -/
theorem exponentialUtility_hasDerivAt (k x : ℝ) :
    HasDerivAt (ExponentialUtility k) (k * Real.exp (-k * x)) x := by
  have h := (((hasDerivAt_id' x).const_mul (-k)).exp).neg
  convert h using 1
  · rfl
  · ring

/-- With positive coefficient, exponential utility is strictly increasing. -/
theorem exponentialUtility_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (ExponentialUtility k) := by
  intro x y hxy
  apply neg_lt_neg
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hxy (neg_neg_of_pos hk))

/-- Exponential utility is strictly concave at every wealth when the coefficient is positive. -/
theorem exponentialUtility_strictConcave {k : ℝ} (hk : 0 < k) :
    StrictConcaveOn ℝ Set.univ (ExponentialUtility k) := by
  have hd := funext fun x => (exponentialUtility_hasDerivAt k x).deriv
  apply StrictAnti.strictConcaveOn_univ_of_deriv
  · exact continuous_iff_continuousAt.mpr fun x => (exponentialUtility_hasDerivAt k x).continuousAt
  · rw [hd]
    intro x y hxy
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hxy (neg_neg_of_pos hk))) hk

/-- Exponential utility has the advertised constant Arrow–Pratt coefficient. -/
theorem absoluteRiskAversion_exponential {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    AbsoluteRiskAversion (ExponentialUtility k) x = k := by
  have hd := funext fun t => (exponentialUtility_hasDerivAt k t).deriv
  have h₂ := ((((hasDerivAt_id' x).const_mul (-k)).exp).const_mul k).deriv
  rw [AbsoluteRiskAversion, hd, h₂]
  field_simp [Real.exp_ne_zero]

/-- Vanishing derivative forces constancy on a real interval using the mean value theorem. -/
theorem eq_on_interval_of_deriv_zero {S : Set ℝ} (hS : Convex ℝ S) {f : ℝ → ℝ}
    (hd : ∀ x ∈ S, HasDerivAt f 0 x) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have h {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) : f a = f b := by
    have hs := hS.ordConnected.out ha hb
    obtain ⟨_, _, he⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab
      (fun t ht => (hd t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hs ⟨ht.1.le, ht.2.le⟩))
    have hzero := (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr hab.ne')
    exact (sub_eq_zero.mp hzero).symm
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact h hx hy hxy
  · rfl
  · exact (h hy hx hyx).symm

/-- A constant coefficient gives an exponential marginal utility on the whole interval. -/
theorem marginal_of_constant_coefficient {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    (k : ℝ) (hk : ∀ x ∈ S, AbsoluteRiskAversion U x = k) :
    ∃ c > 0, ∀ x ∈ S, deriv U x = c * Real.exp (-k * x) := by
  obtain ⟨w, hw⟩ := hne
  let F := fun x => deriv U x * Real.exp (k * x)
  have hd (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    have he := (div_eq_iff (hp x hx).ne').mp (hk x hx)
    have h := (h₂ x hx).hasDerivAt.mul (((hasDerivAt_id' x).const_mul k).exp)
    convert h using 1
    linear_combination Real.exp (k * x) * he
  refine ⟨F w, mul_pos (hp w hw) (Real.exp_pos _), ?_⟩
  intro x hx
  have he := eq_on_interval_of_deriv_zero hS hd hx hw
  rw [← he]
  dsimp [F]
  rw [mul_assoc, ← Real.exp_add, show k * x + -k * x = 0 by ring, Real.exp_zero, mul_one]

/-- **Proposition 6.12, exponential case:** a positive constant coefficient determines the
utility up to positive affine transformation on its interval. -/
theorem proposition_6_12_exponential {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₁ : ∀ x ∈ S, DifferentiableAt ℝ U x)
    (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    {k : ℝ} (hk : 0 < k) (hc : ∀ x ∈ S, AbsoluteRiskAversion U x = k) :
    ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * ExponentialUtility k x := by
  obtain ⟨c, hc', hd⟩ := marginal_of_constant_coefficient hS hne h₂ hp k hc
  obtain ⟨w, hw⟩ := hne
  let B := c / k
  let F := fun x => U x - B * ExponentialUtility k x
  have hf (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    convert (h₁ x hx).hasDerivAt.sub ((exponentialUtility_hasDerivAt k x).const_mul B) using 1
    rw [hd x hx]
    dsimp [B]
    field_simp
    ring
  refine ⟨F w, B, div_pos hc' hk, fun x hx => ?_⟩
  have he := eq_on_interval_of_deriv_zero hS hf hx hw
  dsimp [F] at he ⊢
  linarith

/-- **Proposition 6.12, zero case:** a zero coefficient determines a positive affine utility. -/
theorem proposition_6_12_affine {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₁ : ∀ x ∈ S, DifferentiableAt ℝ U x)
    (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    (hc : ∀ x ∈ S, AbsoluteRiskAversion U x = 0) :
    ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * x := by
  obtain ⟨c, hc', hd⟩ := marginal_of_constant_coefficient hS hne h₂ hp 0 hc
  obtain ⟨w, hw⟩ := hne
  let F := fun x => U x - c * x
  have hf (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    convert (h₁ x hx).hasDerivAt.sub ((hasDerivAt_id' x).const_mul c) using 1
    simp [hd x hx]
  refine ⟨F w, c, hc', fun x hx => ?_⟩
  have he := eq_on_interval_of_deriv_zero hS hf hx hw
  dsimp [F] at he ⊢
  linarith

end Kreps.UtilityForMoney
