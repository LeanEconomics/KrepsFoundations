/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries
import Mathlib.Analysis.Convex.Continuous

/-!
# Risk in relative prices and the price level

Kreps I, Problem 6.8, p. 143. Linear ordinal tastes favor gambling on which
good is cheap. With complementary goods, a strictly increasing piecewise
linear concave index can favor the mean price. Each fixed concave index on
the real line eventually favors sufficiently dispersed price levels. Strict
comparisons require positive income, since zero income allows only the origin.
-/

namespace Kreps.UtilityForMoney

/-- Feasible two-good bundles at unit prices `p` and `q` and income `y`. -/
def TwoGoodBudget (p q y : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ p * x.1 + q * x.2 ≤ y}

/-- At prices (1,3) or (3,1), the cheap good alone attains total quantity equal to income. -/
theorem sum_bundle_risky_price_optima (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget 1 3 y, f (x.1 + x.2) = f y) ∧
    (∃ x ∈ TwoGoodBudget 3 1 y, f (x.1 + x.2) = f y) ∧
    ∀ x : ℝ × ℝ, x ∈ TwoGoodBudget 1 3 y ∨ x ∈ TwoGoodBudget 3 1 y →
      f (x.1 + x.2) ≤ f y := by
  refine ⟨⟨(y, 0), ⟨hy, le_rfl, by simp⟩, by simp⟩,
    ⟨(0, y), ⟨le_rfl, hy, by simp⟩, by simp⟩, fun x hx => hf.monotone ?_⟩
  rcases hx with ⟨_, hx, hc⟩ | ⟨hx, _, hc⟩ <;> linarith

/-- At the sure mean prices (2,2), maximal total quantity is half of income. -/
theorem sum_bundle_mean_price_optimum (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget 2 2 y, f (x.1 + x.2) = f (y / 2)) ∧
    ∀ x ∈ TwoGoodBudget 2 2 y, f (x.1 + x.2) ≤ f (y / 2) := by
  refine ⟨⟨(y / 2, 0), ⟨by positivity, le_rfl, by dsimp; linarith⟩, by simp⟩,
    fun x hx => hf.monotone (by linarith [hx.2.2])⟩

/-- **Problem 6.8(a):** every increasing cardinalization strictly favors the risky prices. -/
theorem problem_6_8a (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 < y) :
    f (y / 2) < (f y + f y) / 2 := by
  rw [add_self_div_two]
  exact hf (by linarith)

/-- Maximum utility with complementary goods when both prices equal the price level. -/
theorem complementary_bundle_value (f : ℝ → ℝ) (hf : StrictMono f) {p y : ℝ}
    (hp : 0 < p) (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget p p y, f (min x.1 x.2) = f (y / (2 * p))) ∧
    ∀ x ∈ TwoGoodBudget p p y, f (min x.1 x.2) ≤ f (y / (2 * p)) := by
  let t := y / (2 * p)
  have ht : (2 * p) * t = y := by dsimp [t]; field_simp
  refine ⟨⟨(t, t), ⟨by dsimp [t]; positivity, by dsimp [t]; positivity, ?_⟩, by simp [t]⟩,
    fun x hx => hf.monotone ((le_div_iff₀ (by positivity)).mpr ?_)⟩
  · dsimp
    linarith
  · have h₁ := mul_le_mul_of_nonneg_left (min_le_left x.1 x.2) hp.le
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right x.1 x.2) hp.le
    linarith [hx.2.2]

/-- A kinked cardinalization with unit left slope and strictly positive right slope. -/
def KinkedPriceUtility (c e t : ℝ) : ℝ := min t (c + e * (t - c))

/-- Positive slopes on both pieces guarantee strict increase. -/
theorem kinkedPriceUtility_strictMono {c e : ℝ} (he : 0 < e) :
    StrictMono (KinkedPriceUtility c e) := by
  intro x y h
  exact lt_min ((min_le_left _ _).trans_lt h)
    ((min_le_right _ _).trans_lt (by nlinarith [mul_pos he (sub_pos.mpr h)]))

/-- A pointwise minimum of these two affine functions is concave everywhere. -/
theorem kinkedPriceUtility_concave (c e : ℝ) : ConcaveOn ℝ Set.univ (KinkedPriceUtility c e) := by
  have h : ConcaveOn ℝ Set.univ (fun t : ℝ => c + e * (t - c)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    nlinarith only [congrArg (fun v : ℝ => v * (c - e * c)) hab]
  exact (concaveOn_id convex_univ).inf h

/-- The low, sure and high quantities of a complementary good are strictly ordered. -/
theorem price_level_quantities_order {y g : ℝ} (hy : 0 < y) (hg : 1 < g) :
    y / (2 * g) < y / (g + g⁻¹) ∧ y / (g + g⁻¹) < y * g / 2 := by
  have hgp : 0 < g := by linarith
  have hi : g⁻¹ < 1 := (inv_lt_one₀ hgp).mpr hg
  constructor
  · exact div_lt_div_of_pos_left hy (by positivity) (by linarith)
  · apply (div_lt_iff₀ (by positivity)).mpr
    field_simp
    nlinarith [mul_pos hy (mul_pos (sub_pos.mpr hg) (by linarith : 0 < g + 1))]

/-- A fixed price dispersion admits an increasing concave index favoring the sure price. -/
theorem problem_6_8b_fixed_dispersion {y g : ℝ} (hy : 0 < y) (hg : 1 < g) :
    ∃ f : ℝ → ℝ, StrictMono f ∧ ConcaveOn ℝ Set.univ f ∧
      (f (y / (2 * g)) + f (y * g / 2)) / 2 < f (y / (g + g⁻¹)) := by
  let l := y / (2 * g)
  let c := y / (g + g⁻¹)
  let u := y * g / 2
  obtain ⟨hl, hu⟩ := price_level_quantities_order hy hg
  change l < c at hl
  change c < u at hu
  let e := (c - l) / (2 * (u - c))
  have he : 0 < e := div_pos (sub_pos.mpr hl) (by linarith)
  have hid : e * (2 * (u - c)) = c - l := div_mul_cancel₀ _ (by linarith)
  refine ⟨KinkedPriceUtility c e, kinkedPriceUtility_strictMono he, kinkedPriceUtility_concave ..,
    ?_⟩
  change (min l _ + min u _) / 2 < min c (c + e * (c - c))
  rw [sub_self, mul_zero, add_zero, min_self]
  nlinarith only [min_le_left l (c + e * (l - c)), min_le_right u (c + e * (u - c)), hid, hl]

/-- Each fixed increasing concave index eventually prefers sufficiently dispersed price levels. -/
theorem problem_6_8b_large_dispersion (f : ℝ → ℝ) (hf : StrictMono f)
    (hc : ConcaveOn ℝ Set.univ f) {y : ℝ} (hy : 0 < y) :
    ∃ G > (1 : ℝ), ∀ g ≥ G,
      f (y / (g + g⁻¹)) < (f (y / (2 * g)) + f (y * g / 2)) / 2 := by
  have hcont : Continuous f := continuousOn_univ.mp (by simpa using hc.continuousOn_interior)
  have hlt : f 0 < (f 0 + f 1) / 2 := by linarith [hf (show (0 : ℝ) < 1 by norm_num)]
  obtain ⟨ε, hε, hs⟩ := Metric.isOpen_iff.mp
    (isOpen_lt hcont continuous_const) 0 hlt
  refine ⟨max 2 (max (y / ε) (2 / y)) + 1, by linarith [le_max_left 2 (max (y / ε) (2 / y))],
    fun g hg => ?_⟩
  have hg' : 0 < g := by linarith [le_max_left 2 (max (y / ε) (2 / y))]
  have hgε : y / ε < g := by
    linarith [le_max_right 2 (max (y / ε) (2 / y)), le_max_left (y / ε) (2 / y)]
  have hgy : 2 / y < g := by
    linarith [le_max_right 2 (max (y / ε) (2 / y)), le_max_right (y / ε) (2 / y)]
  have hlow : 0 < y / (g + g⁻¹) := by positivity
  have hsmall : y / (g + g⁻¹) < ε := (div_lt_iff₀ (by positivity)).mpr (by
    nlinarith [(div_lt_iff₀ hε).mp hgε, mul_pos hε (inv_pos.mpr hg')])
  have hcval := hs (show y / (g + g⁻¹) ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlow] using hsmall)
  exact hcval.trans_le (by
    have h₁ := hf.monotone (show 0 ≤ y / (2 * g) by positivity)
    have h₂ := hf.monotone (show 1 ≤ y * g / 2 by linarith [(div_lt_iff₀ hy).mp hgy])
    linarith)

/-- The price lotteries in Problem 6.8(b) pay the two statewise optimized quantities. -/
theorem price_risk_expectedUtility (f : ℝ → ℝ) (y : ℝ) {g : ℝ} (hg : 0 < g) :
    ExpectedUtility f (BinaryLottery (y / (2 * g)) (y / (2 * g⁻¹)) (1 / 2) (by norm_num)) =
      (f (y / (2 * g)) + f (y * g / 2)) / 2 := by
  have he : y / (2 * g⁻¹) = y * g / 2 := by field_simp
  rw [expectedUtility_binary, he]
  ring

/-- At zero income all three statewise maxima coincide, so neither price regime is preferred. -/
theorem price_risk_at_zero_income (f : ℝ → ℝ) (g : ℝ) :
    (f (0 / (2 * g)) + f (0 * g / 2)) / 2 = f (0 / (g + g⁻¹)) := by
  simp

end Kreps.UtilityForMoney
