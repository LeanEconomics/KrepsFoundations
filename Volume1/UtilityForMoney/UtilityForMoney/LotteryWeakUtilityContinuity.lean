/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryWeakApproximation

/-!
Local prerequisite copy of ChoiceUnderUncertainty.WeakUtilityContinuity from
commit db0d8dce6618d30395cd02429d614bca59568fe7.
# Weak continuity and bounded affine utility

Kreps I, Proposition 5.10, pp. 98–100. Open strict contours make an affine
representation continuous, since it takes every value between its attainable
levels. Weak continuity on the entire probability space forces boundedness:
vanishing weights on arbitrarily distant utility values contradict continuity.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open MeasureTheory Convexity Filter
open scoped Topology BoundedContinuousFunction

variable {Z X : Type*}

/-- The two strict contour sets at each fixed alternative are open. -/
def OpenStrictSections [TopologicalSpace Z] (r : Z → Z → Prop) : Prop :=
  ∀ z, IsOpen {x | Strict r x z} ∧ IsOpen {x | Strict r z x}

/-- An affine utility attains each scalar strictly between two attainable values. -/
theorem affine_attains_between [ConvexSpace ℝ Z] {u : Z → ℝ} (hu : AffineInMix u)
    {x y : Z} {c : ℝ} (hx : u x ≤ c) (hy : c ≤ u y) (hxy : u x < u y) :
    ∃ z, u z = c := by
  have hd := sub_pos.mpr hxy
  let a : Weight := ⟨(c - u x) / (u y - u x),
    div_nonneg (sub_nonneg.mpr hx) hd.le, (div_le_one hd).mpr (by linarith)⟩
  have he : a.val * (u y - u x) = c - u x := div_mul_cancel₀ _ hd.ne'
  exact ⟨Mix a y x, by rw [hu]; linarith only [he]⟩

/-- Open strict sections characterize continuity of any mixture-affine representing index. -/
theorem openStrictSections_iff_continuous [TopologicalSpace Z] [ConvexSpace ℝ Z]
    {r : Z → Z → Prop} {u : Z → ℝ} (hr : Represents u r) (ha : AffineInMix u) :
    OpenStrictSections r ↔ Continuous u := by
  have hs (x y) : Strict r x y ↔ u y < u x := by
    simp only [Strict, hr x y, hr y x, lt_iff_le_not_ge]
  constructor
  · intro ho
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_order.mpr
    constructor
    · intro c hc
      by_cases hy : ∃ y, u y ≤ c
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨z, rfl⟩ := affine_attains_between ha hy hc.le (hy.trans_lt hc)
        have he := (ho z).1.mem_nhds ((hs x z).mpr hc)
        filter_upwards [he] with t ht using (hs t z).mp ht
      · exact Eventually.of_forall fun t => lt_of_not_ge (fun h => hy ⟨t, h⟩)
    · intro c hc
      by_cases hy : ∃ y, c ≤ u y
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨z, rfl⟩ := affine_attains_between ha hc.le hy (hc.trans_le hy)
        have he := (ho z).2.mem_nhds ((hs z x).mpr hc)
        filter_upwards [he] with t ht using (hs z t).mp ht
      · exact Eventually.of_forall fun t => lt_of_not_ge (fun h => hy ⟨t, h⟩)
  · intro hc z
    simp only [hs]
    exact ⟨isOpen_lt continuous_const hc, isOpen_lt hc continuous_const⟩

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

attribute [local instance] BorelConvexSpace

/-- Integrating a bounded continuous utility is affine under mixing probability measures. -/
theorem integral_affineInMix (g : X →ᵇ ℝ) :
    AffineInMix (fun p : ProbabilityMeasure X => ∫ x, g x ∂(p : Measure X)) := by
  intro a p q
  change (∫ x, g x ∂(MeasureCombination (StdSimplex.duple p q a.property.1
    (sub_nonneg.mpr a.property.2) (by ring)) id : Measure X)) = _
  rw [integral_measureCombination, iConvexComb, StdSimplex.map_duple]
  exact convexCombPair_eq_sum _ _ _ _ _ _ _

/-- A sequence of arbitrarily varying probability measures can receive vanishing mixture weight. -/
theorem weakMix_tendsto (p : ProbabilityMeasure X) (q : ℕ → ProbabilityMeasure X)
    (w : ℕ → Weight) (hw : Tendsto (fun n => (w n).val) atTop (𝓝 0)) :
    Tendsto (fun n => Mix (w n) (q n) p) atTop (𝓝 p) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let v (m : ProbabilityMeasure X) := ∫ x, g x ∂(m : Measure X)
  have hb : IsBoundedUnder (· ≤ ·) atTop (norm ∘ (fun n => v (q n))) :=
    isBoundedUnder_of ⟨‖g‖, fun n => g.norm_integral_le_norm (q n : Measure X)⟩
  have hzero := isBoundedUnder_le_mul_tendsto_zero hb hw
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).sub hw
  have hlim := hzero.add (hone.mul_const (v p))
  convert hlim using 1
  · funext n
    change v (Mix (w n) (q n) p) = _
    rw [show v (Mix (w n) (q n) p) = _ from integral_affineInMix g (w n) (q n) p]
    dsimp [v]
    ring
  · simp [v]

/-- A continuous affine index on all probability measures has bounded range. -/
theorem continuous_affine_bounded {u : ProbabilityMeasure X → ℝ}
    (hc : Continuous u) (ha : AffineInMix u) : ∃ C : ℝ, ∀ p, |u p| ≤ C := by
  classical
  by_cases hi : Nonempty (ProbabilityMeasure X)
  · obtain ⟨p⟩ := hi
    suffices hb : ∃ C : ℝ, ∀ q, |u q - u p| ≤ C by
      obtain ⟨C, hC⟩ := hb
      refine ⟨C + |u p|, fun q => ?_⟩
      calc
        |u q| = |u q - u p + u p| := by rw [sub_add_cancel]
        _ ≤ |u q - u p| + |u p| := abs_add_le _ _
        _ ≤ _ := add_le_add_left (hC q) _
    by_contra! h
    choose q hq using fun n : ℕ => h ((n : ℝ) + 1)
    let w (n : ℕ) : Weight := ⟨1 / ((n : ℝ) + 1), by positivity,
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
    have hl := hc.continuousAt.tendsto.comp
      (weakMix_tendsto p q w tendsto_one_div_add_atTop_nhds_zero_nat)
    obtain ⟨n, hn⟩ := (hl.eventually (Metric.ball_mem_nhds (u p) zero_lt_one)).exists
    change dist (u (Mix (w n) (q n) p)) (u p) < 1 at hn
    rw [Real.dist_eq, ha, show (w n).val * u (q n) + (1 - (w n).val) * u p - u p =
      (w n).val * (u (q n) - u p) by ring, abs_mul, abs_of_nonneg (w n).property.1] at hn
    have hd : 0 < (n : ℝ) + 1 := by positivity
    change 1 / ((n : ℝ) + 1) * |u (q n) - u p| < 1 at hn
    rw [one_div_mul_eq_div, div_lt_one hd] at hn
    exact (hq n).not_gt hn
  · exact ⟨0, fun p => (hi ⟨p⟩).elim⟩

end Kreps.UtilityForMoney.LotteryTheory
