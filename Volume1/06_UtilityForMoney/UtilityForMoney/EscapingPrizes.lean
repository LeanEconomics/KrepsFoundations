/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryLimits

/-!
# Weak limits and small-probability monetary prizes

Kreps I, footnote 3, pp. 124–125. A vanishing chance of a prize with sufficiently
large utility alters an expected-utility ranking even as the laws converge weakly
to a sure prize. On an interval with an excluded endpoint, bounded monetary prizes
can likewise leave every compact subset of the prize domain.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory Filter Convexity
open scoped Topology

attribute [local instance] LotteryTheory.BorelConvexSpace

variable {X : Type*} [MeasurableSpace X]

/-- The probability law of a binary lottery is the indicated mixture of Dirac laws. -/
theorem binaryLottery_law (x y : X) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    LotteryTheory.AtomicProbability (BinaryLottery x y a ha) =
      LotteryTheory.Mix ⟨a, ha⟩ (diracProba x) (diracProba y) := by
  rw [LotteryTheory.AtomicProbability, LotteryTheory.measureCombination_eq_barycenter,
    BinaryLottery]
  rw [(StdSimplex.isAffineMap_map ℝ diracProba).map_convexCombPair, sConvexComb_convexCombPair]
  simp only [StdSimplex.map_single, sConvexComb_single, LotteryTheory.Mix]

/-- The rare prize receives probability one over the positive trial index. -/
noncomputable def RareWeight (n : ℕ) : LotteryTheory.Weight :=
  ⟨1 / ((n : ℝ) + 1), by positivity,
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩

/-- The weak law of the rare-prize lottery tends to the unchanged sure prize. -/
theorem rareLottery_weak_limit [TopologicalSpace X] [OpensMeasurableSpace X] (x : ℕ → X) (x₀ : X) :
    Tendsto (fun n => LotteryTheory.AtomicProbability
      (BinaryLottery (x n) x₀ (RareWeight n).val (RareWeight n).property)) atTop
      (𝓝 (diracProba x₀)) := by
  simp only [binaryLottery_law]
  exact LotteryTheory.weakMix_tendsto (diracProba x₀) (fun n => diracProba (x n))
    RareWeight tendsto_one_div_add_atTop_nhds_zero_nat

/-- Footnote 3. A fixed binary lottery with the intermediate utility separates the rankings. -/
theorem unbounded_prize_reversal [TopologicalSpace X] [OpensMeasurableSpace X]
    (U : X → ℝ) (x₀ : X) (hun : ∀ c : ℝ, ∃ x, c < U x) :
    ∃ (q : ℕ → SimpleLottery X) (r : SimpleLottery X),
      Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop (𝓝 (diracProba x₀)) ∧
      ExpectedUtility U r = U x₀ + 1 / 2 ∧
      ∀ᶠ n in atTop, ExpectedUtility U r < ExpectedUtility U (q n) := by
  choose x hx using fun n : ℕ => hun ((n : ℝ) + 1)
  obtain ⟨z, hz⟩ := hun (U x₀ + 1)
  let a := (1 / 2) / (U z - U x₀)
  have hd : 0 < U z - U x₀ := by linarith
  have ha : a ∈ Set.Icc 0 1 := ⟨div_nonneg (by norm_num) hd.le, (div_le_one hd).mpr (by linarith)⟩
  let r := BinaryLottery z x₀ a ha
  let q (n : ℕ) := BinaryLottery (x n) x₀ (RareWeight n).val (RareWeight n).property
  have hv : ExpectedUtility U r = U x₀ + 1 / 2 := by
    change ExpectedUtility U (BinaryLottery z x₀ a ha) = _
    rw [expectedUtility_binary U z x₀ a ha]
    have he : a * (U z - U x₀) = 1 / 2 := div_mul_cancel₀ _ hd.ne'
    linarith only [he]
  refine ⟨q, r, rareLottery_weak_limit x x₀, hv, ?_⟩
  have hw : Tendsto (fun n => (RareWeight n).val) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).sub hw).mul_const (U x₀)
  have hlim : Tendsto (fun n => 1 + (1 - (RareWeight n).val) * U x₀) atTop (𝓝 (1 + U x₀)) := by
    simpa only [sub_zero, one_mul] using (tendsto_const_nhds (x := (1 : ℝ))).add hl
  have hh := hlim.eventually (lt_mem_nhds (show U x₀ + 1/2 < 1 + U x₀ by linarith))
  filter_upwards [hh] with n hn
  have hd' : 0 < (n : ℝ) + 1 := by positivity
  have hg : 1 < (RareWeight n).val * U (x n) := by
    change 1 < 1 / ((n : ℝ) + 1) * U (x n)
    rw [one_div_mul_eq_div, one_lt_div hd']
    exact hx n
  rw [hv, show ExpectedUtility U (q n) = _ from
    expectedUtility_binary U (x n) x₀ (RareWeight n).val (RareWeight n).property]
  change U x₀ + 1/2 < 1 + (1 - (RareWeight n).val) * U x₀ at hn
  linarith

/-- A continuous increasing utility on positive wealth with an excluded zero endpoint. -/
noncomputable def OpenWealthUtility (x : Set.Ioi (0 : ℝ)) : ℝ := -x.val⁻¹

/-- The open-domain utility is continuous and strictly increasing at every admissible wealth. -/
theorem openWealthUtility_regular :
    Continuous OpenWealthUtility ∧ StrictMono OpenWealthUtility := by
  exact ⟨(continuous_subtype_val.inv₀ (fun x => x.property.ne')).neg,
    fun x y h => neg_lt_neg_iff.mpr (inv_lt_inv₀ y.property x.property |>.mpr h)⟩

/-- Bounded prizes on an open interval can converge weakly while their expected utilities differ. -/
theorem bounded_prizes_open_endpoint :
    ∃ (q : ℕ → SimpleLottery (Set.Ioi (0 : ℝ))) (b : Set.Ioi (0 : ℝ)),
      (∀ n x, x ∈ (q n).weights.support → x.val ≤ 1) ∧
      Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop (𝓝 (diracProba b)) ∧
      OpenWealthUtility b = -1 ∧ ∀ n, ExpectedUtility OpenWealthUtility (q n) = -2 := by
  let b : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let x (n : ℕ) : Set.Ioi (0 : ℝ) :=
    ⟨1 / ((n : ℝ) + 2), show 0 < 1 / ((n : ℝ) + 2) by positivity⟩
  let q (n : ℕ) := BinaryLottery (x n) b (RareWeight n).val (RareWeight n).property
  refine ⟨q, b, ?_, rareLottery_weak_limit x b, by norm_num [OpenWealthUtility, b], ?_⟩
  · intro n z hz
    by_cases he : z = x n
    · subst z
      change 1 / ((n : ℝ) + 2) ≤ 1
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    by_cases hb : z = b
    · subst z
      exact le_rfl
    exfalso
    apply (Finsupp.mem_support_iff.mp hz)
    change (LotteryTheory.Mix (RareWeight n) (LotteryTheory.PureLottery (x n))
      (LotteryTheory.PureLottery b)).weights z = 0
    rw [LotteryTheory.lottery_mix_weight]
    simp [LotteryTheory.PureLottery, Finsupp.single_eq_of_ne he, Finsupp.single_eq_of_ne hb]
  · intro n
    rw [show ExpectedUtility OpenWealthUtility (q n) = _ from
      expectedUtility_binary OpenWealthUtility (x n) b (RareWeight n).val (RareWeight n).property]
    simp [OpenWealthUtility, x, b, RareWeight]
    field_simp
    ring

end Kreps.UtilityForMoney
