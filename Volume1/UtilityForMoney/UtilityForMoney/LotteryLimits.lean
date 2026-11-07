/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryWeakUtilityContinuity
import UtilityForMoney.MonetaryLotteries

/-!
# Continuity in lottery probabilities and prizes

Kreps I, pp. 124–125. With support in a common finite set, expected utility
is continuous in probabilities for arbitrary prize values. Weak convergence
suffices for bounded continuous utility and for continuous utility on a common
compact set of prizes. The latter formulation covers uniformly bounded prizes
when the monetary domain is the real line.
-/

namespace Kreps.UtilityForMoney

open Filter Convexity MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- Extra zero-probability prizes preserve the support sum. -/
theorem expectedUtility_sum_over {X : Type*} (U : X → ℝ) (p : SimpleLottery X) (T : Finset X)
    (hp : p.weights.support ⊆ T) : ExpectedUtility U p = ∑ x ∈ T, p.weights x * U x :=
  Finset.sum_subset hp fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx]

/-- On a common finite set of possible prizes coordinatewise convergence of weights suffices. -/
theorem expectedUtility_tendsto_fixed_support {X : Type*} (U : X → ℝ) (T : Finset X)
    (p : SimpleLottery X) (q : ℕ → SimpleLottery X) (hp : p.weights.support ⊆ T)
    (hq : ∀ n, (q n).weights.support ⊆ T)
    (hw : ∀ x ∈ T, Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  simp only [expectedUtility_sum_over U p T hp, fun n => expectedUtility_sum_over U (q n) T (hq n)]
  exact tendsto_finsetSum _ fun x hx => (hw x hx).mul_const _

/-- Both strict comparisons with any fixed lottery persist eventually. -/
theorem lottery_strict_rankings_eventually {X : Type*} (U : X → ℝ) (p r : SimpleLottery X)
    (q : ℕ → SimpleLottery X)
    (h : Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p))) :
    (ExpectedUtility U r < ExpectedUtility U p →
      ∀ᶠ n in atTop, ExpectedUtility U r < ExpectedUtility U (q n)) ∧
    (ExpectedUtility U p < ExpectedUtility U r →
      ∀ᶠ n in atTop, ExpectedUtility U (q n) < ExpectedUtility U r) :=
  ⟨fun hl => h.eventually (isOpen_Ioi.mem_nhds hl),
    fun hg => h.eventually (isOpen_Iio.mem_nhds hg)⟩

/-- With continuous utility, finitely many probability weights and prize locations can both vary. -/
theorem expectedUtility_tendsto_moving_prizes {X I : Type*} [TopologicalSpace X] [Finite I]
    (U : X → ℝ) (hU : Continuous U) (p : SimpleLottery I) (q : ℕ → SimpleLottery I)
    (x : I → X) (z : ℕ → I → X)
    (hw : ∀ i, Tendsto (fun n => (q n).weights i) atTop (𝓝 (p.weights i)))
    (hx : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ExpectedUtility (fun i => U (z n i)) (q n)) atTop
      (𝓝 (ExpectedUtility (fun i => U (x i)) p)) := by
  let : Fintype I := Fintype.ofFinite I
  have he (u : I → ℝ) (w : SimpleLottery I) : ExpectedUtility u w = ∑ i, w.weights i * u i :=
    Finsupp.sum_fintype _ _ (by simp)
  simp only [he]
  exact tendsto_finsetSum _ fun i _ => (hw i).mul (hU.continuousAt.tendsto.comp (hx i))

/-- The illustrative two-outcome tables on p. 124 have these exact expected utilities. -/
theorem nearby_money_lotteries (U : ℝ → ℝ) :
    ExpectedUtility U (BinaryLottery 4 6 (3/10) (by constructor <;> norm_num)) =
      3/10 * U 4 + 7/10 * U 6 ∧
    ExpectedUtility U (BinaryLottery (39/10) (121/20) (29/100) (by constructor <;> norm_num)) =
      29/100 * U (39/10) + 71/100 * U (121/20) := by
  constructor
  · simpa only [show (1 : ℝ) - 3/10 = 7/10 by norm_num] using
      expectedUtility_binary U 4 6 (3/10) (by constructor <;> norm_num)
  · simpa only [show (1 : ℝ) - 29/100 = 71/100 by norm_num] using
      expectedUtility_binary U (39/10) (121/20) (29/100) (by constructor <;> norm_num)

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- Bounded continuous prize utility preserves weak convergence even when supports change. -/
theorem expectedUtility_tendsto_weak (U : X →ᵇ ℝ) (q : ℕ → SimpleLottery X) (p : SimpleLottery X)
    (hw : Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop
      (𝓝 (LotteryTheory.AtomicProbability p))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U).continuousAt
    |>.tendsto.comp hw
  change Tendsto (fun n => LotteryTheory.ExpectedUtility U (q n)) atTop
    (𝓝 (LotteryTheory.ExpectedUtility U p))
  simpa only [Function.comp_def, LotteryTheory.integral_atomicProbability] using h

/-- Common compact support gives weak convergence of values even for globally unbounded utility. -/
theorem expectedUtility_tendsto_on_compact (U : X → ℝ) (hu : Continuous U) {K : Set X}
    (hK : IsCompact K) (q : ℕ → SimpleLottery X) (p : SimpleLottery X)
    (hp : ∀ x ∈ p.weights.support, x ∈ K) (hq : ∀ n x, x ∈ (q n).weights.support → x ∈ K)
    (hw : Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop
      (𝓝 (LotteryTheory.AtomicProbability p))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  let B := max C 0
  let g (x : X) := min B (max (-B) (U x))
  have hg (x : X) : |g x| ≤ B := abs_le.mpr
    ⟨le_min (by dsimp [B]; linarith [le_max_right C 0]) (le_max_left _ _), min_le_left _ _⟩
  let G : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨g, continuous_const.inf (continuous_const.sup hu)⟩ (B+B) (fun x y =>
      (abs_sub (g x) (g y)).trans (add_le_add (hg x) (hg y)))
  have he (w : SimpleLottery X) (h : ∀ x ∈ w.weights.support, x ∈ K) :
      ExpectedUtility G w = ExpectedUtility U w := by
    apply Finset.sum_congr rfl
    intro x hx
    have hb : |U x| ≤ B := (hC x (h x hx)).trans (le_max_left _ _)
    change w.weights x * min B (max (-B) (U x)) = _
    rw [max_eq_right (abs_le.mp hb).1, min_eq_right (abs_le.mp hb).2]
  simpa only [he p hp, fun n => he (q n) (hq n)] using expectedUtility_tendsto_weak G q p hw

end Kreps.UtilityForMoney
