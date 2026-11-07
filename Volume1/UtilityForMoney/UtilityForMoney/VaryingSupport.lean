/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryLimits

/-!
# Changing finite supports and uniformly bounded utilities

Kreps I, footnote 2, p. 124. Outside the limiting lottery's finite support,
the total probability vanishes. A single bound on the utilities of all extra
prizes makes their combined contribution vanish, even when infinitely many
different prizes occur through the sequence.
-/

namespace Kreps.UtilityForMoney

open Filter
open scoped Topology

/-- A limiting prize with positive mass eventually belongs to every approximating support. -/
theorem eventually_mem_lottery_support {X : Type*} (p : SimpleLottery X) (q : ℕ → SimpleLottery X)
    {x : X} (hx : x ∈ p.weights.support)
    (hw : Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x))) :
    ∀ᶠ n in atTop, x ∈ (q n).weights.support := by
  have hp : 0 < p.weights x := lt_of_le_of_ne (p.nonneg x) (Finsupp.mem_support_iff.mp hx).symm
  filter_upwards [hw.eventually (lt_mem_nhds hp)] with n hn
  exact Finsupp.mem_support_iff.mpr hn.ne'

/-- The portion outside any finite set is bounded by its probability times the utility bound. -/
theorem outside_prize_bound {X : Type*} (U : X → ℝ) (p : SimpleLottery X) (T : Finset X)
    (M : ℝ) (hM : ∀ x ∈ p.weights.support, x ∉ T → |U x| ≤ M) :
    |ExpectedUtility U p - ∑ x ∈ T, p.weights x * U x| ≤
      M * (1 - ∑ x ∈ T, p.weights x) := by
  classical
  let D := T ∪ p.weights.support
  have hsub : T ⊆ D := Finset.subset_union_left
  have hsplit (f : X → ℝ) :
      ExpectedUtility f p - ∑ x ∈ T, p.weights x * f x =
        ∑ x ∈ D \ T, p.weights x * f x := by
    rw [expectedUtility_sum_over f p D Finset.subset_union_right]
    have h := Finset.sum_sdiff (f := fun x => p.weights x * f x) hsub
    linarith
  have mass : (∑ x ∈ D \ T, p.weights x) = 1 - ∑ x ∈ T, p.weights x := by
    have h := hsplit (fun _ => 1)
    simpa only [ExpectedUtility, mul_one, p.total] using h.symm
  rw [hsplit, ← mass, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  refine Finset.sum_le_sum fun x hx => ?_
  obtain ⟨hxD, hn⟩ := Finset.mem_sdiff.mp hx
  have hp := (Finset.mem_union.mp hxD).resolve_left hn
  simpa only [abs_mul, abs_of_nonneg (p.nonneg x), mul_comm M] using
    (show |p.weights x * U x| ≤ p.weights x * M by
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hM x hp hn) (p.nonneg x))

/-- Coordinate convergence on the limiting support and bounded extra prizes imply EU convergence. -/
theorem expectedUtility_tendsto_bounded_extra_prizes {X : Type*} (U : X → ℝ)
    (p : SimpleLottery X) (q : ℕ → SimpleLottery X)
    (hw : ∀ x ∈ p.weights.support, Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x)))
    (M : ℝ) (hM : ∀ n x, x ∈ (q n).weights.support → x ∉ p.weights.support → |U x| ≤ M) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  let T := p.weights.support
  have mass : Tendsto (fun n => ∑ x ∈ T, (q n).weights x) atTop (𝓝 1) := by
    rw [← p.total]
    exact tendsto_finsetSum T (fun x hx => hw x hx)
  have core : Tendsto (fun n => ∑ x ∈ T, (q n).weights x * U x) atTop
      (𝓝 (ExpectedUtility U p)) := tendsto_finsetSum T fun x hx => (hw x hx).mul_const _
  have tail : Tendsto (fun n => ExpectedUtility U (q n) - ∑ x ∈ T, (q n).weights x * U x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => outside_prize_bound U (q n) T M (hM n))
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub mass).const_mul M
  simpa only [sub_add_cancel, zero_add] using tail.add core

end Kreps.UtilityForMoney
