/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries

/-!
# Continuity of utility in the monetary prizes

Kreps I, Proposition 6.2, pp. 123–124. Comparisons with every fixed lottery
remain strict in a neighborhood of a strictly ranked sure prize. Every real
threshold between attained prize utilities is itself the value of a binary
lottery, which supplies the converse for arbitrary relative prize domains.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Both strict comparisons between a sure prize and a fixed lottery persist locally. -/
def StablePrizeComparisons {X : Type*} [TopologicalSpace X] (U : X → ℝ) : Prop :=
  ∀ (x : X) (p : SimpleLottery X),
    (U x < ExpectedUtility U p → ∀ᶠ y in 𝓝 x, U y < ExpectedUtility U p) ∧
    (ExpectedUtility U p < U x → ∀ᶠ y in 𝓝 x, ExpectedUtility U p < U y)

/-- **Proposition 6.2:** the sure-prize stability criterion characterizes continuity. -/
theorem proposition_6_2 {X : Type*} [TopologicalSpace X] (U : X → ℝ) :
    Continuous U ↔ StablePrizeComparisons U := by
  constructor
  · intro h x p
    exact ⟨fun hx => h.continuousAt.eventually (isOpen_Iio.mem_nhds hx),
      fun hx => h.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)⟩
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_order.mpr
    constructor
    · intro t ht
      by_cases hy : ∃ y, U y ≤ t
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨p, hp⟩ := exists_lottery_of_between U y x hy ht.le
        have hs := (h x p).2 (hp ▸ ht)
        simpa only [hp] using hs
      · exact Eventually.of_forall fun y => lt_of_not_ge (fun hn => hy ⟨y, hn⟩)
    · intro t ht
      by_cases hy : ∃ y, t ≤ U y
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨p, hp⟩ := exists_lottery_of_between U x y ht.le hy
        have hs := (h x p).1 (hp ▸ ht)
        simpa only [hp] using hs
      · exact Eventually.of_forall fun y => lt_of_not_ge (fun hn => hy ⟨y, hn⟩)

/-- For a metric prize space, local stability uses the source's open neighborhoods and radii. -/
theorem stablePrizeComparisons_iff_metric {X : Type*} [PseudoMetricSpace X] (U : X → ℝ) :
    StablePrizeComparisons U ↔ ∀ (x : X) (p : SimpleLottery X),
      (U x < ExpectedUtility U p → ∃ ε > 0, ∀ y, dist y x < ε → U y < ExpectedUtility U p) ∧
      (ExpectedUtility U p < U x → ∃ ε > 0, ∀ y, dist y x < ε → ExpectedUtility U p < U y) := by
  simp only [StablePrizeComparisons, Metric.eventually_nhds_iff]

end Kreps.UtilityForMoney
