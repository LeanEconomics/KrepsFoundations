/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.DominanceInterpolation
import UtilityForMoney.LotteryLimits

/-!
# The two stochastic dominance orders

Kreps I, p. 132. Both dominance relations are partial orders on monetary laws.
For antisymmetry, differences of three capped payoffs recover the mass of each
individual prize on the finite union of the two supports.
-/

namespace Kreps.UtilityForMoney

/-- Mutual aversion rankings identify expected utility for every increasing capped payoff. -/
theorem capped_values_equal {p q : SimpleLottery ℝ}
    (hp : SecondOrderDominates p q) (hq : SecondOrderDominates q p) (r : ℝ) :
    ExpectedUtility (fun x => min x r) p = ExpectedUtility (fun x => min x r) q := by
  have h := cappedPrizeUtility_properties r
  exact le_antisymm (hq _ h.1 h.2) (hp _ h.1 h.2)

/-- A finite grid admits a positive gap separating any point from its other grid points. -/
theorem finite_prize_gap (T : Finset ℝ) (r : ℝ) :
    ∃ e > 0, ∀ x ∈ T, x ≠ r → e ≤ |x-r| := by
  classical
  by_cases h : (T.erase r).Nonempty
  · let e := (T.erase r).inf' h (fun x => |x-r|)
    obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_inf' h (fun x => |x-r|)
    refine ⟨e, ?_, fun x hx hn => Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hn, hx⟩)⟩
    rw [show e = |x-r| from he]
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1)
  · exact ⟨1, zero_lt_one, fun x hx hn => (h ⟨x, Finset.mem_erase.mpr ⟨hn, hx⟩⟩).elim⟩

/-- A difference of three capped values can isolate one mass on a finite prize grid. -/
theorem secondOrder_antisymm {p q : SimpleLottery ℝ}
    (hp : SecondOrderDominates p q) (hq : SecondOrderDominates q p) : p = q := by
  classical
  apply Convexity.StdSimplex.ext
  ext r
  let T := insert r (p.weights.support ∪ q.weights.support)
  obtain ⟨e, he, hgap⟩ := finite_prize_gap T r
  let F (x : ℝ) := min x (r+e) + min x (r-e) - 2 * min x r
  have aux (w : SimpleLottery ℝ) : ExpectedUtility F w =
      ExpectedUtility (fun x => min x (r+e)) w + ExpectedUtility (fun x => min x (r-e)) w -
        2 * ExpectedUtility (fun x => min x r) w := by
    unfold ExpectedUtility Finsupp.sum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    ring
  have hF : ExpectedUtility F p = ExpectedUtility F q := by
    simp only [aux, capped_values_equal hp hq]
  have at_r : F r = -e := by
    dsimp only [F]
    rw [min_eq_left (by linarith : r ≤ r+e), min_eq_right (by linarith : r-e ≤ r), min_self]
    ring
  have elsewhere (x : ℝ) (hx : x ∈ T) (hn : x ≠ r) : F x = 0 := by
    have hg := hgap x hx hn
    rcases lt_or_gt_of_ne hn with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h.le)] at hg
      dsimp only [F]
      rw [min_eq_left (by linarith : x ≤ r+e), min_eq_left (by linarith : x ≤ r-e),
        min_eq_left h.le]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h.le)] at hg
      dsimp only [F]
      rw [min_eq_right (by linarith : r+e ≤ x), min_eq_right (by linarith : r-e ≤ x),
        min_eq_right h.le]
      ring
  have val (w : SimpleLottery ℝ) (hw : w.weights.support ⊆ T) :
      ExpectedUtility F w = w.weights r * -e := by
    rw [expectedUtility_sum_over F w T hw,
      Finset.sum_eq_single_of_mem r (Finset.mem_insert_self _ _)]
    · rw [at_r]
    · intro x hx hn
      rw [elsewhere x hx hn, mul_zero]
  have sub : p.weights.support ∪ q.weights.support ⊆ T := Finset.subset_insert _ _
  rw [val p (Finset.subset_union_left.trans sub), val q (Finset.subset_union_right.trans sub)] at hF
  exact (mul_left_inj' (neg_ne_zero.mpr he.ne')).mp hF

/-- First-order dominance is antisymmetric on actual prize laws. -/
theorem firstOrder_antisymm {p q : SimpleLottery ℝ}
    (hp : FirstOrderDominates p q) (hq : FirstOrderDominates q p) : p = q :=
  secondOrder_antisymm (fun U hm _ => hp U hm) (fun U hm _ => hq U hm)

/-- The two dominance relations are reflexive. -/
theorem dominance_reflexive (p : SimpleLottery ℝ) :
    FirstOrderDominates p p ∧ SecondOrderDominates p p :=
  ⟨fun _ _ => le_rfl, fun _ _ _ => le_rfl⟩

/-- Both stochastic rankings compose transitively. -/
theorem dominance_transitive (p q r : SimpleLottery ℝ) :
    (FirstOrderDominates p q → FirstOrderDominates q r → FirstOrderDominates p r) ∧
    (SecondOrderDominates p q → SecondOrderDominates q r → SecondOrderDominates p r) :=
  ⟨fun hp hq U hm => (hq U hm).trans (hp U hm),
    fun hp hq U hm hc => (hq U hm hc).trans (hp U hm hc)⟩

end Kreps.UtilityForMoney
