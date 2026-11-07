/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.QuantileBins
import UtilityForMoney.FiniteCouplings
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# First-order dominance by common uniform draws

Kreps I, Propositions 6.14(a) and 6.15(a), and Problem 6.5(b–d), pp. 132–133,
141–142. A uniform draw selects the support point of its half-open cumulative
interval. The joint probability of two prizes is the length of the intersection
of their intervals, which gives the two specified margins.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory

/-- Each quantile bin lies in the unit draw interval. -/
theorem quantileBin_subset_unit (p : SimpleLottery ℝ) (x : ℝ) :
    QuantileBin p x ⊆ Set.Ioc 0 1 := by
  intro u hu
  have hb := prefix_probability_bounds p x
  exact ⟨hb.1.trans_lt hu.1, hu.2.trans hb.2.2⟩

/-- **Problem 6.5(b):** inverse-CDF sampling has each exact prescribed point mass. -/
theorem quantilePrize_uniform_mass (p : SimpleLottery ℝ) (x : ℝ) :
    volume {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = ENNReal.ofReal (p.weights x) := by
  by_cases hx : x ∈ p.weights.support
  · have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = QuantileBin p x := by
      ext u
      constructor
      · rintro ⟨hu, rfl⟩
        exact (quantilePrize_mem_bin p hu).2
      · intro hu
        have h := quantileBin_subset_unit p x hu
        exact ⟨h, quantileBin_unique p (quantilePrize_mem_bin p h).2 hu⟩
    rw [he, QuantileBin, Real.volume_Ioc, prefix_sub_before _ hx]
  · have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, he⟩
      exact hx (he ▸ (quantilePrize_mem_bin p hu).1)
    rw [he, measure_empty, Finsupp.notMem_support_iff.mp hx, ENNReal.ofReal_zero]

/-- Length of the intersection of two real probability bins, by inclusion and exclusion. -/
def Overlap (a b c d : ℝ) : ℝ := (min b d - min b c) - (min a d - min a c)

/-- The overlap agrees with the nonnegative part of the difference of its endpoints. -/
theorem overlap_eq_length {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    Overlap a b c d = max (min b d - max a c) 0 := by
  unfold Overlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Exchanging the bins does not change their overlap. -/
theorem overlap_comm (a b c d : ℝ) : Overlap a b c d = Overlap c d a b := by
  unfold Overlap
  rw [min_comm b d, min_comm b c, min_comm a d, min_comm a c]
  ring

/-- The sum of intersections of a fixed unit subinterval with all bins equals its length. -/
theorem sum_overlap_bins (p : SimpleLottery ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∑ j : p.weights.support, Overlap a b (Before p.weights.support p.weights j.val)
      (Prefix p.weights.support p.weights j.val) = b - a := by
  classical
  rw [Finset.sum_coe_sort p.weights.support (fun j =>
    Overlap a b (Before p.weights.support p.weights j) (Prefix p.weights.support p.weights j))]
  unfold Overlap
  rw [Finset.sum_sub_distrib,
    sum_prefix_increments p.weights.support p.weights (fun t => min b t),
    sum_prefix_increments p.weights.support p.weights (fun t => min a t)]
  have h₁ : ∑ x ∈ p.weights.support, p.weights x = 1 := p.total
  rw [h₁, min_eq_left hb, min_eq_left (hab.trans hb), min_eq_right (ha.trans hab), min_eq_right ha]
  ring

/-- The joint table formed from the shared uniform draw. -/
noncomputable def QuantileCoupling (p q : SimpleLottery ℝ) : FiniteCoupling p q where
  mass i j := Overlap (Before p.weights.support p.weights i.val)
    (Prefix p.weights.support p.weights i.val) (Before q.weights.support q.weights j.val)
    (Prefix q.weights.support q.weights j.val)
  nonneg i j := by
    rw [overlap_eq_length (prefix_probability_bounds p i.val).2.1
      (prefix_probability_bounds q j.val).2.1]
    exact le_max_right _ _
  row_sum i := by
    have h := prefix_probability_bounds p i.val
    rw [sum_overlap_bins q h.1 h.2.1 h.2.2, prefix_sub_before _ i.property]
  col_sum j := by
    have h := prefix_probability_bounds q j.val
    simp_rw [overlap_comm _ _ (Before q.weights.support q.weights j.val)
      (Prefix q.weights.support q.weights j.val)]
    rw [sum_overlap_bins p h.1 h.2.1 h.2.2, prefix_sub_before _ j.property]

/-- A nonnegative supplement, in matrix form, holds at every joint atom of positive mass. -/
def FiniteCoupling.Ordered {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) : Prop :=
  ∀ i j, 0 < C.mass i j → j.val ≤ i.val

/-- **Problem 6.5(c):** the ordered CDFs put the first quantile weakly above the second. -/
theorem quantileCoupling_ordered {p q : SimpleLottery ℝ}
    (h : ∀ r, Cumulative p r ≤ Cumulative q r) :
    (QuantileCoupling p q).Ordered := by
  intro i j hm
  by_contra! hlt
  have hp := prefix_le_before_of_lt q.weights.support (fun t _ => q.nonneg t) hlt
  have he := (cumulative_eq_prefix p i.val).symm.le.trans
    ((h i.val).trans (cumulative_eq_prefix q i.val).le)
  change 0 < Overlap _ _ _ _ at hm
  rw [overlap_eq_length (prefix_probability_bounds p i.val).2.1
    (prefix_probability_bounds q j.val).2.1] at hm
  have hmin := min_le_left (Prefix p.weights.support p.weights i.val)
    (Prefix q.weights.support q.weights j.val)
  have hmax := le_max_right (Before p.weights.support p.weights i.val)
    (Before q.weights.support q.weights j.val)
  rw [max_eq_right (sub_nonpos.mpr ((hmin.trans he).trans (hp.trans hmax)))] at hm
  exact (lt_irrefl _ hm)

/-- **Problem 6.5(d):** a nonnegative supplement increases all nondecreasing expected utilities. -/
theorem firstOrder_of_ordered_coupling {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (ho : C.Ordered) : FirstOrderDominates p q := by
  intro U hi
  rw [← C.first_marginal, ← C.second_marginal]
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  rintro ⟨i, j⟩ _
  change C.mass i j * U j.val ≤ C.mass i j * U i.val
  rcases (C.nonneg i j).eq_or_lt with he | hpos
  · simp [← he]
  · exact mul_le_mul_of_nonneg_left (hi (ho i j hpos)) hpos.le

/-- **Proposition 6.14(a):** first-order dominance iff the cumulative probabilities are ordered. -/
theorem proposition_6_14a (p q : SimpleLottery ℝ) :
    FirstOrderDominates p q ↔ ∀ r, Cumulative p r ≤ Cumulative q r :=
  ⟨cumulative_le_of_firstOrder, fun h =>
    firstOrder_of_ordered_coupling _ (quantileCoupling_ordered h)⟩

/-- **Proposition 6.15(a):** first-order dominance iff there is a common ordered coupling. -/
theorem proposition_6_15a (p q : SimpleLottery ℝ) :
    FirstOrderDominates p q ↔ ∃ C : FiniteCoupling p q, C.Ordered :=
  ⟨fun h => ⟨QuantileCoupling p q, quantileCoupling_ordered ((proposition_6_14a p q).mp h)⟩,
    fun ⟨C, hc⟩ => firstOrder_of_ordered_coupling C hc⟩

/-- Intersections of the two inverse-CDF bins give the actual joint law under the same uniform
draw, including atoms shared by the two marginal laws. -/
theorem quantile_uniform_joint_mass (p q : SimpleLottery ℝ)
    (i : p.weights.support) (j : q.weights.support) :
    volume {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = i.val ∧ QuantilePrize q u = j.val} =
      ENNReal.ofReal ((QuantileCoupling p q).mass i j) := by
  have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = i.val ∧ QuantilePrize q u = j.val} =
      QuantileBin p i.val ∩ QuantileBin q j.val := by
    ext u
    constructor
    · rintro ⟨hu, hp, hq⟩
      exact ⟨hp ▸ (quantilePrize_mem_bin p hu).2, hq ▸ (quantilePrize_mem_bin q hu).2⟩
    · rintro ⟨hp, hq⟩
      have hu := quantileBin_subset_unit p _ hp
      exact ⟨hu, quantileBin_unique p (quantilePrize_mem_bin p hu).2 hp,
        quantileBin_unique q (quantilePrize_mem_bin q hu).2 hq⟩
  rw [he, QuantileBin, QuantileBin, Set.Ioc_inter_Ioc, Real.volume_Ioc]
  change _ = ENNReal.ofReal (Overlap _ _ _ _)
  rw [overlap_eq_length (prefix_probability_bounds p _).2.1 (prefix_probability_bounds q _).2.1]
  simp

/-- Ordered CDFs give ordered realized prizes for every common draw in the unit interval. -/
theorem quantilePrize_ordered {p q : SimpleLottery ℝ} (h : ∀ r, Cumulative p r ≤ Cumulative q r)
    {u : ℝ} (hu : u ∈ Set.Ioc 0 1) : QuantilePrize q u ≤ QuantilePrize p u := by
  have hp := (quantilePrize_mem_bin p hu).2
  have hq := (quantilePrize_mem_bin q hu).2
  by_contra! hlt
  have he := prefix_le_before_of_lt q.weights.support (fun t _ => q.nonneg t) hlt
  have hc := (cumulative_eq_prefix p _).symm.le.trans
    ((h (QuantilePrize p u)).trans (cumulative_eq_prefix q _).le)
  exact (not_lt_of_ge (hp.2.trans (hc.trans he))) hq.1

end Kreps.UtilityForMoney
