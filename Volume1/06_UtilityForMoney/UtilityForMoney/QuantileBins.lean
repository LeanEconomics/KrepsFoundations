/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.StochasticDominance
import Mathlib.Data.Finset.Max

/-!
# Finite cumulative probabilities and inverse-CDF bins

Kreps I, Problem 6.5(b), pp. 141–142. A support point occupies the interval
from its left limit (excluded) to its cumulative mass (included). The ordered
finite sum below establishes coverage, including the final endpoint one.
-/

namespace Kreps.UtilityForMoney

/-- Finite cumulative sum including a possible atom at the upper endpoint. -/
noncomputable def Prefix (s : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ t ∈ s, if t ≤ x then w t else 0

/-- Finite cumulative sum strictly before the upper endpoint. -/
noncomputable def Before (s : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ t ∈ s, if t < x then w t else 0

/-- The threshold-indicator expectation is the sum of the corresponding point masses. -/
theorem cumulative_eq_prefix (p : SimpleLottery ℝ) (x : ℝ) :
    Cumulative p x = Prefix p.weights.support p.weights x := by
  simp [Cumulative, Prefix, ExpectedUtility, Finsupp.sum, mul_ite]

/-- The jump of the cumulative sum is exactly the included point mass. -/
theorem prefix_sub_before {s : Finset ℝ} (w : ℝ → ℝ) {x : ℝ} (hx : x ∈ s) :
    Prefix s w x - Before s w x = w x := by
  rw [Prefix, Before, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · simp
  · intro t _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h.le, h]
    · simp [h.not_ge, h.not_gt]
  · simp [hx]

/-- Bins of two different ordered prizes do not overlap. -/
theorem prefix_le_before_of_lt (s : Finset ℝ) {w : ℝ → ℝ} (hn : ∀ i ∈ s, 0 ≤ w i)
    {x y : ℝ} (hxy : x < y) : Prefix s w x ≤ Before s w y := by
  apply Finset.sum_le_sum
  intro t ht
  split_ifs <;> first | exact le_rfl | exact hn t ht | linarith

/-- The cumulative sums in a probability law lie between zero and one. -/
theorem prefix_probability_bounds (p : SimpleLottery ℝ) (t : ℝ) :
    0 ≤ Before p.weights.support p.weights t ∧
      Before p.weights.support p.weights t ≤ Prefix p.weights.support p.weights t ∧
      Prefix p.weights.support p.weights t ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), Finset.sum_le_sum (fun i _ => ?_), ?_⟩
  · split_ifs <;> simp
  · split_ifs <;> first | exact le_rfl | exact p.nonneg i | linarith
  · rw [← p.total]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact le_rfl | exact p.nonneg i

/-- A sum of increments over all adjacent cumulative intervals telescopes. -/
theorem sum_prefix_increments (s : Finset ℝ) (w f : ℝ → ℝ) :
    ∑ i ∈ s, (f (Prefix s w i) - f (Before s w i)) = f (∑ i ∈ s, w i) - f 0 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp [Prefix, Before]
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have hp (i : ℝ) (hi : i ∈ s) : Prefix (insert a s) w i = Prefix s w i := by
      simp [Prefix, ha, (hmax i hi).not_ge]
    have hb (i : ℝ) (hi : i ∈ s) : Before (insert a s) w i = Before s w i := by
      simp [Before, ha, (hmax i hi).not_gt]
    have hp' : Prefix (insert a s) w a = w a + ∑ i ∈ s, w i := by
      simp only [Prefix, Finset.sum_insert ha, le_rfl, ite_true]
      congr 1
      exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi).le
    have hb' : Before (insert a s) w a = ∑ i ∈ s, w i := by
      simp only [Before, Finset.sum_insert ha, lt_irrefl, ite_false, zero_add]
      exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi)
    have he : (∑ i ∈ s, (f (Prefix (insert a s) w i) - f (Before (insert a s) w i))) =
        ∑ i ∈ s, (f (Prefix s w i) - f (Before s w i)) := by
      exact Finset.sum_congr rfl fun i hi => by rw [hp i hi, hb i hi]
    rw [Finset.sum_insert ha, hp', hb', Finset.sum_insert ha, he, ih]
    ring

/-- The half-open cumulative bins cover the full cumulative interval. -/
theorem exists_prefix_bin (s : Finset ℝ) (w : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (ht : u ≤ ∑ i ∈ s, w i) :
    ∃ i ∈ s, u ∈ Set.Ioc (Before s w i) (Prefix s w i) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp at ht; linarith
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    by_cases h : u ≤ ∑ i ∈ s, w i
    · obtain ⟨i, hi, hm⟩ := ih h
      refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
      simpa [Before, Prefix, ha, (hmax i hi).not_ge, (hmax i hi).not_gt] using hm
    · refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩
      · have he : Before (insert a s) w a = ∑ i ∈ s, w i := by
          simp only [Before, Finset.sum_insert ha, lt_irrefl, ite_false, zero_add]
          exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi)
        exact he ▸ lt_of_not_ge h
      · have he : Prefix (insert a s) w a = ∑ i ∈ insert a s, w i := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ite_eq_left le_rfl
          · exact ite_eq_left (hmax i hi).le
        exact he ▸ ht

/-- The uniform-probability interval of a monetary prize. -/
noncomputable def QuantileBin (p : SimpleLottery ℝ) (x : ℝ) : Set ℝ :=
  Set.Ioc (Before p.weights.support p.weights x) (Prefix p.weights.support p.weights x)

/-- Choosing the prize of the unique bin implements inverse-CDF sampling on `(0,1]`. -/
noncomputable def QuantilePrize (p : SimpleLottery ℝ) (u : ℝ) : ℝ := by
  classical
  exact if h : ∃ x ∈ p.weights.support, u ∈ QuantileBin p x then h.choose
    else p.weights.support.min' p.support_weights_nonempty

/-- At the zero endpoint of the uniform draw the book assigns the smallest support prize. -/
theorem quantilePrize_zero (p : SimpleLottery ℝ) :
    QuantilePrize p 0 = p.weights.support.min' p.support_weights_nonempty := by
  have hn : ¬ ∃ x ∈ p.weights.support, 0 ∈ QuantileBin p x := by
    rintro ⟨x, _, hx⟩
    exact (not_lt_of_ge (prefix_probability_bounds p x).1) hx.1
  simp only [QuantilePrize, dite_eq_right hn]

/-- Every uniform draw in `(0,1]` lands on a support point and in that point's bin. -/
theorem quantilePrize_mem_bin (p : SimpleLottery ℝ) {u : ℝ} (hu : u ∈ Set.Ioc 0 1) :
    QuantilePrize p u ∈ p.weights.support ∧ u ∈ QuantileBin p (QuantilePrize p u) := by
  have h : ∃ x ∈ p.weights.support, u ∈ QuantileBin p x :=
    exists_prefix_bin _ _ _ hu.1 (by
      change u ≤ p.weights.sum (fun _ a => a)
      rw [p.total]
      exact hu.2)
  simpa only [QuantilePrize, dite_eq_left h] using h.choose_spec

/-- Bins meeting at the same draw have the same prize. -/
theorem quantileBin_unique (p : SimpleLottery ℝ) {u x y : ℝ}
    (hx : u ∈ QuantileBin p x) (hy : u ∈ QuantileBin p y) : x = y := by
  have h {i j : ℝ} := @prefix_le_before_of_lt p.weights.support p.weights
    (fun i _ => p.nonneg i) i j
  rcases lt_trichotomy x y with hxy | he | hyx
  · exact False.elim ((not_lt_of_ge (hx.2.trans (h hxy))) hy.1)
  · exact he
  · exact False.elim ((not_lt_of_ge (hy.2.trans (h hyx))) hx.1)

end Kreps.UtilityForMoney
