/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality

/-!
# One-sided necessary conditions

Kreps I, Problem 3.13, p. 65. Only actual one-sided derivatives are used.
The existence of coordinate partial derivatives does not supply a multivariate
first-order expansion along commodity exchanges.
-/

namespace Kreps.ConsumerDemand

open Set Filter
open scoped Topology NNReal

/-- A right derivative at a one-sided maximum is nonpositive. -/
theorem right_derivative_nonpos {f : ℝ → ℝ} {a d : ℝ}
    (hm : IsLocalMaxOn f (Ici a) a) (hd : HasDerivWithinAt f d (Ici a) a) : d ≤ 0 := by
  have ht : (1 : ℝ) ∈ posTangentConeAt (Ici a) a :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Ici (𝕜 := ℝ) a).segment_subset (by simp) (by simp))
  simpa using hm.hasFDerivWithinAt_nonpos hd ht

/-- A left derivative at a one-sided maximum is nonnegative. -/
theorem left_derivative_nonneg {f : ℝ → ℝ} {a d : ℝ}
    (hm : IsLocalMaxOn f (Iic a) a) (hd : HasDerivWithinAt f d (Iic a) a) : 0 ≤ d := by
  have ht : (-1 : ℝ) ∈ posTangentConeAt (Iic a) a :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Iic (𝕜 := ℝ) a).segment_subset (by simp) (by simp))
  have h := hm.hasFDerivWithinAt_nonpos hd ht
  simpa [UtilityPref] using h

/-- Varying one coordinate gives a continuous expenditure function. -/
theorem coordinate_expenditure_continuous {k : ℕ} (p : PositivePrices k)
    (x : Fin k → ℝ) (j : Fin k) :
    Continuous (fun t : ℝ => ∑ i, p.val i * Function.update x j t i) := by
  apply continuous_finsetSum
  intro i _
  by_cases h : i = j
  · subst i
    convert (continuous_const.mul continuous_id :
      Continuous (fun t : ℝ => p.val j * t)) using 1
    funext t
    simp
  · simp only [Function.update_of_ne h]
    exact continuous_const

/-- Reducing a positive consumed coordinate is locally feasible, regardless of budget slack. -/
theorem demand_coordinate_left_max {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y) (j : Fin k)
    (hx : 0 < x.val j) :
    IsLocalMaxOn (fun t => u (Function.update x.val j t)) (Iic (x.val j)) (x.val j) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hx)] with t ht hpos
  have hn : 0 ≤ Function.update x.val j t := by
    intro i
    by_cases h : i = j
    · subst i
      simpa using hpos.le
    · simpa [Function.update_of_ne h] using x.property i
  have hb : (∑ i, p.val i * Function.update x.val j t i) ≤ (y : ℝ) := by
    apply le_trans _ hm.1
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i = j
    · subst i
      simpa using mul_le_mul_of_nonneg_left ht (p.property j).le
    · simp [Function.update_of_ne h]
  have h := hm.2 ⟨Function.update x.val j t, hn⟩ hb
  simpa [UtilityPref] using h

/-- At slack budgets increasing a coordinate is locally feasible, including at zero. -/
theorem demand_coordinate_right_max {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y) (j : Fin k)
    (hslack : Expenditure p x < (y : ℝ)) :
    IsLocalMaxOn (fun t => u (Function.update x.val j t)) (Ici (x.val j)) (x.val j) := by
  have hc := (coordinate_expenditure_continuous p x.val j).continuousAt (x := x.val j)
  have he : (∑ i, p.val i * Function.update x.val j (x.val j) i) < (y : ℝ) := by
    simpa [Expenditure] using hslack
  have hev := hc.eventually (isOpen_Iio.mem_nhds he)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds hev] with t ht hcost
  have hn : 0 ≤ Function.update x.val j t := by
    intro i
    by_cases h : i = j
    · subst i
      simpa using (x.property j).trans ht
    · simpa [Function.update_of_ne h] using x.property i
  have h := hm.2 ⟨Function.update x.val j t, hn⟩ hcost.le
  simpa [UtilityPref] using h

/-- Any feasible path with an actual right derivative has a nonpositive derivative
at an optimum. No multivariate derivative is inferred from coordinate derivatives. -/
theorem demand_feasible_path_derivative_nonpos {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand u p y) {path : ℝ → NonnegativeOrthant k}
    (hzero : path 0 = x) (hfeas : ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, path t ∈ BudgetSet p y)
    {d : ℝ} (hd : HasDerivWithinAt (fun t => u (path t)) d (Ici 0) 0) : d ≤ 0 := by
  apply right_derivative_nonpos _ hd
  filter_upwards [hfeas] with t ht
  simpa [hzero, UtilityPref] using hm.2 (path t) ht

/-- **Problem 3.13:** necessary coordinate conditions use genuine left and right partials.
At positive quantities the left marginal is nonnegative; at a slack budget every
right marginal is nonpositive. Directional exchange tests are given separately above. -/
theorem problem_3_13 {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y)
    (left right : Fin k → ℝ)
    (hl : ∀ j, 0 < x.val j → HasDerivWithinAt
      (fun t => u (Function.update x.val j t)) (left j) (Iic (x.val j)) (x.val j))
    (hr : ∀ j, HasDerivWithinAt
      (fun t => u (Function.update x.val j t)) (right j) (Ici (x.val j)) (x.val j)) :
    (∀ j, 0 < x.val j → 0 ≤ left j) ∧
      (Expenditure p x < (y : ℝ) → ∀ j, right j ≤ 0) := by
  constructor
  · intro j hj
    exact left_derivative_nonneg (demand_coordinate_left_max hm j hj) (hl j hj)
  · intro hs j
    exact right_derivative_nonpos (demand_coordinate_right_max hm j hs) (hr j)

end Kreps.ConsumerDemand
