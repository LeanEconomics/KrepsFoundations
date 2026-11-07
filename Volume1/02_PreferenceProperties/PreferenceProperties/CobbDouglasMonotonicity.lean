/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Homotheticity
import PreferenceProperties.Monotonicity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Cobb-Douglas monotonicity and boundary failures

Kreps I, p. 32. Positive exponents give strict improvement when all coordinates
increase, and strict product-order monotonicity on the positive orthant. With
at least two goods, points on a coordinate axis give a counterexample to strict
monotonicity on the whole nonnegative orthant.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ}

/-- The finite-dimensional Cobb-Douglas utility in the p. 32 example. -/
noncomputable def CobbDouglasUtility (α : Fin k → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  ∏ j, (x.val j) ^ (α j)

/-- Every factor, and hence the product, is nonnegative on the orthant. -/
theorem cobbDouglasUtility_nonneg (α : Fin k → ℝ) (x : NonnegativeOrthant k) :
    0 ≤ CobbDouglasUtility α x :=
  Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (x.property j) _)

/-- Positive consumption of every good makes the product strictly positive. -/
theorem cobbDouglasUtility_pos (α : Fin k → ℝ) {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j) : 0 < CobbDouglasUtility α x :=
  Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) _)

/-- A zero coordinate with nonzero exponent makes the entire product zero. -/
theorem cobbDouglasUtility_zero_coordinate {α : Fin k → ℝ} {x : NonnegativeOrthant k}
    {j : Fin k} (hα : α j ≠ 0) (hx : x.val j = 0) : CobbDouglasUtility α x = 0 := by
  unfold CobbDouglasUtility
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hx, Real.zero_rpow hα]

/-- With a positive number of goods and positive exponents, utility at the origin is zero. -/
theorem cobbDouglasUtility_origin [NeZero k] {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    CobbDouglasUtility α (OrthantZero k) = 0 :=
  cobbDouglasUtility_zero_coordinate (j := 0) (ne_of_gt (hα 0)) rfl

/-- Nonnegative exponents give weak product-order monotonicity. -/
theorem cobbDouglasUtility_monotone {α : Fin k → ℝ} (hα : ∀ j, 0 ≤ α j) :
    Monotone (CobbDouglasUtility α) := by
  intro x y hxy
  exact Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (x.property j) _)
    (fun j _ => Real.rpow_le_rpow (x.property j) (hxy j) (hα j))

/-- A nontrivial coordinatewise increase from a positive bundle strictly increases utility. -/
theorem cobbDouglasUtility_strict_of_positive {α : Fin k → ℝ} (hα : ∀ j, 0 < α j)
    {x y : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) (hxy : x < y) :
    CobbDouglasUtility α x < CobbDouglasUtility α y := by
  have hex : ∃ j, x.val j < y.val j := by
    by_contra hn
    push Not at hn
    exact hxy.ne (Subtype.ext (funext (fun j => le_antisymm (hxy.le j) (hn j))))
  obtain ⟨j, hj⟩ := hex
  exact Finset.prod_lt_prod₀ (fun i _ => Real.rpow_pos_of_pos (hx i) _)
    (fun i _ => Real.rpow_le_rpow (x.property i) (hxy.le i) (hα i).le)
    ⟨j, Finset.mem_univ j, Real.rpow_lt_rpow (x.property j) hj (hα j)⟩

/-- This gives strict monotonicity away from all coordinate axes. -/
theorem cobbDouglasUtility_strictMonoOn_positive {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    StrictMonoOn (CobbDouglasUtility α) {x : NonnegativeOrthant k | ∀ j, 0 < x.val j} :=
  fun _ hx _ _ hxy => cobbDouglasUtility_strict_of_positive hα hx hxy

/-- Strict increases in every commodity improve preference, including from boundary bundles. -/
theorem cobbDouglasPreference_strictAllIncrease [NeZero k] {α : Fin k → ℝ}
    (hα : ∀ j, 0 < α j) : StrictAllIncreasePreference (UtilityPref (CobbDouglasUtility α)) := by
  intro x y hxy
  have hu : Represents (CobbDouglasUtility α) (UtilityPref (CobbDouglasUtility α)) :=
    fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ _).mpr
  by_cases hy : ∀ j, 0 < y.val j
  · apply cobbDouglasUtility_strict_of_positive hα hy
    apply lt_of_le_of_ne (fun j => (hxy j).le)
    intro he
    exact (ne_of_lt (hxy 0)) (congrArg (fun z : NonnegativeOrthant k => z.val 0) he)
  · push Not at hy
    obtain ⟨j, hj⟩ := hy
    rw [cobbDouglasUtility_zero_coordinate (ne_of_gt (hα j))
      (le_antisymm hj (y.property j))]
    exact cobbDouglasUtility_pos α (fun i => (y.property i).trans_lt (hxy i))

/-- With at least two goods, increasing one coordinate on an axis leaves utility zero. -/
theorem cobbDouglasPreference_not_strictlyMonotone (hk : 2 ≤ k) {α : Fin k → ℝ}
    (hα : ∀ j, 0 < α j) : ¬StrictlyMonotonePreference (UtilityPref (CobbDouglasUtility α)) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  let y : NonnegativeOrthant k :=
    ⟨Function.update (0 : Fin k → ℝ) i 1, fun a => by
      simp only [Function.update_apply]
      split_ifs <;> norm_num⟩
  have hyj : y.val j = 0 := by simp [y, i, j]
  have hy : CobbDouglasUtility α y = 0 :=
    cobbDouglasUtility_zero_coordinate (ne_of_gt (hα j)) hyj
  have hz : CobbDouglasUtility α (OrthantZero k) = 0 :=
    cobbDouglasUtility_zero_coordinate (j := j) (ne_of_gt (hα j)) rfl
  have hne : y ≠ OrthantZero k := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant k => z.val i) h
    simp [y, OrthantZero] at he
  intro h
  apply (h y (OrthantZero k) y.property hne).2
  change CobbDouglasUtility α y ≤ CobbDouglasUtility α (OrthantZero k)
  rw [hy, hz]

/-- The p. 32 Cobb-Douglas example, with the dimension needed for its boundary counterexample. -/
theorem cobbDouglasUtility_example (hk : 2 ≤ k) {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    MonotonePreference (UtilityPref (CobbDouglasUtility α)) ∧
      StrictAllIncreasePreference (UtilityPref (CobbDouglasUtility α)) ∧
      LocallyInsatiable (UtilityPref (CobbDouglasUtility α)) ∧
      ¬StrictlyMonotonePreference (UtilityPref (CobbDouglasUtility α)) ∧
      StrictMonoOn (CobbDouglasUtility α) {x : NonnegativeOrthant k | ∀ j, 0 < x.val j} := by
  let : NeZero k := ⟨by omega⟩
  have hu : Represents (CobbDouglasUtility α) (UtilityPref (CobbDouglasUtility α)) :=
    fun _ _ => Iff.rfl
  have hs := cobbDouglasPreference_strictAllIncrease hα
  exact ⟨(proposition_2_2_monotone hu).mpr (cobbDouglasUtility_monotone (fun j => (hα j).le)),
    hs, strictAllIncrease_locallyInsatiable hs,
    cobbDouglasPreference_not_strictlyMonotone hk hα,
    cobbDouglasUtility_strictMonoOn_positive hα⟩

end Kreps.PreferenceProperties
