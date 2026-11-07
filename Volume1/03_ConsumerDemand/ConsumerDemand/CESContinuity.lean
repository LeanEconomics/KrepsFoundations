/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CESDemand
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of CES utility at the axes

Kreps I, Problem 3.7, pp. 64-65. Negative powers are evaluated only at positive
coordinates in the interior formula. Its zero extension at an axis is continuous:
utility is bounded above by a positive constant times every coordinate. Thus the
full-domain demand theorem does not rely on the value of `Real.rpow` at zero
for a negative exponent.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators Topology
open Filter

/-- CES utility is nonnegative on the entire consumption domain. -/
theorem cesUtility_nonneg {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (x : NonnegativeOrthant k) : 0 ≤ CESUtility a mu x := by
  unfold CESUtility
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (cesPowerSum_nonneg a ha mu x) _

/-- A negative-exponent CES utility vanishes whenever a commodity is absent. -/
theorem cesUtility_zero_of_coordinate {k : ℕ} (a : Fin k → ℝ) {mu : ℝ}
    (hmu : mu < 0) {x : NonnegativeOrthant k} {j : Fin k} (hj : x.val j = 0) :
    CESUtility a mu x = 0 := by
  have hb : mu < 0 ∧ ∃ i, x.val i = 0 := ⟨hmu, j, hj⟩
  simp only [CESUtility, ite_eq_left hb]

/-- Each coordinate provides a linear upper bound for negative-exponent CES utility. -/
theorem cesUtility_le_coordinate {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 0) (x : NonnegativeOrthant k) (j : Fin k) :
    CESUtility a mu x ≤ a j ^ (1 / mu) * x.val j := by
  by_cases hb : ∃ i, x.val i = 0
  · obtain ⟨i, hi⟩ := hb
    rw [cesUtility_zero_of_coordinate a hmu hi]
    exact mul_nonneg (Real.rpow_pos_of_pos (ha j) _).le (x.property j)
  have hx : ∀ i, 0 < x.val i := fun i =>
    lt_of_le_of_ne (x.property i) (fun he => hb ⟨i, he.symm⟩)
  rw [cesUtility_of_positive a mu hx]
  have hterm : a j * x.val j ^ mu ≤ CESPowerSum a mu x :=
    Finset.single_le_sum (fun i _ =>
      mul_nonneg (ha i).le (Real.rpow_nonneg (x.property i) _)) (Finset.mem_univ j)
  calc
    CESPowerSum a mu x ^ (1 / mu) ≤ (a j * x.val j ^ mu) ^ (1 / mu) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _))
        hterm (one_div_neg.mpr hmu).le
    _ = a j ^ (1 / mu) * x.val j := by
      rw [Real.mul_rpow (ha j).le (Real.rpow_nonneg (x.property j) _),
        ← Real.rpow_mul (x.property j)]
      simp [hmu.ne]

/-- At an interior point the power sum is continuous for any real exponent. -/
theorem cesPowerSum_continuousAt_interior {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    ContinuousAt (CESPowerSum a mu) x := by
  have hc (j : Fin k) : ContinuousAt (fun z : NonnegativeOrthant k => z.val j ^ mu) x :=
    (((continuous_apply j).comp continuous_subtype_val).continuousAt).rpow_const
      (Or.inl (hx j).ne')
  unfold CESPowerSum
  fun_prop

/-- The full-domain CES formula is continuous at every strictly positive bundle. -/
theorem cesUtility_continuousAt_interior {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    ContinuousAt (CESUtility a mu) x := by
  have hc := (cesPowerSum_continuousAt_interior a mu hx).rpow_const (p := 1 / mu)
    (Or.inl (cesPowerSum_pos a ha mu hx).ne')
  apply hc.congr
  have he : ∀ᶠ z : NonnegativeOrthant k in 𝓝 x, ∀ j, 0 < z.val j := by
    apply eventually_all.mpr
    intro j
    exact (isOpen_lt continuous_const ((continuous_apply j).comp continuous_subtype_val)).mem_nhds
      (hx j)
  filter_upwards [he] with z hz
  exact (cesUtility_of_positive a mu hz).symm

/-- The negative-exponent boundary extension is continuous at every absent commodity. -/
theorem cesUtility_continuousAt_boundary {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 0) {x : NonnegativeOrthant k} {j : Fin k} (hj : x.val j = 0) :
    ContinuousAt (CESUtility a mu) x := by
  have hc : Continuous (fun z : NonnegativeOrthant k => a j ^ (1 / mu) * z.val j) :=
    continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  have hl : Tendsto (fun z : NonnegativeOrthant k => a j ^ (1 / mu) * z.val j)
      (𝓝 x) (𝓝 0) := by simpa only [hj, mul_zero] using hc.tendsto x
  change Tendsto (CESUtility a mu) (𝓝 x) (𝓝 (CESUtility a mu x))
  rw [cesUtility_zero_of_coordinate a hmu hj]
  exact squeeze_zero (cesUtility_nonneg a ha mu)
    (fun z => cesUtility_le_coordinate a ha hmu z j) hl

/-- CES utility is continuous on the full orthant for every nonzero real exponent. -/
theorem cesUtility_continuous {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hm0 : mu ≠ 0) : Continuous (CESUtility a mu) := by
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hb : ∃ j, x.val j = 0
    · obtain ⟨j, hj⟩ := hb
      exact cesUtility_continuousAt_boundary a ha hm hj
    · exact cesUtility_continuousAt_interior a ha mu
        (fun j => lt_of_le_of_ne (x.property j) (fun he => hb ⟨j, he.symm⟩))
  · have he : CESUtility a mu = fun x => CESPowerSum a mu x ^ (1 / mu) := by
      funext x
      simp [CESUtility, not_lt_of_ge hm.le]
    rw [he]
    apply Continuous.rpow_const _ (fun _ => Or.inr (one_div_pos.mpr hm).le)
    have hc (j : Fin k) : Continuous (fun x : NonnegativeOrthant k => x.val j ^ mu) :=
      (Real.continuous_rpow_const hm.le).comp
        ((continuous_apply j).comp continuous_subtype_val)
    unfold CESPowerSum
    fun_prop

end Kreps.ConsumerDemand
