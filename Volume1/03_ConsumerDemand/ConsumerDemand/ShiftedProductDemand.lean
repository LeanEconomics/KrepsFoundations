/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.LogarithmicSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shifted Cobb-Douglas utility, including zero boundary factors

Kreps I, pp. 59-60 and Problems 3.3 and 3.5, p. 64. Positive exponents make
the product zero if any shifted consumption is zero. Elsewhere, its logarithm
is exactly the weighted sum of logarithms. Consequently the logarithmic
conditions characterize a unique product-utility optimum on the full orthant,
without asserting concavity of the original unnormalized product.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The shifted Cobb-Douglas product with real exponents. -/
noncomputable def ShiftedCobbDouglas {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∏ j, (x.val j + γ j) ^ a j

/-- Positive shifted quantities make the product strictly positive. -/
theorem shiftedCobbDouglas_pos {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j) :
    0 < ShiftedCobbDouglas a γ x :=
  Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) (a j))

/-- A zero shifted quantity makes the product zero when its exponent is positive. -/
theorem shiftedCobbDouglas_eq_zero {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) (ha : 0 < a j)
    (hx : x.val j + γ j = 0) : ShiftedCobbDouglas a γ x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hx, Real.zero_rpow (ne_of_gt ha)]

/-- On the positive-argument region, logarithms give the weighted-log utility exactly. -/
theorem log_shiftedCobbDouglas {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j) :
    Real.log (ShiftedCobbDouglas a γ x) = ShiftedLogUtility a γ x := by
  rw [ShiftedCobbDouglas, Real.log_prod
    (fun j _ => ne_of_gt (Real.rpow_pos_of_pos (hx j) (a j)))]
  exact Finset.sum_congr rfl (fun j _ => Real.log_rpow (hx j) (a j))

/-- Logarithmic optimality yields strict product-utility optimality, including boundary rivals. -/
theorem shiftedCobbDouglas_strict_optimality {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y) (hne : z ≠ x) :
    ShiftedCobbDouglas a γ z < ShiftedCobbDouglas a γ x := by
  by_cases hpos : ∀ j, 0 < z.val j + γ j
  · apply (Real.log_lt_log_iff (shiftedCobbDouglas_pos a γ z hpos)
      (shiftedCobbDouglas_pos a γ x hx)).mp
    rw [log_shiftedCobbDouglas a γ z hpos, log_shiftedCobbDouglas a γ x hx]
    exact shiftedLog_strict_optimality a γ ha hx ho hz hpos hne
  · push Not at hpos
    obtain ⟨j, hj⟩ := hpos
    have hzero : z.val j + γ j = 0 := le_antisymm hj (add_nonneg (z.property j) (hγ j))
    rw [shiftedCobbDouglas_eq_zero a γ z j (ha j) hzero]
    exact shiftedCobbDouglas_pos a γ x hx

/-- The positive-argument candidate is the unique full-domain product-utility optimum. -/
theorem shiftedCobbDouglas_demand_of_optimality {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x)) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y = {x} := by
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (not_lt_of_ge (hz.2 x ho.1))
      (shiftedCobbDouglas_strict_optimality a γ ha hγ hx ho hz.1 hne)
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨ho.1, fun w hw => ?_⟩
    change ShiftedCobbDouglas a γ w ≤ ShiftedCobbDouglas a γ x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedCobbDouglas_strict_optimality a γ ha hγ hx ho hw he).le

end Kreps.ConsumerDemand
