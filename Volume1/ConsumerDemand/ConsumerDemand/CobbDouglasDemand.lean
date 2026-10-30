/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ShiftedProductDemand
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Full-domain Cobb-Douglas demand

Kreps I, pp. 59-60. Each good receives its exponent's share of total expenditure.
The proof uses the strictly increasing logarithmic transformation only where
all coordinates are positive and treats zero boundary factors separately.
There is no normalization assumption on the sum of exponents and no finite
derivative assumption at the boundary. Zero income is included explicitly.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The ordinary, unshifted Cobb-Douglas utility on the full nonnegative orthant. -/
noncomputable def CobbDouglas {k : ℕ} (a : Fin k → ℝ) : NonnegativeOrthant k → ℝ :=
  ShiftedCobbDouglas a 0

/-- Positive powers make Cobb-Douglas continuous even at zero coordinates. -/
theorem cobbDouglas_continuous {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    Continuous (CobbDouglas a) := by
  unfold CobbDouglas ShiftedCobbDouglas
  apply continuous_finsetProd
  intro j _
  exact (Real.continuous_rpow_const (ha j).le).comp
    (((continuous_apply j).comp continuous_subtype_val).add continuous_const)

/-- The total exponent is strictly positive in a nonempty commodity space. -/
theorem exponent_sum_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    0 < ∑ j, a j := Finset.sum_pos (fun j _ => ha j) Finset.univ_nonempty

/-- The Cobb-Douglas expenditure-share formula. -/
noncomputable def CobbDouglasBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) : NonnegativeOrthant k :=
  ⟨fun j => (a j / ∑ i, a i) * ((y : ℝ) / p.val j), fun j =>
    mul_nonneg (div_pos (ha j) (exponent_sum_pos a ha)).le
      (div_nonneg y.property (p.property j).le)⟩

/-- At positive income every coordinate of Cobb-Douglas demand is strictly positive. -/
theorem cobbDouglasBundle_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (j : Fin k) : 0 < (CobbDouglasBundle a ha p y).val j :=
  mul_pos (div_pos (ha j) (exponent_sum_pos a ha)) (div_pos hy (p.property j))

/-- The expenditure-share formula exhausts income. -/
theorem expenditure_cobbDouglasBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (CobbDouglasBundle a ha p y) = (y : ℝ) := by
  have hterm (j : Fin k) :
      p.val j * (CobbDouglasBundle a ha p y).val j = a j * ((y : ℝ) / ∑ i, a i) := by
    dsimp only [CobbDouglasBundle]
    field_simp [ne_of_gt (p.property j)]
  simp only [Expenditure, hterm, ← Finset.sum_mul]
  exact mul_div_cancel₀ _ (ne_of_gt (exponent_sum_pos a ha))

/-- At positive income, the logarithmic marginal equals total exponent over income times price. -/
theorem cobbDouglasBundle_logMarginals {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (j : Fin k) :
    LogMarginals a 0 (CobbDouglasBundle a ha p y) j = ((∑ i, a i) / (y : ℝ)) * p.val j := by
  dsimp only [LogMarginals, CobbDouglasBundle, Pi.zero_apply]
  simp only [add_zero]
  field_simp [ne_of_gt (ha j), ne_of_gt (p.property j), ne_of_gt hy,
    ne_of_gt (exponent_sum_pos a ha)]

/-- The explicit bundle satisfies all logarithmic optimality conditions. -/
theorem cobbDouglasBundle_optimality {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    CombinedOptimality p y (CobbDouglasBundle a ha p y)
      (LogMarginals a 0 (CobbDouglasBundle a ha p y)) := by
  refine ⟨(expenditure_cobbDouglasBundle a ha p y).le, (∑ i, a i) / (y : ℝ),
    (div_pos (exponent_sum_pos a ha) hy).le, ?_, ?_, ?_⟩
  · intro j
    exact (cobbDouglasBundle_logMarginals a ha p y hy j).le
  · intro j _
    exact cobbDouglasBundle_logMarginals a ha p y hy j
  · rw [expenditure_cobbDouglasBundle]
    exact fun h => False.elim (lt_irrefl _ h)

/-- The expenditure-share formula is the unique demand at positive income. -/
theorem cobbDouglas_demand_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    MarshallianDemand (CobbDouglas a) p y = {CobbDouglasBundle a ha p y} := by
  exact shiftedCobbDouglas_demand_of_optimality a 0 ha (fun _ => le_rfl)
    (fun j => by simpa using cobbDouglasBundle_pos a ha p y hy j)
    (cobbDouglasBundle_optimality a ha p y hy)

/-- The expenditure-share formula becomes the origin at zero income. -/
theorem cobbDouglasBundle_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) :
    CobbDouglasBundle a ha p 0 = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [CobbDouglasBundle, ZeroBundle]

/-- The full Cobb-Douglas demand formula of pp. 59-60, for every nonnegative income. -/
theorem cobbDouglas_demand {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (CobbDouglas a) p y = {CobbDouglasBundle a ha p y} := by
  by_cases hy : 0 < (y : ℝ)
  · exact cobbDouglas_demand_pos a ha p y hy
  · have hzero : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
    subst y
    rw [marshallianDemand_zero, cobbDouglasBundle_zero]

/-- The source's interiority assertion follows for every full-domain optimum. -/
theorem cobbDouglas_demand_positive {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {x : NonnegativeOrthant k} (hx : x ∈ MarshallianDemand (CobbDouglas a) p y) :
    ∀ j, 0 < x.val j := by
  rw [cobbDouglas_demand a ha p y, Set.mem_singleton_iff] at hx
  subst x
  exact cobbDouglasBundle_pos a ha p y hy

end Kreps.ConsumerDemand
