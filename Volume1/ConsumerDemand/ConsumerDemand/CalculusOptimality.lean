/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem
import ConsumerDemand.ConstrainedOptimization
import ConsumerDemand.LinearBudgetMultipliers
import ConsumerDemand.ConcaveSupport

/-!
# Calculus conditions for the consumer's problem

Kreps I, Definition 3.4 and Proposition 3.5, pp. 57-62. The derivative is taken
within the nonnegative orthant. Its values on the coordinate directions are the
right-hand marginal utilities, including at boundary bundles. Values of the
utility outside the orthant play no role and need not form a smooth extension.

Necessity reduces the derivative's first-order inequalities to a finite linear
budget problem. Sufficiency uses the concave supporting inequality. The compact
conditions are also equivalent to the full nonnegative-multiplier conditions.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal BigOperators

/-- The derivative's marginal value in the direction of one additional unit of good `j`. -/
def MarginalUtility {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ) (j : Fin k) : ℝ :=
  D (Pi.single j 1)

/-- **Definition 3.4:** feasibility, marginal inequalities, and complementary slackness. -/
def CombinedOptimality {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) (m : Fin k → ℝ) : Prop :=
  x ∈ BudgetSet p y ∧ ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j ≤ l * p.val j) ∧
    (∀ j, 0 < x.val j → m j = l * p.val j) ∧
    (Expenditure p x < (y : ℝ) → l = 0)

/-- The book's optimality conditions evaluated at the actual within-domain derivative. -/
def OptimalityConditions {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) (D : (Fin k → ℝ) →L[ℝ] ℝ) : Prop :=
  CombinedOptimality p y x (MarginalUtility D)

/-- The same budget region expressed in the ambient vector space for within-domain calculus. -/
def BudgetVectors {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) : Set (Fin k → ℝ) :=
  {z | 0 ≤ z ∧ ∑ j, p.val j * z j ≤ (y : ℝ)}

/-- A subtype bundle is feasible exactly when its coordinate vector is in the ambient budget. -/
theorem mem_budgetVectors_val {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) : x.val ∈ BudgetVectors p y ↔ x ∈ BudgetSet p y := by
  exact ⟨And.right, fun hx => ⟨x.property, hx⟩⟩

/-- Ambient budget vectors form a convex set, including its nonnegative boundary. -/
theorem budgetVectors_convex {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    Convex ℝ (BudgetVectors p y) := by
  intro x hx z hz a b ha hb hab
  refine ⟨(convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) hx.1 hz.1 ha hb hab, ?_⟩
  change (∑ j, p.val j * (a * x j + b * z j)) ≤ (y : ℝ)
  have he : (∑ j, p.val j * (a * x j + b * z j)) =
      a * (∑ j, p.val j * x j) + b * (∑ j, p.val j * z j) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he]
  have hxa := mul_le_mul_of_nonneg_left hx.2 ha
  have hzb := mul_le_mul_of_nonneg_left hz.2 hb
  nlinarith

/-- A linear derivative is the scalar product of its coordinate marginals with the direction. -/
theorem derivative_coordinate_expansion {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ)
    (z : Fin k → ℝ) : D z = ∑ j, MarginalUtility D j * z j := by
  classical
  have hz : z = ∑ j, z j • (Pi.single j 1 : Fin k → ℝ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    D z = D (∑ j, z j • (Pi.single j 1 : Fin k → ℝ)) := congrArg D hz
    _ = ∑ j, MarginalUtility D j * z j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [MarginalUtility, map_smul, mul_comm]

/-- Within-orthant derivatives give the actual right-hand coordinate marginal at every bundle. -/
theorem marginalUtility_right_derivative {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} {x : NonnegativeOrthant k}
    (hd : HasFDerivWithinAt u D (Ici 0) x.val) (j : Fin k) :
    HasDerivWithinAt (fun t : ℝ => u (x.val + t • Pi.single j 1))
      (MarginalUtility D j) (Ici 0) 0 := by
  have hp : HasDerivAt (fun t : ℝ => x.val + t • (Pi.single j 1 : Fin k → ℝ))
      (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single j 1 : Fin k → ℝ)).const_add x.val
  have hm : MapsTo (fun t : ℝ => x.val + t • (Pi.single j 1 : Fin k → ℝ))
      (Ici 0) (Ici 0) := by
    intro t ht i
    apply add_nonneg (x.property i)
    change 0 ≤ t * (Pi.single j 1 : Fin k → ℝ) i
    apply mul_nonneg ht
    by_cases hij : i = j <;> simp [hij]
  exact hd.comp_hasDerivWithinAt_of_eq 0 hp.hasDerivWithinAt hm (by simp)

/-- The compact conditions are equivalent to vanishing multiplier-slack products. -/
theorem combinedOptimality_iff_complementarity {k : ℕ} (p : PositivePrices k)
    (y : ℝ≥0) (x : NonnegativeOrthant k) (m : Fin k → ℝ) :
    CombinedOptimality p y x m ↔
      x ∈ BudgetSet p y ∧ ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j ≤ l * p.val j) ∧
        (∀ j, (l * p.val j - m j) * x.val j = 0) ∧
        l * ((y : ℝ) - Expenditure p x) = 0 := by
  constructor
  · rintro ⟨hx, l, hl, hm, heq, hslack⟩
    refine ⟨hx, l, hl, hm, ?_, ?_⟩
    · intro j
      by_cases hj : x.val j = 0
      · simp [hj]
      · rw [heq j (lt_of_le_of_ne (x.property j) (Ne.symm hj)), sub_self, zero_mul]
    · by_cases hs : Expenditure p x < (y : ℝ)
      · rw [hslack hs, zero_mul]
      · have he : Expenditure p x = (y : ℝ) := le_antisymm hx (le_of_not_gt hs)
        rw [he, sub_self, mul_zero]
  · rintro ⟨hx, l, hl, hm, heq, hslack⟩
    refine ⟨hx, l, hl, hm, ?_, ?_⟩
    · intro j hj
      have he := (mul_eq_zero.mp (heq j)).resolve_right (ne_of_gt hj)
      exact (sub_eq_zero.mp he).symm
    · intro hs
      exact (mul_eq_zero.mp hslack).resolve_right (ne_of_gt (sub_pos.mpr hs))

/-- The full Lagrangian conditions use nonnegative budget and commodity multipliers. -/
theorem combinedOptimality_iff_lagrangian {k : ℕ} (p : PositivePrices k)
    (y : ℝ≥0) (x : NonnegativeOrthant k) (m : Fin k → ℝ) :
    CombinedOptimality p y x m ↔
      x ∈ BudgetSet p y ∧ ∃ (l : ℝ) (μ : Fin k → ℝ), 0 ≤ l ∧
        (∀ j, 0 ≤ μ j) ∧ (∀ j, m j - l * p.val j + μ j = 0) ∧
        (∀ j, μ j * x.val j = 0) ∧ l * ((y : ℝ) - Expenditure p x) = 0 := by
  rw [combinedOptimality_iff_complementarity]
  constructor
  · rintro ⟨hx, l, hl, hm, hg, hs⟩
    exact ⟨hx, l, fun j => l * p.val j - m j, hl,
      fun j => sub_nonneg.mpr (hm j), fun j => by ring, hg, hs⟩
  · rintro ⟨hx, l, μ, hl, hμ, hm, hg, hs⟩
    have he (j) : μ j = l * p.val j - m j := by linarith [hm j]
    refine ⟨hx, l, hl, ?_, ?_, hs⟩
    · intro j
      linarith [hμ j, hm j]
    · intro j
      rw [← he j]
      exact hg j

/-- **Proposition 3.5(a):** every positive-income optimum satisfies the calculus conditions. -/
theorem proposition_3_5a {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) {x : NonnegativeOrthant k}
    (hd : HasFDerivWithinAt u D (Ici 0) x.val)
    (hx : x ∈ MarshallianDemand (fun z => u z.val) p y) :
    OptimalityConditions p y x D := by
  have hmax : IsMaxOn u (BudgetVectors p y) x.val := by
    intro z hz
    exact hx.2 ⟨z, hz.1⟩ hz.2
  have hfirst := convex_firstOrderNecessary hmax hd (fun _ hz => hz.1)
    (budgetVectors_convex p y) ((mem_budgetVectors_val p y x).mpr hx.1)
  have hlinear : ∀ z : Fin k → ℝ, (∀ j, 0 ≤ z j) →
      (∑ j, p.val j * z j ≤ (y : ℝ)) →
      (∑ j, MarginalUtility D j * z j) ≤ ∑ j, MarginalUtility D j * x.val j := by
    intro z hz hb
    have he := hfirst z ⟨hz, hb⟩
    rw [map_sub, derivative_coordinate_expansion, derivative_coordinate_expansion] at he
    exact sub_nonpos.mp he
  apply (combinedOptimality_iff_complementarity p y x (MarginalUtility D)).mpr
  exact ⟨hx.1, linear_budget_multipliers p.val (MarginalUtility D) x.val (y : ℝ)
    p.property hy x.property hx.1 hlinear⟩

/-- The optimality conditions make the derivative largest at the candidate over its budget. -/
theorem optimalityConditions_firstOrder {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {D : (Fin k → ℝ) →L[ℝ] ℝ}
    (ho : OptimalityConditions p y x D) :
    ∀ z ∈ BudgetVectors p y, D (z - x.val) ≤ 0 := by
  obtain ⟨_, l, hl, hm, hg, hs⟩ :=
    (combinedOptimality_iff_complementarity p y x (MarginalUtility D)).mp ho
  have hprod (j) : MarginalUtility D j * x.val j = (l * p.val j) * x.val j := by
    have h := hg j
    nlinarith
  have hxsum : (∑ j, MarginalUtility D j * x.val j) = l * (y : ℝ) := by
    calc
      (∑ j, MarginalUtility D j * x.val j) = l * Expenditure p x := by
        simp_rw [hprod]
        simp [Expenditure, Finset.mul_sum, mul_assoc]
      _ = l * (y : ℝ) := by nlinarith
  intro z hz
  rw [map_sub, derivative_coordinate_expansion, derivative_coordinate_expansion, hxsum]
  apply sub_nonpos.mpr
  calc
    (∑ j, MarginalUtility D j * z j) ≤ ∑ j, (l * p.val j) * z j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (hz.1 j))
    _ = l * (∑ j, p.val j * z j) := by simp [Finset.mul_sum, mul_assoc]
    _ ≤ l * (y : ℝ) := mul_le_mul_of_nonneg_left hz.2 hl

/-- **Proposition 3.5(b):** the calculus conditions suffice for a concave utility maximum. -/
theorem proposition_3_5b {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} (hu : ConcaveOn ℝ (Ici 0) u)
    (hd : HasFDerivWithinAt u D (Ici 0) x.val) (ho : OptimalityConditions p y x D) :
    x ∈ MarshallianDemand (fun z => u z.val) p y := by
  have hmax := concave_firstOrderSufficient hu hd (fun _ hz => hz.1)
    ((mem_budgetVectors_val p y x).mpr ho.1) (optimalityConditions_firstOrder ho)
  refine ⟨ho.1, ?_⟩
  intro z hz
  exact hmax ((mem_budgetVectors_val p y z).mpr hz)

end Kreps.ConsumerDemand
