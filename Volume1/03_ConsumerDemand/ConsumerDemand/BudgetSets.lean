/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.Prerequisites
import Mathlib.Topology.Order.Compact

/-!
# Budget sets at positive prices

Kreps I, Section 3.1 and the budget-set arguments in Proposition 3.1, pp. 50-54.
Income is nonnegative and every commodity price is strictly positive. Feasibility
uses weak inequalities, so zero consumption and spending exactly the available
income are included. Nonemptiness, coordinate bounds, closedness and convexity
are established before optimizing any utility.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- The strictly positive finite-dimensional price vectors of Section 3.1. -/
abbrev PositivePrices (k : ℕ) := {p : Fin k → ℝ // ∀ j, 0 < p j}

/-- The zero consumption bundle, feasible at every nonnegative income. -/
def ZeroBundle (k : ℕ) : NonnegativeOrthant k := ⟨0, le_rfl⟩

/-- Expenditure at constant unit prices, the finite scalar product `p · x`. -/
def Expenditure {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) : ℝ :=
  ∑ j, p.val j * x.val j

/-- The budget-feasible bundles at a strictly positive price vector and nonnegative income. -/
def BudgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  {x | Expenditure p x ≤ (y : ℝ)}

/-- The zero bundle costs nothing. -/
theorem expenditure_zero {k : ℕ} (p : PositivePrices k) :
    Expenditure p (ZeroBundle k) = 0 := by simp [Expenditure, ZeroBundle]

/-- Every feasible consumption expenditure is nonnegative. -/
theorem expenditure_nonneg {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) :
    0 ≤ Expenditure p x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (x.property j))

/-- Every nonnegative-income budget set is nonempty. -/
theorem budgetSet_nonempty {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    (BudgetSet p y).Nonempty := by
  refine ⟨ZeroBundle k, ?_⟩
  change Expenditure p (ZeroBundle k) ≤ (y : ℝ)
  rw [expenditure_zero]
  exact y.property

/-- Spending on one good cannot exceed the total nonnegative expenditure. -/
theorem commodity_expenditure_le {k : ℕ} (p : PositivePrices k)
    (x : NonnegativeOrthant k) (j : Fin k) : p.val j * x.val j ≤ Expenditure p x :=
  Finset.single_le_sum (fun i _ => mul_nonneg (p.property i).le (x.property i))
    (Finset.mem_univ j)

/-- Each budget-feasible coordinate is bounded by income divided by its price. -/
theorem budgetSet_coordinate_bound {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ BudgetSet p y) (j : Fin k) :
    x.val j ≤ (y : ℝ) / p.val j := by
  apply (le_div_iff₀ (p.property j)).mpr
  simpa only [mul_comm] using (commodity_expenditure_le p x j).trans hx

/-- At zero income the zero bundle is the only feasible consumption. -/
theorem budgetSet_zero {k : ℕ} (p : PositivePrices k) :
    BudgetSet p 0 = {ZeroBundle k} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext j
    apply le_antisymm
    · change x.val j ≤ 0
      simpa only [NNReal.coe_zero, zero_div] using budgetSet_coordinate_bound p 0 hx j
    · exact x.property j
  · rintro rfl
    change Expenditure p (ZeroBundle k) ≤ 0
    exact (expenditure_zero p).le

/-- Expenditure is continuous in the consumption bundle. -/
theorem expenditure_continuous {k : ℕ} (p : PositivePrices k) : Continuous (Expenditure p) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- Feasibility is a closed condition inside the nonnegative orthant. -/
theorem budgetSet_isClosed {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsClosed (BudgetSet p y) := isClosed_le (expenditure_continuous p) continuous_const

/-- Positive prices put the closed budget set inside a compact coordinate box. -/
theorem budgetSet_isCompact {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsCompact (BudgetSet p y) := by
  let b : Fin k → ℝ := fun j => (y : ℝ) / p.val j
  have hbox : IsCompact ((Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹'
      Set.Icc 0 b) :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  apply hbox.of_isClosed_subset (budgetSet_isClosed p y)
  intro x hx
  exact ⟨x.property, fun j => budgetSet_coordinate_bound p y hx j⟩

/-- Expenditure of a mixture is the corresponding mixture of expenditures. -/
theorem expenditure_mix {k : ℕ} (p : PositivePrices k) (x z : NonnegativeOrthant k)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) =
      a * Expenditure p x + (1 - a) * Expenditure p z := by
  change (∑ j, p.val j * (a * x.val j + (1 - a) * z.val j)) = _
  calc
    _ = ∑ j, (a * (p.val j * x.val j) + (1 - a) * (p.val j * z.val j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- Budget sets are convex, without any assumption on the consumer's utility. -/
theorem budgetSet_convex {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (BudgetSet p y) := by
  intro x hx z hz a ha
  have he := expenditure_mix p x z a ha
  change Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) ≤ (y : ℝ)
  rw [he]
  have hx' := mul_le_mul_of_nonneg_left hx ha.1
  have hz' := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ha.2)
  linarith

/-- Multiply every commodity price by the same strictly positive factor. -/
def ScalePrices {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) : PositivePrices k :=
  ⟨fun j => a * p.val j, fun j => mul_pos ha (p.property j)⟩

/-- Scaling all unit prices scales expenditure by the same factor. -/
theorem expenditure_scalePrices {k : ℕ} (a : ℝ) (ha : 0 < a)
    (p : PositivePrices k) (x : NonnegativeOrthant k) :
    Expenditure (ScalePrices a ha p) x = a * Expenditure p x := by
  simp only [Expenditure, ScalePrices, mul_assoc, Finset.mul_sum]

/-- Simultaneous positive scaling of prices and income leaves the entire budget set unchanged. -/
theorem budgetSet_scale {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    BudgetSet (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = BudgetSet p y := by
  ext x
  change Expenditure (ScalePrices a ha p) x ≤ a * (y : ℝ) ↔ _
  rw [expenditure_scalePrices, mul_le_mul_iff_right₀ ha]
  rfl

end Kreps.ConsumerDemand
