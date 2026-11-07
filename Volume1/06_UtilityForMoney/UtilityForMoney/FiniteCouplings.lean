/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries

/-!
# Joint laws of two finite monetary lotteries

Kreps I, Proposition 6.15 and Problem 6.6, pp. 133–134 and 141–142.
A joint law assigns nonnegative probabilities to pairs of support points.
Rows and columns recover the prescribed marginal laws. Each row has positive
mass, so its conditional expected supplement is well-defined.
-/

namespace Kreps.UtilityForMoney

open Convexity

/-- The probabilities at the actual support points sum to one. -/
theorem support_mass_sum {X : Type*} (p : SimpleLottery X) :
    ∑ i : p.weights.support, p.weights i.val = 1 := by
  rw [Finset.sum_coe_sort p.weights.support (fun x => p.weights x)]
  exact p.total

/-- Each simple lottery has at least one actual support point. -/
theorem lottery_support_nonempty {X : Type*} (p : SimpleLottery X) :
    Nonempty ↥p.weights.support := by
  have h := support_mass_sum p
  by_contra! he
  simp at h

/-- A finite coupling is a joint probability table with the given row and column marginals. -/
structure FiniteCoupling (p q : SimpleLottery ℝ) where
  /-- Joint mass of the specified support pair. -/
  mass : p.weights.support → q.weights.support → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ mass i j
  /-- Summing over columns recovers the first marginal. -/
  row_sum : ∀ i, ∑ j, mass i j = p.weights i.val
  /-- Summing over rows recovers the second marginal. -/
  col_sum : ∀ j, ∑ i, mass i j = q.weights j.val

/-- The second outcome's conditional increment has nonpositive mass-weighted mean in every row. -/
def FiniteCoupling.NonpositiveDrift {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) : Prop :=
  ∀ i, ∑ j : q.weights.support, C.mass i j * (j.val - i.val) ≤ 0

/-- Normalizing the row gives its conditional expected supplement. -/
noncomputable def FiniteCoupling.conditionalDrift {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (i : p.weights.support) : ℝ :=
  ∑ j : q.weights.support, (C.mass i j / p.weights i.val) * (j.val - i.val)

/-- The sign of the conditional mean agrees with that of the unnormalized drift. -/
theorem FiniteCoupling.nonpositiveDrift_iff {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) :
    C.NonpositiveDrift ↔ ∀ i, C.conditionalDrift i ≤ 0 := by
  have hp (i : p.weights.support) : 0 < p.weights i.val :=
    lt_of_le_of_ne (p.nonneg i.val) (Ne.symm (Finsupp.mem_support_iff.mp i.property))
  have he (i : p.weights.support) : C.conditionalDrift i =
      (∑ j : q.weights.support, C.mass i j * (j.val - i.val)) / p.weights i.val := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [NonpositiveDrift, he, div_le_iff₀ (hp _), zero_mul]

/-- The joint lottery on support pairs gives both random variables on a common sample space. -/
noncomputable def FiniteCoupling.jointLaw {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) :
    SimpleLottery (↥p.weights.support × ↥q.weights.support) where
  weights := Finsupp.equivFunOnFinite.symm (fun ij => C.mass ij.1 ij.2)
  nonneg := fun ij => C.nonneg ij.1 ij.2
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 = 1
    rw [Fintype.sum_prod_type]
    simpa only [C.row_sum] using support_mass_sum p

/-- The first projection gives the prescribed marginal expectation. -/
theorem FiniteCoupling.first_marginal {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (U : ℝ → ℝ) : ExpectedUtility (fun ij => U ij.1.val) C.jointLaw = ExpectedUtility U p := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 * U ij.1.val = _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, C.row_sum, Finset.sum_coe_sort p.weights.support
    (fun x => p.weights x * U x), Finsupp.sum]

/-- Integrating a function of the second projection gives its second marginal expectation. -/
theorem FiniteCoupling.second_marginal {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (U : ℝ → ℝ) : ExpectedUtility (fun ij => U ij.2.val) C.jointLaw = ExpectedUtility U q := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 * U ij.2.val = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, C.col_sum, Finset.sum_coe_sort q.weights.support
    (fun x => q.weights x * U x), Finsupp.sum]

end Kreps.UtilityForMoney
