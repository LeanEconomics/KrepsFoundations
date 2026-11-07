/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BangForBuck

/-!
# Budget-preserving commodity transfers

Kreps I, pp. 61-62. Moving expenditure from a consumed good to another good
preserves cost and remains nonnegative for a suitably small transfer. The actual
within-domain derivative along that path is the difference of marginal utilities
per dollar. This uses a multivariate derivative, not merely coordinate partials.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- One dollar moved from good `j` to good `i`, expressed as a commodity direction. -/
noncomputable def TransferDirection {k : ℕ} (p : PositivePrices k) (i j : Fin k) : Fin k → ℝ :=
  (1 / p.val i) • Pi.single i 1 - (1 / p.val j) • Pi.single j 1

/-- Every expenditure transfer has zero net cost. -/
theorem transferDirection_cost {k : ℕ} (p : PositivePrices k) (i j : Fin k) :
    (∑ l, p.val l * TransferDirection p i j l) = 0 := by
  simp [TransferDirection, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
    ne_of_gt (p.property i), ne_of_gt (p.property j)]

/-- Transferring no more than the original expenditure on the donor good is nonnegative. -/
theorem transfer_nonnegative {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) {d : ℝ} (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    0 ≤ x.val + d • TransferDirection p i j := by
  intro l
  by_cases hli : l = i
  · subst l
    have h : 0 ≤ d / p.val i := div_nonneg hd (p.property i).le
    simpa [TransferDirection, Pi.single_apply, hij, Ne.symm hij, div_eq_mul_inv] using
      add_nonneg (x.property i) h
  · by_cases hlj : l = j
    · subst l
      have h : d / p.val j ≤ x.val j :=
        (div_le_iff₀ (p.property j)).mpr (by simpa only [mul_comm] using hb)
      simpa [TransferDirection, Pi.single_apply, hij, Ne.symm hij, div_eq_mul_inv] using
        sub_nonneg.mpr h
    · simpa [TransferDirection, Pi.single_apply, hli, hlj] using x.property l

/-- A feasible commodity transfer as a nonnegative consumption bundle. -/
noncomputable def TransferBundle {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    NonnegativeOrthant k := ⟨x.val + d • TransferDirection p i j,
      transfer_nonnegative p x i j hij hd hb⟩

/-- The actual nonnegative transfer bundle has exactly the original expenditure. -/
theorem expenditure_transferBundle {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    Expenditure p (TransferBundle p x i j hij d hd hb) = Expenditure p x := by
  have he : Expenditure p (TransferBundle p x i j hij d hd hb) =
      Expenditure p x + d * (∑ l, p.val l * TransferDirection p i j l) := by
    simp only [Expenditure, TransferBundle, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he, transferDirection_cost, mul_zero, add_zero]

/-- The expenditure transfer preserves budget feasibility. -/
theorem transferBundle_mem_budget {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ BudgetSet p y) (i j : Fin k) (hij : i ≠ j)
    (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    TransferBundle p x i j hij d hd hb ∈ BudgetSet p y := by
  change Expenditure p (TransferBundle p x i j hij d hd hb) ≤ (y : ℝ)
  rwa [expenditure_transferBundle]

/-- Evaluating a linear derivative on the exchange gives the marginal-return difference. -/
theorem derivative_transferDirection {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ)
    (p : PositivePrices k) (i j : Fin k) :
    D (TransferDirection p i j) =
      MarginalUtility D i / p.val i - MarginalUtility D j / p.val j := by
  simp [TransferDirection, MarginalUtility, map_sub, map_smul, div_eq_mul_inv, mul_comm]

/-- The actual right derivative on a short exchange segment equals the marginal-return gap. -/
theorem utility_transfer_derivative {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) {b : ℝ} (hb : b ≤ p.val j * x.val j)
    (hd : HasFDerivWithinAt u D (Set.Ici 0) x.val) :
    HasDerivWithinAt (fun d : ℝ => u (x.val + d • TransferDirection p i j))
      (MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) (Set.Icc 0 b) 0 := by
  have hp : HasDerivAt (fun d : ℝ => x.val + d • TransferDirection p i j)
      (TransferDirection p i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (TransferDirection p i j)).const_add x.val
  have hm : Set.MapsTo (fun d : ℝ => x.val + d • TransferDirection p i j)
      (Set.Icc 0 b) (Set.Ici 0) :=
    fun _ ht => transfer_nonnegative p x i j hij ht.1 (ht.2.trans hb)
  have h := hd.comp_hasDerivWithinAt_of_eq 0 hp.hasDerivWithinAt hm (by simp)
  rwa [derivative_transferDirection] at h

/-- A positive marginal-return gap yields an actual utility-improving affordable transfer. -/
theorem exists_improving_commodity_transfer {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (hj : 0 < x.val j)
    (hd : HasFDerivWithinAt u D (Set.Ici 0) x.val)
    (hgap : 0 < MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) :
    ∃ d : ℝ, 0 < d ∧ d ≤ p.val j * x.val j ∧
      u x.val < u (x.val + d • TransferDirection p i j) := by
  let b := p.val j * x.val j
  have hb : 0 < b := mul_pos (p.property j) hj
  have hder := utility_transfer_derivative p x i j hij (le_refl b) hd
  by_contra! hn
  have hmax : IsMaxOn (fun d : ℝ => u (x.val + d • TransferDirection p i j))
      (Set.Icc 0 b) 0 := by
    intro d hd'
    change u (x.val + d • TransferDirection p i j) ≤ u (x.val + 0 • TransferDirection p i j)
    simp only [zero_smul, add_zero]
    by_cases hzero : d = 0
    · simp [hzero]
    · have hpos : 0 < d := lt_of_le_of_ne hd'.1 (Ne.symm hzero)
      exact hn d hpos hd'.2
  have hfirst := convex_firstOrderNecessary hmax hder.hasFDerivWithinAt (Set.Subset.refl _)
    (convex_Icc _ _) (show 0 ∈ Set.Icc (0 : ℝ) b from ⟨le_rfl, hb.le⟩)
    b ⟨hb.le, le_rfl⟩
  have hnonpos : b * (MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) ≤ 0 := by
    simpa using hfirst
  exact not_lt_of_ge hnonpos (mul_pos hb hgap)

end Kreps.ConsumerDemand
