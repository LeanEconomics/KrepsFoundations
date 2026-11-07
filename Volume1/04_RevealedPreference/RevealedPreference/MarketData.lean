/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.PreferenceProperties
import RevealedPreference.RevealedChains

/-!
# Finite market observations and rationalization

Kreps I, pp. 67-70. Observed bundles are nonnegative, prices are strictly positive,
incomes are nonnegative, and observations are feasible. Budget exhaustion is a
conclusion of GARP or locally insatiable maximization, never an input to the data.
The index type need not be finite until the sufficiency proof invokes it.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- Expenditure at a price vector, on any real commodity vector. -/
def Expenditure (p x : Fin k → ℝ) : ℝ := ∑ j, p j * x j

/-- The full nonnegative budget set includes its boundary and all unobserved bundles. -/
def Budget (p : Fin k → ℝ) (y : ℝ) : Set (NonnegativeOrthant k) :=
  {x | Expenditure p x.val ≤ y}

/-- Primitive market observations; feasibility does not presume budget exhaustion. -/
structure MarketData (I : Type*) (k : ℕ) where
  price : I → Fin k → ℝ
  income : I → ℝ
  bundle : I → NonnegativeOrthant k
  price_pos : ∀ i j, 0 < price i j
  income_nonneg : ∀ i, 0 ≤ income i
  feasible : ∀ i, Expenditure (price i) (bundle i).val ≤ income i

/-- The matrix records cross-expenditure minus the original observation's income. -/
def MarketData.cost (D : MarketData I k) (i j : I) : ℝ :=
  Expenditure (D.price i) (D.bundle j).val - D.income i

/-- **Definition 4.2:** the original-income data have no revealed strict cycle. -/
def GARP (D : MarketData I k) : Prop := MatrixGARP D.cost

/-- A preference rationalizes each choice on its entire observed budget set. -/
def Rationalizes (D : MarketData I k)
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ i, D.bundle i ∈ PrefChoice r (Budget (D.price i) (D.income i))

/-- Expenditure is continuous on real commodity space. -/
theorem expenditure_continuous (p : Fin k → ℝ) : Continuous (Expenditure p) := by
  unfold Expenditure
  fun_prop

/-- Expenditure remains continuous when restricted to nonnegative bundles. -/
theorem expenditure_orthant_continuous (p : Fin k → ℝ) :
    Continuous (fun x : NonnegativeOrthant k => Expenditure p x.val) :=
  (expenditure_continuous p).comp continuous_subtype_val

/-- The strict interior of a budget is an open set in the consumption domain. -/
theorem strictBudget_isOpen (p : Fin k → ℝ) (y : ℝ) :
    IsOpen {x : NonnegativeOrthant k | Expenditure p x.val < y} :=
  isOpen_lt (expenditure_orthant_continuous p) continuous_const

/-- Feasibility makes every diagonal entry nonpositive. -/
theorem MarketData.cost_self_nonpos (D : MarketData I k) (i : I) : D.cost i i ≤ 0 :=
  sub_nonpos.mpr (D.feasible i)

/-- GARP forces every observation to exhaust its original income. -/
theorem garp_budget_exhaustion {D : MarketData I k} (hG : GARP D) (i : I) :
    Expenditure (D.price i) (D.bundle i).val = D.income i :=
  sub_eq_zero.mp (matrixGARP_diagonal_zero hG D.cost_self_nonpos i)

/-- With exhausted budgets, costs are the expenditure differences in the Afriat formula. -/
theorem garp_cost_eq_difference {D : MarketData I k} (hG : GARP D) (i j : I) :
    D.cost i j = Expenditure (D.price i) (D.bundle j).val -
      Expenditure (D.price i) (D.bundle i).val := by
  rw [garp_budget_exhaustion hG]
  rfl

/-- Without local insatiability, complete indifference rationalizes every feasible dataset. -/
theorem constant_utility_rationalizes (D : MarketData I k) :
    Rationalizes D (UtilityPref (fun _ => 0)) := by
  intro i
  exact ⟨D.feasible i, fun _ _ => le_rfl⟩

end Kreps.RevealedPreference
