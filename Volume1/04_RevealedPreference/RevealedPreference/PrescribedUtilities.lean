/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.MarketExamples

/-!
# The two possible rankings in the modified example

Kreps I, p. 69, allows either a strict ranking of the second bundle above the
first or indifference between them; both dominate the third. We construct
full-domain regular utility rationalizers realizing both possibilities, with
explicit Afriat coefficients. The reusable interpolation results preserve
prescribed utility levels on every observation.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} [Fintype I] [Nonempty I] {k : ℕ}

/-- The affine envelope attached to market data and prescribed Afriat coefficients. -/
noncomputable def DataEnvelope (D : MarketData I k) (v lam : I → ℝ) :
    (Fin k → ℝ) → ℝ := FiniteAffineEnvelope D.price (fun i => (D.bundle i).val) v lam

/-- Positive original-income Afriat inequalities imply exact interpolation at observations. -/
theorem dataEnvelope_at {D : MarketData I k} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hv : ∀ i j, v i ≤ v j + lam j * D.cost j i) (i : I) :
    DataEnvelope D v lam (D.bundle i).val = v i := by
  have hG : GARP D := matrixGARP_of_afriat hlam hv
  apply finiteAffineEnvelope_at_anchor
  intro a b
  simpa only [garp_cost_eq_difference hG, AffineExpenditure, Expenditure] using hv a b

/-- The prescribed envelope rationalizes entire budgets, not just the finite observations. -/
theorem dataEnvelope_rationalizes {D : MarketData I k} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hv : ∀ i j, v i ≤ v j + lam j * D.cost j i) :
    Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => DataEnvelope D v lam x.val)) := by
  have hG : GARP D := matrixGARP_of_afriat hlam hv
  intro i
  refine ⟨D.feasible i, fun x hx => ?_⟩
  change DataEnvelope D v lam x.val ≤ DataEnvelope D v lam (D.bundle i).val
  rw [dataEnvelope_at hlam hv]
  apply finiteAffineEnvelope_le_value i (hlam i).le
  change Expenditure (D.price i) x.val ≤ Expenditure (D.price i) (D.bundle i).val
  rw [garp_budget_exhaustion hG]
  exact hx

/-- A family realizing both printed rankings, with intermediate utility levels allowed. -/
noncomputable def ModifiedUtility (b : ℝ) : (Fin 3 → ℝ) → ℝ :=
  DataEnvelope ModifiedData ![1, b, 0] ![1 / 20, 1, 1]

/-- All the multipliers used for the modified example are strictly positive. -/
theorem modified_multipliers_pos (i : Fin 3) : 0 < (![1 / 20, 1, 1] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num

/-- The exact Afriat inequalities hold for every prescribed second utility between one and two. -/
theorem modified_afriat {b : ℝ} (hb : b ∈ Set.Icc 1 2) (i j : Fin 3) :
    (![1, b, 0] : Fin 3 → ℝ) i ≤ ![1, b, 0] j +
      ![1 / 20, 1, 1] j * ModifiedData.cost j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [MarketData.cost, ModifiedData, InitialBundles, Expenditure,
      Fin.sum_univ_succ] <;> linarith [hb.1, hb.2]

/-- Each member of the explicit family is continuous, increasing and concave on all vectors. -/
theorem modifiedUtility_regular (b : ℝ) :
    Continuous (ModifiedUtility b) ∧ StrictMono (ModifiedUtility b) ∧
      ConcaveOn ℝ Set.univ (ModifiedUtility b) := by
  unfold ModifiedUtility DataEnvelope
  exact ⟨finiteAffineEnvelope_continuous _ _ _ _,
    finiteAffineEnvelope_strictMono modified_multipliers_pos ModifiedData.price_pos,
    finiteAffineEnvelope_concaveOn _ _ _ _⟩

/-- The explicit utilities rationalize the modified data on the full orthant. -/
theorem modifiedUtility_rationalizes {b : ℝ} (hb : b ∈ Set.Icc 1 2) :
    Rationalizes ModifiedData
      (UtilityPref (fun x : NonnegativeOrthant 3 => ModifiedUtility b x.val)) :=
  dataEnvelope_rationalizes modified_multipliers_pos (modified_afriat hb)

/-- The constructed family has exactly the prescribed three observed utility levels. -/
theorem modifiedUtility_values {b : ℝ} (hb : b ∈ Set.Icc 1 2) (i : Fin 3) :
    ModifiedUtility b (InitialBundles i).val = ![1, b, 0] i :=
  dataEnvelope_at modified_multipliers_pos (modified_afriat hb) i

/-- The source's strict ordering is realized by a full-domain rationalizer. -/
theorem modifiedUtility_strict_rankings :
    ModifiedUtility 2 (InitialBundles 2).val < ModifiedUtility 2 (InitialBundles 0).val ∧
      ModifiedUtility 2 (InitialBundles 0).val < ModifiedUtility 2 (InitialBundles 1).val := by
  simp [modifiedUtility_values (by norm_num : (2 : ℝ) ∈ Set.Icc 1 2)]

/-- The source's alternative indifference is also realized by a full-domain rationalizer. -/
theorem modifiedUtility_tied_rankings :
    ModifiedUtility 1 (InitialBundles 2).val < ModifiedUtility 1 (InitialBundles 0).val ∧
      ModifiedUtility 1 (InitialBundles 0).val = ModifiedUtility 1 (InitialBundles 1).val := by
  simp [modifiedUtility_values (by norm_num : (1 : ℝ) ∈ Set.Icc 1 2)]

end Kreps.RevealedPreference
