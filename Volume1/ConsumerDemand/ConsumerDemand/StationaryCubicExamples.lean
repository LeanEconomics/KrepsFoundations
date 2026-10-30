/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import ConsumerDemand.RepresentationMonotonicity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Stationary but strictly increasing utility

Kreps I, Problems 3.11(b) and 3.12, p. 65. The constructed one-good utility
`(x - 1)^3` has a zero derivative at one unit. At income two this is a nonoptimal
stationary candidate; at income one it is the unique optimum and forces a zero
multiplier. The formula is our witness, not a formula printed in the book.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- The one-good stationary cubic, defined on the ambient line of bundles. -/
def StationaryCubic (x : Fin 1 → ℝ) : ℝ := (x 0 - 1) ^ 3

/-- A one-good consumption quantity as a bundle. -/
def SingleQuantity (q : ℝ≥0) : NonnegativeOrthant 1 := ⟨fun _ => q, fun _ => q.property⟩

/-- The unit price for the cubic examples. -/
def UnitPrice : PositivePrices 1 := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- The scalar cubic is strictly increasing despite its stationary point. -/
theorem stationaryCubic_increasing {a b : ℝ} (h : a < b) :
    (a - 1) ^ 3 < (b - 1) ^ 3 :=
  (Odd.strictMono_pow (by decide : Odd 3)) (sub_lt_sub_right h 1)

/-- The utility is continuously differentiable on the whole ambient space. -/
theorem stationaryCubic_contDiff : ContDiff ℝ 1 StationaryCubic := by
  unfold StationaryCubic
  fun_prop

/-- Local insatiability holds at every nonnegative quantity, including zero and one. -/
theorem stationaryCubic_locallyInsatiable :
    LocallyInsatiable (UtilityPref (fun x : NonnegativeOrthant 1 => StationaryCubic x.val)) := by
  apply Representation.strictAllIncrease_locallyInsatiable
  intro x y h
  have hs := stationaryCubic_increasing (h 0)
  exact ⟨hs.le, not_le_of_gt hs⟩

/-- The actual derivative at one unit is the zero linear functional. -/
theorem stationaryCubic_derivative_one :
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
    (x := (SingleQuantity 1).val)).sub_const 1 |>.pow 3
  convert h using 1 <;> first | rfl | simp [SingleQuantity]

/-- At either income, the stationary candidate satisfies the exact combined conditions. -/
theorem stationaryCubic_conditions {y : ℝ≥0} (hy : 1 ≤ y) :
    OptimalityConditions UnitPrice y (SingleQuantity 1) 0 := by
  refine ⟨?_, 0, le_rfl, ?_, ?_, ?_⟩
  · change Expenditure UnitPrice (SingleQuantity 1) ≤ (y : ℝ)
    simpa [Expenditure, UnitPrice, SingleQuantity] using (show (1 : ℝ) ≤ y from hy)
  · intro j
    simp [MarginalUtility]
  · intro j _
    simp [MarginalUtility]
  · intro _
    rfl

/-- **Problem 3.11(b):** the stationary candidate at income two is strictly suboptimal. -/
theorem stationaryCubic_nonoptimal :
    SingleQuantity 1 ∉ MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 2 := by
  intro h
  have hb : SingleQuantity 2 ∈ BudgetSet UnitPrice 2 := by
    norm_num [BudgetSet, Expenditure, UnitPrice, SingleQuantity]
  have hc := h.2 (SingleQuantity 2) hb
  norm_num [UtilityPref, StationaryCubic, SingleQuantity] at hc

/-- Strictly increasing one-good cubic preferences are strictly convex. -/
theorem stationaryCubic_strictlyConvex :
    StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (UtilityPref (fun x => StationaryCubic x.val)) := by
  intro x y hne hxy a ha
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  have hle : y.val 0 ≤ x.val 0 := hf.le_iff_le.mp hxy
  have hneq : x.val 0 ≠ y.val 0 := by
    intro h
    apply hne
    apply Subtype.ext
    funext i
    fin_cases i
    exact h
  have hlt : y.val 0 < x.val 0 := lt_of_le_of_ne hle (Ne.symm hneq)
  have hm : y.val 0 < a * x.val 0 + (1 - a) * y.val 0 := by
    nlinarith [mul_pos ha.1 (sub_pos.mpr hlt)]
  have h := stationaryCubic_increasing hm
  exact ⟨h.le, not_le_of_gt h⟩

/-- The witness also satisfies the quasi-concavity premise of Problem 3.11. -/
theorem stationaryCubic_quasiConcave :
    QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (fun x => StationaryCubic x.val) := by
  intro x y a ha
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  change min ((x.val 0 - 1) ^ 3) ((y.val 0 - 1) ^ 3) ≤
    ((a * x.val 0 + (1 - a) * y.val 0) - 1) ^ 3
  by_cases h : x.val 0 ≤ y.val 0
  · exact (min_le_left _ _).trans (hf.monotone (by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr h)]))
  · exact (min_le_right _ _).trans (hf.monotone (by
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (le_of_not_ge h))]))

/-- At unit price the unique demand is the entire income, including zero income. -/
theorem stationaryCubic_demand (y : ℝ≥0) :
    MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice y = {SingleQuantity y} := by
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  have hb : SingleQuantity y ∈ BudgetSet UnitPrice y := by
    simp [BudgetSet, Expenditure, UnitPrice, SingleQuantity]
  ext x
  constructor
  · intro hx
    have hlow : (y : ℝ) ≤ x.val 0 := hf.le_iff_le.mp (hx.2 _ hb)
    have hupp : x.val 0 ≤ (y : ℝ) := by
      simpa [BudgetSet, Expenditure, UnitPrice] using hx.1
    apply Subtype.ext
    funext i
    fin_cases i
    exact le_antisymm hupp hlow
  · intro hx
    rcases hx with rfl
    refine ⟨hb, fun z hz => ?_⟩
    apply hf.monotone
    simpa [BudgetSet, Expenditure, UnitPrice, SingleQuantity] using hz

/-- **Problem 3.12:** every multiplier satisfying stationarity at the unique income-one
optimum is zero. The stationary derivative is proved separately above. -/
theorem stationaryCubic_multiplier_forced_zero (l : ℝ)
    (heq : ∀ j, 0 < (SingleQuantity 1).val j →
      MarginalUtility (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) j = l * UnitPrice.val j) : l = 0 := by
  have h := heq 0 (by norm_num [SingleQuantity])
  simpa [MarginalUtility, UnitPrice] using h.symm

/-- The utility is strictly increasing in the full one-good coordinate order. -/
theorem stationaryCubic_strictMono : StrictMono StationaryCubic := by
  intro x y hxy
  apply stationaryCubic_increasing
  by_contra h
  apply hxy.not_ge
  intro i
  fin_cases i
  exact le_of_not_gt h

/-- **Problem 3.11(b):** all regularity premises hold, but the exact calculus conditions
at one unit do not imply demand at income two. -/
theorem problem_3_11b :
    ContDiff ℝ 1 StationaryCubic ∧
    LocallyInsatiable (UtilityPref (fun x : NonnegativeOrthant 1 => StationaryCubic x.val)) ∧
    QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (fun x => StationaryCubic x.val) ∧
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val ∧
    OptimalityConditions UnitPrice 2 (SingleQuantity 1) 0 ∧
    SingleQuantity 1 ∉ MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 2 :=
  ⟨stationaryCubic_contDiff, stationaryCubic_locallyInsatiable, stationaryCubic_quasiConcave,
    stationaryCubic_derivative_one, stationaryCubic_conditions (by norm_num),
    stationaryCubic_nonoptimal⟩

/-- **Problem 3.12:** the strictly increasing, strictly convex preference witness has
unique demand at the stationary point, whose multiplier must vanish. -/
theorem problem_3_12 :
    StrictMono StationaryCubic ∧
    StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (UtilityPref (fun x => StationaryCubic x.val)) ∧
    MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 1 = {SingleQuantity 1} ∧
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val ∧
    OptimalityConditions UnitPrice 1 (SingleQuantity 1) 0 ∧
    ∀ l : ℝ, (∀ j, 0 < (SingleQuantity 1).val j →
      MarginalUtility (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) j = l * UnitPrice.val j) → l = 0 :=
  ⟨stationaryCubic_strictMono, stationaryCubic_strictlyConvex, stationaryCubic_demand 1,
    stationaryCubic_derivative_one, stationaryCubic_conditions le_rfl,
    stationaryCubic_multiplier_forced_zero⟩

end Kreps.ConsumerDemand
