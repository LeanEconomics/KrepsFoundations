/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BudgetContinuity
import ConsumerDemand.ConsumerProblem

/-!
# Homothetic preference and income scaling of all demand

Kreps I, Problem 3.10(b), p. 65. Positive income scaling transports every
maximizer, and transports the full choice set bijectively. Zero target income is
handled separately; the origin at zero source income does not identify choices
at positive income. Neither continuity nor uniqueness is assumed.

The homotheticity definition and elementary scaling identities are selected
local copies from Chapter 2's `Homotheticity`, originating at commit `7d496c5`.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

variable {k : ℕ}

/-- Every common nonnegative scaling preserves weak preference. -/
def HomotheticPreference (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x z t, r x z → r (ScaleBundle t x) (ScaleBundle t z)

/-- A zero scalar gives the zero commodity bundle. -/
theorem scaleBundle_zero_scalar (x : NonnegativeOrthant k) :
    ScaleBundle 0 x = ZeroBundle k := by
  apply Subtype.ext
  ext j
  simp [ScaleBundle, ZeroBundle]

/-- Successive scalings multiply their factors. -/
theorem scaleBundle_mul (a b : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle (a * b) x = ScaleBundle a (ScaleBundle b x) := by
  apply Subtype.ext
  ext j
  simp [ScaleBundle, mul_assoc]

/-- Every positive scalar can be undone inside the consumption domain. -/
theorem scaleBundle_inv {a : ℝ≥0} (ha : a ≠ 0) (x : NonnegativeOrthant k) :
    ScaleBundle a⁻¹ (ScaleBundle a x) = x := by
  rw [← scaleBundle_mul, inv_mul_cancel₀ ha, scaleBundle_one]

/-- Positive scaling preserves and reflects weak preference. -/
theorem homothetic_scale_iff {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hh : HomotheticPreference r) {a : ℝ≥0} (ha : 0 < a) (x z : NonnegativeOrthant k) :
    r (ScaleBundle a x) (ScaleBundle a z) ↔ r x z := by
  refine ⟨fun h => ?_, hh x z a⟩
  simpa only [scaleBundle_inv ha.ne'] using hh _ _ a⁻¹ h

/-- Positive scaling exactly transports budget feasibility at fixed prices. -/
theorem mem_budgetSet_scale_bundle_iff (p : PositivePrices k) (y : ℝ≥0)
    {a : ℝ≥0} (ha : 0 < a) (x : NonnegativeOrthant k) :
    ScaleBundle a x ∈ BudgetSet p (a * y) ↔ x ∈ BudgetSet p y := by
  change Expenditure p (ScaleBundle a x) ≤ ((a * y : ℝ≥0) : ℝ) ↔ _
  rw [expenditure_scaleBundle, NNReal.coe_mul]
  exact mul_le_mul_iff_right₀ ha

/-- A chosen bundle stays chosen under a positive common scaling of consumption and income. -/
theorem homothetic_choice_scale_pos
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a)
    {x : NonnegativeOrthant k} (hx : x ∈ PrefChoice r (BudgetSet p y)) :
    ScaleBundle a x ∈ PrefChoice r (BudgetSet p (a * y)) := by
  refine ⟨(mem_budgetSet_scale_bundle_iff p y ha x).mpr hx.1, ?_⟩
  intro z hz
  have hz' : ScaleBundle a⁻¹ z ∈ BudgetSet p y := by
    have h := (mem_budgetSet_scale_bundle_iff p (a * y) (inv_pos.mpr ha) z).mpr hz
    simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using h
  have hr := hh x (ScaleBundle a⁻¹ z) a (hx.2 _ hz')
  rwa [← scaleBundle_mul, mul_inv_cancel₀ ha.ne', scaleBundle_one] at hr

/-- The scaled choice is optimal exactly when the original choice is optimal. -/
theorem homothetic_choice_scale_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a) (x : NonnegativeOrthant k) :
    ScaleBundle a x ∈ PrefChoice r (BudgetSet p (a * y)) ↔
      x ∈ PrefChoice r (BudgetSet p y) := by
  constructor
  · intro h
    have h' := homothetic_choice_scale_pos hh p (a * y) (inv_pos.mpr ha) h
    simpa [scaleBundle_inv ha.ne', ← mul_assoc, inv_mul_cancel₀ ha.ne'] using h'
  · exact homothetic_choice_scale_pos hh p y ha

/-- At positive incomes, the entire demand correspondence scales, including multiple maxima. -/
theorem homothetic_choice_set_scale
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a) :
    PrefChoice r (BudgetSet p (a * y)) = ScaleBundle a '' PrefChoice r (BudgetSet p y) := by
  ext z
  constructor
  · intro hz
    refine ⟨ScaleBundle a⁻¹ z, ?_, ?_⟩
    · have h := homothetic_choice_scale_pos hh p (a * y) (inv_pos.mpr ha) hz
      simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using h
    · rw [← scaleBundle_mul, mul_inv_cancel₀ ha.ne', scaleBundle_one]
  · rintro ⟨x, hx, rfl⟩
    exact homothetic_choice_scale_pos hh p y ha hx

/-- **Problem 3.10(b):** from positive income, every chosen bundle scales by the income ratio. -/
theorem problem_3_10b
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y y' : ℝ≥0) (hy : 0 < y)
    {x : NonnegativeOrthant k} (hx : x ∈ PrefChoice r (BudgetSet p y)) :
    ScaleBundle (y' / y) x ∈ PrefChoice r (BudgetSet p y') := by
  by_cases hy' : y' = 0
  · subst y'
    simp only [zero_div, scaleBundle_zero_scalar, budgetSet_zero]
    refine ⟨rfl, ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    simpa only [scaleBundle_zero_scalar] using hh x x 0 (hx.2 x hx.1)
  · have h := homothetic_choice_scale_pos hh p y (div_pos (pos_iff_ne_zero.mpr hy') hy) hx
    simpa only [div_mul_cancel₀ _ hy.ne'] using h

/-- Degree-one homogeneous utility represents homothetic preference, including at zero scale. -/
theorem homothetic_of_homogeneous {u : NonnegativeOrthant k → ℝ}
    (hu : ∀ a x, u (ScaleBundle a x) = (a : ℝ) * u x) : HomotheticPreference (UtilityPref u) := by
  intro x z a hxz
  change u (ScaleBundle a z) ≤ u (ScaleBundle a x)
  rw [hu, hu]
  exact mul_le_mul_of_nonneg_left hxz a.property

end Kreps.ConsumerDemand
