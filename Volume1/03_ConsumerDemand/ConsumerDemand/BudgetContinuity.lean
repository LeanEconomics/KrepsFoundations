/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BudgetSets
import ConsumerDemand.CorrespondenceMaximum

/-!
# Continuity and local boundedness of the budget correspondence

Kreps I, the proof of Proposition 3.3, pp. 55-56. The graph is closed and nearby
budgets lie in a common compact coordinate box. For lower semicontinuity we use
the printed recovery formula `(y'/y) * (p · x)/(p' · x) * x`, with the zero
bundle handled separately. The formula supplies a continuous feasible selection
through every feasible bundle, including the zero-income case.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal Topology

/-- The full parameter domain, including zero income but excluding zero prices. -/
abbrev PriceIncome (k : ℕ) := PositivePrices k × ℝ≥0

/-- Scale a nonnegative bundle by a nonnegative scalar. -/
def ScaleBundle {k : ℕ} (a : ℝ≥0) (x : NonnegativeOrthant k) : NonnegativeOrthant k :=
  ⟨fun j => (a : ℝ) * x.val j, fun j => mul_nonneg a.property (x.property j)⟩

/-- Scaling zero consumption leaves it unchanged. -/
theorem scaleBundle_zero {k : ℕ} (a : ℝ≥0) : ScaleBundle a (ZeroBundle k) = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, ZeroBundle]

/-- Scaling by one leaves the whole bundle unchanged. -/
theorem scaleBundle_one {k : ℕ} (x : NonnegativeOrthant k) : ScaleBundle 1 x = x := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle]

/-- Expenditure scales linearly in consumption. -/
theorem expenditure_scaleBundle {k : ℕ} (p : PositivePrices k) (a : ℝ≥0)
    (x : NonnegativeOrthant k) : Expenditure p (ScaleBundle a x) = a * Expenditure p x := by
  simp only [Expenditure, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every nonzero nonnegative bundle costs strictly more than zero at strictly positive prices. -/
theorem expenditure_pos {k : ℕ} (p : PositivePrices k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : 0 < Expenditure p x := by
  have hn : Expenditure p x ≠ 0 := by
    intro he
    apply hx
    apply Subtype.ext
    funext j
    have h := commodity_expenditure_le p x j
    have hp := p.property j
    have hxj : 0 ≤ x.val j := x.property j
    change x.val j = 0
    rw [he] at h
    nlinarith
  exact lt_of_le_of_ne (expenditure_nonneg p x) hn.symm

/-- For a fixed bundle, expenditure varies continuously with the price vector. -/
theorem expenditure_price_continuous {k : ℕ} (x : NonnegativeOrthant k) :
    Continuous (fun p : PositivePrices k => Expenditure p x) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- Joint continuity in prices and consumption gives closed budget graphs. -/
theorem expenditure_joint_continuous {k : ℕ} :
    Continuous (fun z : PositivePrices k × NonnegativeOrthant k => Expenditure z.1 z.2) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))

/-- The exact nonnegative multiplier in the book's recovery sequence. -/
noncomputable def BudgetAdjustmentFactor {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : ℝ≥0 :=
  ⟨(η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x),
    mul_nonneg (div_nonneg η.2.property θ.2.property)
      (div_nonneg (expenditure_nonneg θ.1 x) (expenditure_nonneg η.1 x))⟩

/-- Adjust the reference bundle to the new prices and income by the printed scaling formula. -/
noncomputable def BudgetAdjustment {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : NonnegativeOrthant k :=
  ScaleBundle (BudgetAdjustmentFactor θ x η) x

/-- The recovery multiplier equals one at its positive-income, nonzero reference point. -/
theorem budgetAdjustment_self {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ≠ ZeroBundle k) : BudgetAdjustment θ x θ = x := by
  have hf : BudgetAdjustmentFactor θ x θ = 1 := by
    apply NNReal.coe_injective
    change (θ.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure θ.1 x) = 1
    rw [div_self hy.ne', div_self (expenditure_pos θ.1 hx).ne', one_mul]
  rw [BudgetAdjustment, hf, scaleBundle_one]

/-- Every adjusted bundle remains feasible at its new prices and income. -/
theorem budgetAdjustment_feasible {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ∈ BudgetSet θ.1 θ.2) (η : PriceIncome k) :
    BudgetAdjustment θ x η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    change Expenditure η.1 (ScaleBundle _ (ZeroBundle k)) ≤ (η.2 : ℝ)
    rw [scaleBundle_zero, expenditure_zero]
    exact η.2.property
  change Expenditure η.1 (ScaleBundle _ x) ≤ (η.2 : ℝ)
  rw [expenditure_scaleBundle]
  change ((η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x)) *
    Expenditure η.1 x ≤ (η.2 : ℝ)
  rw [mul_assoc, div_mul_cancel₀ _ (expenditure_pos η.1 hx0).ne']
  calc
    _ ≤ ((η.2 : ℝ) / θ.2) * θ.2 :=
      mul_le_mul_of_nonneg_left hx (div_nonneg η.2.property θ.2.property)
    _ = _ := div_mul_cancel₀ _ hy.ne'

/-- The recovery bundle is continuous in the new parameters when the reference is nonzero. -/
theorem budgetAdjustment_continuous {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : Continuous (BudgetAdjustment θ x) := by
  have hf : Continuous (fun η : PriceIncome k => (BudgetAdjustmentFactor θ x η : ℝ)) :=
    ((continuous_subtype_val.comp continuous_snd).div_const (θ.2 : ℝ)).mul
      (continuous_const.div ((expenditure_price_continuous x).comp continuous_fst)
        (fun η => (expenditure_pos η.1 hx).ne'))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact hf.mul continuous_const

/-- Every feasible reference bundle admits a global continuous feasible recovery selection. -/
theorem budgetSet_continuous_selection {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (hx : x ∈ BudgetSet θ.1 θ.2) :
    ∃ s : PriceIncome k → NonnegativeOrthant k, Continuous s ∧ s θ = x ∧
      ∀ η, s η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    exact ⟨fun _ => ZeroBundle k, continuous_const, rfl,
      fun η => by change Expenditure η.1 (ZeroBundle k) ≤ (η.2 : ℝ)
                  rw [expenditure_zero]; exact η.2.property⟩
  have hy : 0 < (θ.2 : ℝ) := (expenditure_pos θ.1 hx0).trans_le hx
  exact ⟨BudgetAdjustment θ x, budgetAdjustment_continuous θ hx0,
    budgetAdjustment_self θ hy hx0, budgetAdjustment_feasible θ hy hx⟩

/-- The budget correspondence is lower semicontinuous, including at zero income. -/
theorem budgetSet_sequentialLower {k : ℕ} :
    SequentialLower (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) :=
  sequentialLower_of_continuous_selections budgetSet_continuous_selection

/-- Limits of feasible bundles are feasible at the limiting prices and income. -/
theorem budgetSet_sequentialUpper {k : ℕ} :
    SequentialUpper (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ x θ₀ x₀ hθ hx hm
  have he := expenditure_joint_continuous.continuousAt.tendsto.comp
    ((continuous_fst.continuousAt.tendsto.comp hθ).prodMk_nhds hx)
  have hy := (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hθ
  exact le_of_tendsto_of_tendsto he hy (Filter.Eventually.of_forall hm)

/-- All nearby budgets fit in one compact coordinate box. -/
theorem budgetSet_localCompactBound {k : ℕ} :
    LocalCompactBound (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ
  let b : Fin k → ℝ := fun j => ((θ.2 : ℝ) + 1) / (θ.1.val j / 2)
  let K := (Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹' Set.Icc 0 b
  have hK : IsCompact K :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  refine ⟨K, hK, ?_⟩
  have hyc : Continuous (fun η : PriceIncome k => (η.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hy : ∀ᶠ η : PriceIncome k in 𝓝 θ, (η.2 : ℝ) < (θ.2 : ℝ) + 1 :=
    (hyc.continuousAt (x := θ)).eventually
      (isOpen_Iio.mem_nhds (show (θ.2 : ℝ) < (θ.2 : ℝ) + 1 by linarith))
  have hp : ∀ᶠ η : PriceIncome k in 𝓝 θ, ∀ j, θ.1.val j / 2 < η.1.val j := by
    apply Filter.eventually_all.mpr
    intro j
    have hjc : Continuous (fun η : PriceIncome k => η.1.val j) :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    have hj : θ.1.val j / 2 < θ.1.val j := by have h := θ.1.property j; linarith
    exact hjc.continuousAt.eventually (isOpen_Ioi.mem_nhds hj)
  filter_upwards [hy, hp] with η hy hp
  intro x hx
  refine ⟨x.property, fun j => ?_⟩
  apply (le_div_iff₀ (by have h := θ.1.property j; positivity)).mpr
  have h₁ := commodity_expenditure_le η.1 x j
  have h₂ := mul_le_mul_of_nonneg_right (hp j).le (x.property j)
  change Expenditure η.1 x ≤ (η.2 : ℝ) at hx
  change x.val j * (θ.1.val j / 2) ≤ (θ.2 : ℝ) + 1
  nlinarith

end Kreps.ConsumerDemand
