/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConcaveUtility
import PreferenceProperties.MonotonicityExamples

/-!
# Product utility on the two-good orthant

Elementary mixture inequalities used in the exact counterexamples of Kreps I,
Problem 2.8. The domain includes its axes; no interior-only assumption is hidden
in the weak quasi-concavity result.
-/

namespace Kreps.PreferenceProperties

/-- The product of the two nonnegative commodity quantities. -/
def TwoGoodProduct (x : NonnegativeOrthant 2) : ℝ := x.val 0 * x.val 1

/-- Along oppositely ordered coordinates the product exceeds its chord. -/
theorem product_mix_ge_average_of_cross (x₀ x₁ y₀ y₁ a : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hcross : (x₀ - y₀) * (x₁ - y₁) ≤ 0) :
    a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) ≤
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have ht : 0 ≤ a * (1 - a) := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have hneg := mul_nonpos_of_nonneg_of_nonpos ht hcross
  nlinarith

/-- Nonnegative two-coordinate products are quasi-concave under convex mixing. -/
theorem product_mix_ge_min (x₀ x₁ y₀ y₁ a : ℝ)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (ha : a ∈ Set.Icc 0 1) :
    min (x₀ * x₁) (y₀ * y₁) ≤
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
  have hmean : min (x₀ * x₁) (y₀ * y₁) ≤
      a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) := by
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (min_le_left (x₀ * x₁) (y₀ * y₁))),
      mul_nonneg hb (sub_nonneg.mpr (min_le_right (x₀ * x₁) (y₀ * y₁)))]
  by_cases h₀ : x₀ ≤ y₀
  · by_cases h₁ : x₁ ≤ y₁
    · apply (min_le_left _ _).trans
      exact mul_le_mul
        (show x₀ ≤ a * x₀ + (1 - a) * y₀ by
          nlinarith [mul_nonneg hb (sub_nonneg.mpr h₀)])
        (show x₁ ≤ a * x₁ + (1 - a) * y₁ by
          nlinarith [mul_nonneg hb (sub_nonneg.mpr h₁)]) hx₁
        (add_nonneg (mul_nonneg ha.1 hx₀) (mul_nonneg hb hy₀))
    · apply hmean.trans (product_mix_ge_average_of_cross x₀ x₁ y₀ y₁ a ha _)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h₀)
        (sub_nonneg.mpr (le_of_not_ge h₁))
  · by_cases h₁ : y₁ ≤ x₁
    · apply (min_le_right _ _).trans
      exact mul_le_mul
        (show y₀ ≤ a * x₀ + (1 - a) * y₀ by
          nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (le_of_not_ge h₀))])
        (show y₁ ≤ a * x₁ + (1 - a) * y₁ by
          nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr h₁)]) hy₁
        (add_nonneg (mul_nonneg ha.1 hx₀) (mul_nonneg hb hy₀))
    · apply hmean.trans (product_mix_ge_average_of_cross x₀ x₁ y₀ y₁ a ha _)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_not_ge h₀))
        (sub_nonpos.mpr (le_of_not_ge h₁))

/-- Product utility is continuous on the entire nonnegative orthant. -/
theorem twoGoodProduct_continuous : Continuous TwoGoodProduct :=
  ((continuous_apply 0).comp continuous_subtype_val).mul
    ((continuous_apply 1).comp continuous_subtype_val)

/-- Quasi-concavity includes zero-product boundary bundles. -/
theorem twoGoodProduct_quasiConcave :
    QuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) TwoGoodProduct := by
  intro x y a ha
  exact product_mix_ge_min (x.val 0) (x.val 1) (y.val 0) (y.val 1) a
    (x.property 0) (x.property 1) (y.property 0) (y.property 1) ha

/-- Strictly oppositely ordered coordinates give a strict chord inequality. -/
theorem product_mix_gt_average_of_cross (x₀ x₁ y₀ y₁ a : ℝ)
    (ha : a ∈ Set.Ioo 0 1) (hcross : (x₀ - y₀) * (x₁ - y₁) < 0) :
    a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) <
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have ht : 0 < a * (1 - a) := mul_pos ha.1 (sub_pos.mpr ha.2)
  have hneg := mul_neg_of_pos_of_neg ht hcross
  nlinarith

/-- Distinct positive-product bundles improve strictly over the lower-product endpoint. -/
theorem product_mix_gt_lower (x₀ x₁ y₀ y₁ a : ℝ)
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 < y₀) (hy₁ : 0 < y₁)
    (hprod : y₀ * y₁ ≤ x₀ * x₁) (hne : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (ha : a ∈ Set.Ioo 0 1) :
    y₀ * y₁ < (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have hmean : y₀ * y₁ ≤ a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) := by
    nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr hprod)]
  rcases lt_trichotomy x₀ y₀ with h₀ | h₀ | h₀
  · have h₁ : y₁ < x₁ := by
      by_contra h
      have hle := mul_le_mul_of_nonneg_left (le_of_not_gt h) hx₀
      have hlt := mul_lt_mul_of_pos_right h₀ hy₁
      exact not_lt_of_ge hprod (hle.trans_lt hlt)
    exact hmean.trans_lt (product_mix_gt_average_of_cross x₀ x₁ y₀ y₁ a ha
      (mul_neg_of_neg_of_pos (sub_neg.mpr h₀) (sub_pos.mpr h₁)))
  · have hn₁ : x₁ ≠ y₁ := hne.resolve_left (not_ne_iff.mpr h₀)
    have h₁ : y₁ < x₁ := by
      rw [h₀] at hprod
      exact lt_of_le_of_ne ((mul_le_mul_iff_right₀ hy₀).mp hprod) (Ne.symm hn₁)
    have hm₀ : a * x₀ + (1 - a) * y₀ = y₀ := by rw [h₀]; ring
    have hm₁ : y₁ < a * x₁ + (1 - a) * y₁ := by
      nlinarith [mul_pos ha.1 (sub_pos.mpr h₁)]
    rw [hm₀]
    exact mul_lt_mul_of_pos_left hm₁ hy₀
  · by_cases h₁ : x₁ < y₁
    · exact hmean.trans_lt (product_mix_gt_average_of_cross x₀ x₁ y₀ y₁ a ha
        (mul_neg_of_pos_of_neg (sub_pos.mpr h₀) (sub_neg.mpr h₁)))
    · have hm₀ : y₀ < a * x₀ + (1 - a) * y₀ := by
        nlinarith [mul_pos ha.1 (sub_pos.mpr h₀)]
      have hm₁ : y₁ ≤ a * x₁ + (1 - a) * y₁ := by
        nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr (le_of_not_gt h₁))]
      exact (mul_lt_mul_of_pos_right hm₀ hy₁).trans_le
        (mul_le_mul_of_nonneg_left hm₁ (hy₀.trans hm₀).le)

/-- Positive product is equivalent to positive quantities on the nonnegative orthant. -/
theorem twoGoodProduct_pos_iff (x : NonnegativeOrthant 2) :
    0 < TwoGoodProduct x ↔ 0 < x.val 0 ∧ 0 < x.val 1 := by
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hp | hn
    · exact hp
    · exact False.elim (not_lt_of_ge (x.property 0) hn.1)
  · rintro ⟨h₀, h₁⟩
    exact mul_pos h₀ h₁

/-- At positive rank, distinct weakly better bundles yield a strict product improvement. -/
theorem twoGoodProduct_mix_strict {x y : NonnegativeOrthant 2}
    (hy : 0 < TwoGoodProduct y) (hxy : TwoGoodProduct y ≤ TwoGoodProduct x) (hne : x ≠ y)
    {a : ℝ} (ha : a ∈ Set.Ioo 0 1) :
    TwoGoodProduct y < TwoGoodProduct
      (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ⟨ha.1.le, ha.2.le⟩) := by
  have hcoords : x.val 0 ≠ y.val 0 ∨ x.val 1 ≠ y.val 1 := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  have hyp := (twoGoodProduct_pos_iff y).mp hy
  exact product_mix_gt_lower (x.val 0) (x.val 1) (y.val 0) (y.val 1) a
    (x.property 0) hyp.1 hyp.2 hxy hcoords ha

/-- An interior mixture with a positive-product endpoint has positive product. -/
theorem twoGoodProduct_mix_pos {x y : NonnegativeOrthant 2}
    (hx : 0 < TwoGoodProduct x) {a : ℝ} (ha : a ∈ Set.Ioo 0 1) :
    0 < TwoGoodProduct (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ⟨ha.1.le, ha.2.le⟩) := by
  have hxp := (twoGoodProduct_pos_iff x).mp hx
  apply mul_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos ha.1 hxp.1)
      (mul_nonneg (sub_pos.mpr ha.2).le (y.property 0))
  · exact add_pos_of_pos_of_nonneg (mul_pos ha.1 hxp.2)
      (mul_nonneg (sub_pos.mpr ha.2).le (y.property 1))

end Kreps.PreferenceProperties
