/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ProductQuasiconcavity
import PreferenceProperties.ContinuousUtility
import PreferenceProperties.Rationalization

/-!
# The plateau-product counterexample

Kreps I, Problem 2.8a, first utility. The scalar product is unchanged below four,
constant at four between four and eight, and reduced by four above eight.
Its preference is convex and continuous, but fails semi-strict convexity and
therefore admits no concave numerical representation.
-/

namespace Kreps.PreferenceProperties

/-- The continuous nondecreasing scalar transformation defining the first example. -/
noncomputable def ProductPlateau (s : ℝ) : ℝ := min s 4 + max (s - 8) 0

/-- The first branch in the book's displayed formula. -/
theorem productPlateau_below {s : ℝ} (hs : s ≤ 4) : ProductPlateau s = s := by
  have ht : s - 8 ≤ 0 := by linarith
  simp [ProductPlateau, min_eq_left hs, max_eq_right ht]

/-- The middle, flat branch includes both endpoints consistently. -/
theorem productPlateau_middle {s : ℝ} (hs : 4 ≤ s) (ht : s ≤ 8) :
    ProductPlateau s = 4 := by
  simp [ProductPlateau, min_eq_right hs, max_eq_right (sub_nonpos.mpr ht)]

/-- The upper branch in the book's displayed formula. -/
theorem productPlateau_above {s : ℝ} (hs : 8 ≤ s) : ProductPlateau s = s - 4 := by
  have ht : 4 ≤ s := by linarith
  rw [ProductPlateau, min_eq_right ht, max_eq_left (sub_nonneg.mpr hs)]
  ring

/-- Flattening the interval `[4,8]` preserves weak ordering of products. -/
theorem productPlateau_monotone : Monotone ProductPlateau := by
  intro a b hab
  exact add_le_add (min_le_min hab le_rfl) (max_le_max (sub_le_sub_right hab 8) le_rfl)

/-- The two corners do not create a discontinuity. -/
theorem productPlateau_continuous : Continuous ProductPlateau :=
  (continuous_id.min continuous_const).add
    ((continuous_id.sub continuous_const).max continuous_const)

/-- The exact utility `u₁` in Problem 2.8a. -/
noncomputable def PlateauProductUtility (x : NonnegativeOrthant 2) : ℝ :=
  ProductPlateau (TwoGoodProduct x)

/-- The first utility is continuous, despite having a flat range of product levels. -/
theorem plateauProductUtility_continuous : Continuous PlateauProductUtility :=
  productPlateau_continuous.comp twoGoodProduct_continuous

/-- Weakly increasing transformations preserve the product's quasi-concavity. -/
theorem plateauProductUtility_quasiConcave :
    QuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) PlateauProductUtility := by
  intro x y a ha
  change min (ProductPlateau (TwoGoodProduct x)) (ProductPlateau (TwoGoodProduct y)) ≤ _
  rw [← productPlateau_monotone.map_min]
  exact productPlateau_monotone (twoGoodProduct_quasiConcave x y a ha)

/-- A better endpoint can mix into the plateau of the worse endpoint. -/
theorem plateauProductUtility_not_semiStrict :
    ¬ SemiStrictlyQuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ))
      PlateauProductUtility := by
  intro h
  let x := PairBundle 3 3 (by norm_num) (by norm_num)
  let y := PairBundle 2 2 (by norm_num) (by norm_num)
  have hxy : PlateauProductUtility y < PlateauProductUtility x := by
    norm_num [x, y, PlateauProductUtility, ProductPlateau, TwoGoodProduct, PairBundle]
  have hm := h.2 x y hxy (1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num [x, y, PlateauProductUtility, ProductPlateau, TwoGoodProduct, PairBundle, Mix] at hm

/-- The first example's preference is not semi-strictly convex. -/
theorem plateauProductPreference_not_semiStrict :
    ¬ SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref PlateauProductUtility) := by
  intro h
  exact plateauProductUtility_not_semiStrict
    ((proposition_2_8b_semiStrict (fun _ _ => Iff.rfl)).mpr h)

/-- The failure is ordinal: no concave function can represent these preferences. -/
theorem plateauProductPreference_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref PlateauProductUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hc⟩
  exact plateauProductPreference_not_semiStrict
    ((proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc))

/-- **Problem 2.8a, first example:** convex and continuous, but not semi-strictly convex. -/
theorem problem_2_8a_first :
    Rational (UtilityPref PlateauProductUtility) ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref PlateauProductUtility) ∧
      ContinuousPreference (UtilityPref PlateauProductUtility) ∧
      ¬ SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
        (UtilityPref PlateauProductUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref PlateauProductUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _,
    (proposition_2_8b_quasi (fun _ _ => Iff.rfl)).mp plateauProductUtility_quasiConcave,
    continuousPreference_of_continuous_utility plateauProductUtility_continuous,
    plateauProductPreference_not_semiStrict, plateauProductPreference_no_concave_representation⟩

end Kreps.PreferenceProperties
