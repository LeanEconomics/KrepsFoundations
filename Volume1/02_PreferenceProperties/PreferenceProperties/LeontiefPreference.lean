/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.LinearPreference

/-!
# Leontief utility on two goods

Kreps I, Problem 2.9b, p. 47. For positive α and β, `min (x₁/α) (x₂/β)`
gives monotone, locally insatiable, convex, semi-strictly convex and continuous
preferences. Neither strict monotonicity nor strict convexity holds. The two
rays describing each indifference curve are stated as an exact set condition.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The fixed-proportions utility in Problem 2.9b. -/
noncomputable def LeontiefUtility (α β : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  min (x.val 0 / α) (x.val 1 / β)

/-- Positive scale parameters give nondecreasing Leontief utility. -/
theorem leontiefUtility_monotone {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Monotone (LeontiefUtility α β) := by
  intro x y hxy
  exact min_le_min (div_le_div_of_nonneg_right (hxy 0) hα.le)
    (div_le_div_of_nonneg_right (hxy 1) hβ.le)

/-- Increasing both goods strictly raises the minimum of their normalized quantities. -/
theorem leontiefPreference_strictAllIncrease {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictAllIncreasePreference (UtilityPref (LeontiefUtility α β)) := by
  intro x y hxy
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ _).mpr
  exact lt_min ((min_le_left _ _).trans_lt (div_lt_div_of_pos_right (hxy 0) hα))
    ((min_le_right _ _).trans_lt (div_lt_div_of_pos_right (hxy 1) hβ))

/-- The minimum of these two affine functions satisfies Jensen's concavity inequality. -/
theorem leontiefUtility_concave (α β : ℝ) :
    ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) (LeontiefUtility α β) := by
  intro x y a ha
  change a * min (x.val 0 / α) (x.val 1 / β) +
    (1 - a) * min (y.val 0 / α) (y.val 1 / β) ≤
    min ((a * x.val 0 + (1 - a) * y.val 0) / α)
      ((a * x.val 1 + (1 - a) * y.val 1) / β)
  apply le_min
  · calc
      _ ≤ a * (x.val 0 / α) + (1 - a) * (y.val 0 / α) := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left _ _) ha.1)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ha.2))
      _ = _ := by ring
  · calc
      _ ≤ a * (x.val 1 / β) + (1 - a) * (y.val 1 / β) := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_right _ _) ha.1)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (sub_nonneg.mpr ha.2))
      _ = _ := by ring

/-- The minimum is continuous, including at its corner and on the coordinate axes. -/
theorem leontiefUtility_continuous (α β : ℝ) : Continuous (LeontiefUtility α β) := by
  have h0 : Continuous (fun x : NonnegativeOrthant 2 => x.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun x : NonnegativeOrthant 2 => x.val 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact (h0.div_const α).min (h1.div_const β)

/-- No amount of the first good raises utility when the second good is absent. -/
theorem leontiefUtility_first_axis {α : ℝ} (hα : 0 < α) (β : ℝ)
    {x : NonnegativeOrthant 2} (hx : x.val 1 = 0) : LeontiefUtility α β x = 0 := by
  unfold LeontiefUtility
  rw [hx, zero_div, min_eq_right (div_nonneg (x.property 0) hα.le)]

/-- The first coordinate axis refutes strict monotonicity. -/
theorem leontiefPreference_not_strictlyMonotone {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ¬StrictlyMonotonePreference (UtilityPref (LeontiefUtility α β)) := by
  let y := PairBundle 1 0 (by norm_num) le_rfl
  have hy : LeontiefUtility α β y = 0 :=
    leontiefUtility_first_axis hα β (by simp [y, PairBundle])
  have hz : LeontiefUtility α β (OrthantZero 2) = 0 := leontiefUtility_first_axis hα β rfl
  have hne : y ≠ OrthantZero 2 := by
    intro h
    have he := congrArg (fun x : NonnegativeOrthant 2 => x.val 0) h
    simp [y, PairBundle, OrthantZero] at he
  intro h
  apply (h y (OrthantZero 2) y.property hne).2
  change LeontiefUtility α β y ≤ LeontiefUtility α β (OrthantZero 2)
  rw [hy, hz]

/-- Mixing two distinct points on the first axis leaves utility zero, refuting strict convexity. -/
theorem leontiefPreference_not_strictlyConvex {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (LeontiefUtility α β)) := by
  let y := PairBundle 1 0 (by norm_num) le_rfl
  have hy : LeontiefUtility α β y = 0 :=
    leontiefUtility_first_axis hα β (by simp [y, PairBundle])
  have hz : LeontiefUtility α β (OrthantZero 2) = 0 := leontiefUtility_first_axis hα β rfl
  have hne : y ≠ OrthantZero 2 := by
    intro h
    have he := congrArg (fun x : NonnegativeOrthant 2 => x.val 0) h
    simp [y, PairBundle, OrthantZero] at he
  have hp : UtilityPref (LeontiefUtility α β) y (OrthantZero 2) := by
    change LeontiefUtility α β (OrthantZero 2) ≤ LeontiefUtility α β y
    rw [hy, hz]
  intro h
  have hs := h y (OrthantZero 2) hne hp (1 / 2) (by constructor <;> norm_num)
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  have hgt := (strict_iff_utility_lt hu _ _).mp hs
  have hm : LeontiefUtility α β
      (Mix (convex_Ici (0 : Fin 2 → ℝ)) y (OrthantZero 2) (1 / 2)
        (by constructor <;> norm_num)) = 0 :=
    leontiefUtility_first_axis hα β (by simp [Mix, y, PairBundle, OrthantZero])
  exact not_lt_of_ge hz.ge (hgt.trans_eq hm)

/-- Leontief utility is degree-one homogeneous. -/
theorem leontiefUtility_homogeneous (α β : ℝ) : HomogeneousUtility (LeontiefUtility α β) := by
  intro t x
  change min (((t : ℝ) * x.val 0) / α) (((t : ℝ) * x.val 1) / β) =
    (t : ℝ) * min (x.val 0 / α) (x.val 1 / β)
  rw [mul_min_of_nonneg (a := (t : ℝ)) _ _ t.property]
  congr 1 <;> ring

/-- A level curve consists of a vertical ray and a horizontal ray meeting at `(αc,βc)`. -/
theorem leontief_indifference_curve {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (p x : NonnegativeOrthant 2) :
    Indifferent (UtilityPref (LeontiefUtility α β)) x p ↔
      (x.val 0 = α * LeontiefUtility α β p ∧ β * LeontiefUtility α β p ≤ x.val 1) ∨
      (x.val 1 = β * LeontiefUtility α β p ∧ α * LeontiefUtility α β p ≤ x.val 0) := by
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  rw [indifferent_iff_utility_eq hu]
  change min (x.val 0 / α) (x.val 1 / β) = LeontiefUtility α β p ↔ _
  constructor
  · intro h
    rcases min_eq_iff.mp h with ⟨he, hle⟩ | ⟨he, hle⟩
    · rw [he] at hle
      exact Or.inl ⟨by simpa [mul_comm] using (div_eq_iff (ne_of_gt hα)).mp he,
        by simpa [mul_comm] using (le_div_iff₀ hβ).mp hle⟩
    · rw [he] at hle
      exact Or.inr ⟨by simpa [mul_comm] using (div_eq_iff (ne_of_gt hβ)).mp he,
        by simpa [mul_comm] using (le_div_iff₀ hα).mp hle⟩
  · rintro (⟨he, hle⟩ | ⟨he, hle⟩)
    · have hd : x.val 0 / α = LeontiefUtility α β p :=
        (div_eq_iff (ne_of_gt hα)).mpr (by simpa [mul_comm] using he)
      rw [hd]
      exact min_eq_left ((le_div_iff₀ hβ).mpr (by simpa [mul_comm] using hle))
    · have hd : x.val 1 / β = LeontiefUtility α β p :=
        (div_eq_iff (ne_of_gt hβ)).mpr (by simpa [mul_comm] using he)
      rw [hd]
      exact min_eq_right ((le_div_iff₀ hα).mpr (by simpa [mul_comm] using hle))

/-- **Problem 2.9b:** all seven requested preference properties. -/
theorem problem_2_9b {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    MonotonePreference (UtilityPref (LeontiefUtility α β)) ∧
    ¬StrictlyMonotonePreference (UtilityPref (LeontiefUtility α β)) ∧
    LocallyInsatiable (UtilityPref (LeontiefUtility α β)) ∧
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (LeontiefUtility α β)) ∧
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (LeontiefUtility α β)) ∧
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (LeontiefUtility α β)) ∧
    ContinuousPreference (UtilityPref (LeontiefUtility α β)) := by
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  have hc := leontiefUtility_concave α β
  exact ⟨(proposition_2_2_monotone hu).mpr (leontiefUtility_monotone hα hβ),
    leontiefPreference_not_strictlyMonotone hα β,
    strictAllIncrease_locallyInsatiable (leontiefPreference_strictAllIncrease hα hβ),
    proposition_2_8a_concave hu hc, leontiefPreference_not_strictlyConvex hα β,
    (proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc),
    proposition_2_9_forward hu (leontiefUtility_continuous α β)⟩

end Kreps.PreferenceProperties
