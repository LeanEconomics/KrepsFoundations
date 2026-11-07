/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RepresentationQuantifiers
import PreferenceProperties.TransformationExamples
import PreferenceProperties.Rationalization
import PreferenceProperties.PlateauProductPreference

/-!
# Why the representation table needs `some` rather than `all`

Kreps I, Problem 2.1, Table 2.1, p. 45. Increasing transformations preserve the
preference but need not preserve concavity, continuity, exact additive form,
the quasi-linear money normalization, or degree-one homogeneity.
The additive example has three nontrivial commodity blocks and continuous preference.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : X → X → Prop}

/-- Adding a constant preserves every ordinal comparison. -/
theorem represents_add_constant {u : X → ℝ} (hu : Represents u r) (c : ℝ) :
    Represents (fun x => u x + c) r := by
  intro x y
  simpa only [add_le_add_iff_right] using hu x y

/-- Multiplication by a positive constant preserves every ordinal comparison. -/
theorem represents_mul_positive {u : X → ℝ} (hu : Represents u r) {c : ℝ} (hc : 0 < c) :
    Represents (fun x => c * u x) r := by
  intro x y
  simpa only [mul_le_mul_iff_right₀ hc] using hu x y

/-- Concavity can hold for one representation and fail for another of the same convex preference. -/
theorem table_concave_not_all :
    ConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref (fun x : OneGood => x.val)) ∧
      SomeRepresentation (UtilityPref (fun x : OneGood => x.val))
        (ConcaveUtility (convex_Ici (0 : ℝ))) ∧
      ¬EveryRepresentation (UtilityPref (fun x : OneGood => x.val))
        (ConcaveUtility (convex_Ici (0 : ℝ))) := by
  have hu : Represents (fun x : OneGood => x.val) (UtilityPref (fun x : OneGood => x.val)) :=
    fun _ _ => Iff.rfl
  refine ⟨proposition_2_8a_concave hu identityUtility_concave,
    ⟨_, hu, identityUtility_concave⟩, ?_⟩
  intro hall
  exact convexWarp_not_concave
    (hall _ (proposition_1_20 hu convexWarp_strictMono))

/-- Convexity need not give even one concave representation, despite continuous preference. -/
theorem table_convex_not_some_concave :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref PlateauProductUtility) ∧
      ContinuousPreference (UtilityPref PlateauProductUtility) ∧
      ¬SomeRepresentation (UtilityPref PlateauProductUtility)
        (ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ))) :=
  ⟨problem_2_8a_first.2.1, problem_2_8a_first.2.2.1,
    plateauProductPreference_no_concave_representation⟩

/-- Continuity of preference guarantees a continuous representation, but not continuity of all. -/
theorem table_continuous_not_all :
    ContinuousPreference (UtilityPref (fun x : OneGood => x.val)) ∧
      SomeRepresentation (UtilityPref (fun x : OneGood => x.val)) Continuous ∧
      ¬EveryRepresentation (UtilityPref (fun x : OneGood => x.val)) Continuous := by
  have hu : Represents (fun x : OneGood => x.val) (UtilityPref (fun x : OneGood => x.val)) :=
    fun _ _ => Iff.rfl
  refine ⟨continuousPreference_of_continuous_utility continuous_subtype_val,
    ⟨_, hu, continuous_subtype_val⟩, ?_⟩
  intro hall
  exact jumpUtility_not_continuous
    (hall _ (proposition_1_20 hu jumpUtility_strictMono))

/-- Doubling a quasi-linear utility destroys its required money coefficient of one. -/
theorem doubled_quasiLinear_not_form [Nonempty X] (u : X → ℝ) :
    ¬QuasiLinearForm (fun p => 2 * QuasiLinearUtility u p) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rintro ⟨v, he⟩
  have h0 := congrArg (fun U => U (x, 0)) he
  have h1 := congrArg (fun U => U (x, 1)) he
  norm_num [QuasiLinearUtility] at h0 h1
  linarith

/-- For every quasi-linear preference on a nonempty goods domain, `all` is false. -/
theorem table_quasiLinear_not_all [Nonempty X]
    {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop} (hq : QuasiLinear r) :
    ¬EveryRepresentation r QuasiLinearForm := by
  obtain ⟨u, hu⟩ := hq
  intro hall
  exact doubled_quasiLinear_not_form u
    (hall _ (represents_mul_positive hu (by norm_num : (0 : ℝ) < 2)))

/-- Shifting a homogeneous representation by one violates the required value at the origin. -/
theorem shifted_homogeneous_not_homogeneous {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : ¬HomogeneousUtility (fun x => u x + 1) := by
  intro hs
  have hzero := homogeneousUtility_origin hh
  have hshift := homogeneousUtility_origin hs
  change u (OrthantZero k) + 1 = 0 at hshift
  linarith

/-- An ordinal homogeneous representation cannot make every representation homogeneous. -/
theorem homogeneous_not_every_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} {u : NonnegativeOrthant k → ℝ}
    (hu : Represents u r) (hh : HomogeneousUtility u) :
    ¬EveryRepresentation r HomogeneousUtility := by
  intro hall
  exact shifted_homogeneous_not_homogeneous hh (hall _ (represents_add_constant hu 1))

/-- Table 2.1, continuous homogeneous representation is `some`, never `all`. -/
theorem table_homogeneous_not_all {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r) :
    ¬EveryRepresentation r (fun u => Continuous u ∧ HomogeneousUtility u) := by
  obtain ⟨u, hu, _, huh⟩ := (proposition_2_19 k hr).mp ⟨hc, hh⟩
  intro hall
  exact homogeneous_not_every_representation hu huh (fun v hv => (hall v hv).2)

/-- Total quantity of three independent nonnegative commodities, in additive form. -/
def ThreeCommodityTotal (x : Fin 3 → ℝ≥0) : ℝ :=
  AdditiveUtility (fun (_ : Fin 3) (a : ℝ≥0) => (a : ℝ)) x

/-- Total quantity is nonnegative. -/
theorem threeCommodityTotal_nonneg (x : Fin 3 → ℝ≥0) : 0 ≤ ThreeCommodityTotal x := by
  change 0 ≤ ∑ i : Fin 3, (x i : ℝ)
  exact Finset.sum_nonneg (fun i _ => (x i).property)

/-- Squaring total quantity preserves its preference because all its values are nonnegative. -/
theorem squared_threeCommodityTotal_represents :
    Represents (fun x => ThreeCommodityTotal x ^ 2) (UtilityPref ThreeCommodityTotal) := by
  intro x y
  exact (sq_le_sq₀ (threeCommodityTotal_nonneg y) (threeCommodityTotal_nonneg x)).symm

/-- A nonzero cross difference rules out every exact additive decomposition of the square. -/
theorem squared_threeCommodityTotal_not_additive :
    ¬AdditiveForm (fun x => ThreeCommodityTotal x ^ 2) := by
  rintro ⟨w, he⟩
  have h00 := congrArg (fun U => U (![0, 0, 0] : Fin 3 → ℝ≥0)) he
  have h10 := congrArg (fun U => U (![1, 0, 0] : Fin 3 → ℝ≥0)) he
  have h01 := congrArg (fun U => U (![0, 1, 0] : Fin 3 → ℝ≥0)) he
  have h11 := congrArg (fun U => U (![1, 1, 0] : Fin 3 → ℝ≥0)) he
  norm_num [ThreeCommodityTotal, AdditiveUtility, Fin.sum_univ_succ] at h00 h10 h01 h11
  linarith

/-- Every commodity in the additive counterexample is nontrivial, independently of its context. -/
theorem threeCommodityTotal_nontrivial (i : Fin 3) :
    NontrivialBlock (UtilityPref ThreeCommodityTotal) i := by
  refine ⟨1, 0, fun _ => 0, ?_⟩
  change (ThreeCommodityTotal (Function.update (fun _ => 0) i 0) ≤
      ThreeCommodityTotal (Function.update (fun _ => 0) i 1)) ∧
    ¬(ThreeCommodityTotal (Function.update (fun _ => 0) i 1) ≤
      ThreeCommodityTotal (Function.update (fun _ => 0) i 0))
  fin_cases i <;>
    norm_num [ThreeCommodityTotal, AdditiveUtility, Fin.sum_univ_succ, Function.update]

/-- The counterexample satisfies the substantive three-nontrivial-block hypothesis. -/
theorem threeCommodityTotal_threeNontrivial :
    ThreeNontrivialBlocks (UtilityPref ThreeCommodityTotal) :=
  ⟨0, 1, 2, by decide, by decide, by decide, threeCommodityTotal_nontrivial 0,
    threeCommodityTotal_nontrivial 1, threeCommodityTotal_nontrivial 2⟩

/-- The additive counterexample's preference is rational, continuous, and strongly separable. -/
theorem threeCommodityTotal_preference_properties :
    Rational (UtilityPref ThreeCommodityTotal) ∧
      ContinuousPreference (UtilityPref ThreeCommodityTotal) ∧
      StronglySeparable (UtilityPref ThreeCommodityTotal) := by
  have hu : Represents (AdditiveUtility (fun (_ : Fin 3) (a : ℝ≥0) => (a : ℝ)))
      (UtilityPref ThreeCommodityTotal) := fun _ _ => Iff.rfl
  exact ⟨proposition_1_3a ThreeCommodityTotal,
    continuousPreference_of_additive hu (fun _ => NNReal.continuous_coe),
    proposition_2_14_additive hu⟩

/-- Strong separability need not make every representation additive, even with three active blocks.
-/
theorem table_additive_not_all :
    SomeRepresentation (UtilityPref ThreeCommodityTotal) AdditiveForm ∧
      ¬EveryRepresentation (UtilityPref ThreeCommodityTotal) AdditiveForm := by
  refine ⟨⟨ThreeCommodityTotal, (fun _ _ => Iff.rfl), (fun _ a => (a : ℝ)), rfl⟩, ?_⟩
  intro hall
  exact squared_threeCommodityTotal_not_additive (hall _ squared_threeCommodityTotal_represents)

end Kreps.PreferenceProperties
