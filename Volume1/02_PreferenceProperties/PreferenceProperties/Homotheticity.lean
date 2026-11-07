/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.GeneralContinuousRepresentation
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Homothetic preferences and homogeneous utilities

Kreps I, Definitions 2.17-2.18 and the easy direction of Proposition 2.19, p. 44.
The scalar domain includes zero. A cone here requires closure under nonnegative
scaling; it need not be convex or closed under addition.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- **Definition 2.18:** closure under all nonnegative scalar multiples. -/
def NonnegativeCone {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S

/-- Scalar multiplication as an operation inside the cone domain. -/
def ScaleInCone {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : NonnegativeCone S) (t : ℝ≥0) (x : S) : S :=
  ⟨(t : ℝ) • x.val, hS x.val x.property t t.property⟩

/-- **Definition 2.18:** homogeneity of a specified nonnegative degree. -/
def HomogeneousOfDegree {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : NonnegativeCone S) (α : ℝ≥0) (u : S → ℝ) : Prop :=
  ∀ t x, u (ScaleInCone hS t x) = (t : ℝ) ^ (α : ℝ) * u x

/-- Degree one is ordinary scalar homogeneity, including the zero scalar. -/
theorem homogeneousOfDegree_one_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : NonnegativeCone S) (u : S → ℝ) :
    HomogeneousOfDegree hS 1 u ↔ ∀ t x, u (ScaleInCone hS t x) = (t : ℝ) * u x := by
  simp only [HomogeneousOfDegree, NNReal.coe_one, Real.rpow_one]

/-- The nonnegative orthant is a cone in the book's sense. -/
theorem orthant_nonnegativeCone (k : ℕ) :
    NonnegativeCone (Set.Ici (0 : Fin k → ℝ)) := by
  intro x hx t ht j
  exact mul_nonneg ht (hx j)

/-- The zero commodity bundle. -/
def OrthantZero (k : ℕ) : NonnegativeOrthant k := ⟨0, le_rfl⟩

/-- Nonnegative scalar multiplication of a consumption bundle. -/
def ScaleBundle {k : ℕ} (t : ℝ≥0) (x : NonnegativeOrthant k) : NonnegativeOrthant k :=
  ⟨fun j => (t : ℝ) * x.val j, fun j => mul_nonneg t.property (x.property j)⟩

/-- Bundle scaling is the general cone operation specialized to the orthant. -/
theorem scaleBundle_eq_cone {k : ℕ} (t : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle t x = ScaleInCone (orthant_nonnegativeCone k) t x := rfl

/-- Scaling by zero gives the origin. -/
theorem scaleBundle_zero {k : ℕ} (x : NonnegativeOrthant k) :
    ScaleBundle 0 x = OrthantZero k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, OrthantZero]

/-- Scaling by one preserves the bundle. -/
theorem scaleBundle_one {k : ℕ} (x : NonnegativeOrthant k) : ScaleBundle 1 x = x := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle]

/-- Every scalar leaves the origin fixed. -/
theorem scaleBundle_origin {k : ℕ} (t : ℝ≥0) :
    ScaleBundle t (OrthantZero k) = OrthantZero k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, OrthantZero]

/-- Successive scalings multiply their factors. -/
theorem scaleBundle_mul {k : ℕ} (t s : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle (t * s) x = ScaleBundle t (ScaleBundle s x) := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, mul_assoc]

/-- Every nonzero scaling can be undone within the nonnegative orthant. -/
theorem scaleBundle_inv {k : ℕ} {t : ℝ≥0} (ht : t ≠ 0) (x : NonnegativeOrthant k) :
    ScaleBundle t⁻¹ (ScaleBundle t x) = x := by
  rw [← scaleBundle_mul, inv_mul_cancel₀ ht, scaleBundle_one]

/-- Joint continuity of the scalar and the bundle. -/
theorem scaleBundle_continuous {k : ℕ} :
    Continuous (fun p : ℝ≥0 × NonnegativeOrthant k => ScaleBundle p.1 p.2) :=
  (continuous_pi fun j => (NNReal.continuous_coe.comp continuous_fst).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- A ray is continuous in its nonnegative scalar. -/
theorem scaleBundle_ray_continuous {k : ℕ} (x : NonnegativeOrthant k) :
    Continuous (fun t : ℝ≥0 => ScaleBundle t x) :=
  scaleBundle_continuous.comp (continuous_id.prodMk continuous_const)

/-- Iterating a contraction along a ray converges to the origin. -/
theorem scaleBundle_pow_tendsto_zero {k : ℕ} {t : ℝ≥0} (ht : t < 1)
    (x : NonnegativeOrthant k) :
    Filter.Tendsto (fun m : ℕ => ScaleBundle (t ^ m) x) Filter.atTop
      (nhds (OrthantZero k)) := by
  simpa only [Function.comp_def, scaleBundle_zero] using
    (scaleBundle_ray_continuous x).continuousAt.tendsto.comp
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ht)

/-- **Definition 2.17:** every common nonnegative scaling preserves weak preference. -/
def HomotheticPreference {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x y t, r x y → r (ScaleBundle t x) (ScaleBundle t y)

/-- Positive scaling preserves a comparison in both directions. -/
theorem homothetic_scale_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    r (ScaleBundle t x) (ScaleBundle t y) ↔ r x y := by
  constructor
  · intro h
    simpa only [scaleBundle_inv (ne_of_gt ht)] using hh _ _ t⁻¹ h
  · exact hh x y t

/-- Positive scaling preserves strict preference, while zero is deliberately excluded here. -/
theorem homothetic_scale_strict_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    Strict r (ScaleBundle t x) (ScaleBundle t y) ↔ Strict r x y :=
  and_congr (homothetic_scale_iff hh ht x y) (not_congr (homothetic_scale_iff hh ht y x))

/-- Positive scaling preserves indifference in both directions. -/
theorem homothetic_scale_indifferent_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    Indifferent r (ScaleBundle t x) (ScaleBundle t y) ↔ Indifferent r x y :=
  and_congr (homothetic_scale_iff hh ht x y) (homothetic_scale_iff hh ht y x)

/-- Degree-one homogeneous utility on the nonnegative commodity orthant. -/
def HomogeneousUtility {k : ℕ} (u : NonnegativeOrthant k → ℝ) : Prop :=
  ∀ t x, u (ScaleBundle t x) = (t : ℝ) * u x

/-- The specialized definition agrees with the general cone definition at degree one. -/
theorem homogeneousUtility_iff_degree_one {k : ℕ} (u : NonnegativeOrthant k → ℝ) :
    HomogeneousUtility u ↔ HomogeneousOfDegree (orthant_nonnegativeCone k) 1 u := by
  exact (homogeneousOfDegree_one_iff (orthant_nonnegativeCone k)
    (fun x : Set.Ici (0 : Fin k → ℝ) => u ⟨x.val, x.property⟩)).symm

/-- Degree-one homogeneity forces utility at the origin to be zero. -/
theorem homogeneousUtility_origin {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : u (OrthantZero k) = 0 := by
  have h := hh 0 (OrthantZero k)
  simpa only [scaleBundle_zero, NNReal.coe_zero, zero_mul] using h

/-- A homogeneous utility representation gives homothetic preferences. -/
theorem homogeneous_represents_homothetic {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hu : Represents u r) (hh : HomogeneousUtility u) : HomotheticPreference r := by
  intro x y t hxy
  apply (hu _ _).mpr
  rw [hh, hh]
  exact mul_le_mul_of_nonneg_left ((hu x y).mp hxy) t.property

/-- **Proposition 2.19**, representation-to-preference direction. -/
theorem proposition_2_19_forward {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hu : Represents u r) (hc : Continuous u) (hh : HomogeneousUtility u) :
    ContinuousPreference r ∧ HomotheticPreference r :=
  ⟨proposition_2_9_forward hu hc, homogeneous_represents_homothetic hu hh⟩

end Kreps.PreferenceProperties
