/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveSeparability

/-!
# Removing constant commodity factors

Deleting singleton factors preserves the order, topology and strong separability
of a product. Additive coordinate utilities on the remaining factors extend by
zero on every deleted factor.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*} (P : I → Prop)

/-- Insert a fixed baseline at each inactive coordinate. -/
noncomputable def ActiveCoordinateExtend (z : ∀ i, B i) (x : ∀ i : Subtype P, B i.val) :
    ∀ i, B i := by
  classical
  exact fun i => if h : P i then x ⟨i, h⟩ else z i

/-- Restrict a bundle to its active coordinates. -/
def ActiveCoordinateRestrict (x : ∀ i, B i) : ∀ i : Subtype P, B i.val := fun i => x i.val

/-- Extension leaves each active coordinate unchanged. -/
@[simp] theorem activeCoordinateExtend_active (z : ∀ i, B i)
    (x : ∀ i : Subtype P, B i.val) (i : Subtype P) :
    ActiveCoordinateExtend P z x i.val = x i := by
  simp only [ActiveCoordinateExtend, dite_eq_left i.property]

/-- Restriction recovers an extended active bundle. -/
@[simp] theorem activeCoordinateRestrict_extend (z : ∀ i, B i)
    (x : ∀ i : Subtype P, B i.val) :
    ActiveCoordinateRestrict P (ActiveCoordinateExtend P z x) = x := by
  funext i
  exact activeCoordinateExtend_active P z x i

/-- Singleton inactive factors make extension recover every original bundle. -/
@[simp] theorem activeCoordinateExtend_restrict (z x : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) :
    ActiveCoordinateExtend P z (ActiveCoordinateRestrict P x) = x := by
  classical
  funext i
  by_cases hi : P i
  · simp only [ActiveCoordinateExtend, dite_eq_left hi, ActiveCoordinateRestrict]
  · simp only [ActiveCoordinateExtend, dite_eq_right hi]
    exact (htriv i hi).elim _ _

/-- Extension by constant coordinates is continuous. -/
theorem activeCoordinateExtend_continuous [∀ i, TopologicalSpace (B i)] (z : ∀ i, B i) :
    Continuous (ActiveCoordinateExtend P z) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : P i
  · simpa only [ActiveCoordinateExtend, dite_eq_left hi] using
      continuous_apply (⟨i, hi⟩ : Subtype P)
  · simpa only [ActiveCoordinateExtend, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : ∀ j : Subtype P, B j.val => z i))

/-- Deleting singleton factors identifies the two product orders. -/
noncomputable def ActiveCoordinateOrderIso [∀ i, PartialOrder (B i)] (z : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) :
    (∀ i : Subtype P, B i.val) ≃o (∀ i, B i) where
  toFun := ActiveCoordinateExtend P z
  invFun := ActiveCoordinateRestrict P
  left_inv := activeCoordinateRestrict_extend P z
  right_inv := fun x => activeCoordinateExtend_restrict P z x htriv
  map_rel_iff' := by
    classical
    intro x y
    change (∀ i, ActiveCoordinateExtend P z x i ≤ ActiveCoordinateExtend P z y i) ↔
      (∀ i, x i ≤ y i)
    constructor
    · intro h i
      simpa only [activeCoordinateExtend_active] using h i.val
    · intro h i
      by_cases hi : P i
      · simpa only [ActiveCoordinateExtend, dite_eq_left hi] using h ⟨i, hi⟩
      · simp only [ActiveCoordinateExtend, dite_eq_right hi, le_refl]

/-- Extension commutes with replacing an arbitrary finite collection of active factors. -/
theorem activeCoordinateExtend_piecewise [DecidableEq I] (z : ∀ i, B i)
    (s : Finset (Subtype P)) (x y : ∀ i : Subtype P, B i.val) :
    ActiveCoordinateExtend P z (s.piecewise x y) =
      (s.image Subtype.val).piecewise (ActiveCoordinateExtend P z x)
        (ActiveCoordinateExtend P z y) := by
  classical
  funext i
  by_cases hi : P i
  · have hmem : i ∈ s.image Subtype.val ↔ (⟨i, hi⟩ : Subtype P) ∈ s := by
      constructor
      · intro h
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
        have hji : j = ⟨i, hi⟩ := Subtype.ext he
        simpa only [hji] using hj
      · exact Finset.mem_image_of_mem Subtype.val
    by_cases hs : (⟨i, hi⟩ : Subtype P) ∈ s
    · simp only [ActiveCoordinateExtend, dite_eq_left hi, Finset.piecewise,
        ite_eq_left hs, ite_eq_left (hmem.mpr hs)]
    · simp only [ActiveCoordinateExtend, dite_eq_left hi, Finset.piecewise,
        ite_eq_right hs, ite_eq_right (mt hmem.mp hs)]
  · have hmem : i ∉ s.image Subtype.val := by
      intro h
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp h
      exact hi (he ▸ j.property)
    simp only [ActiveCoordinateExtend, dite_eq_right hi, Finset.piecewise, ite_eq_right hmem]

/-- Strong separability restricts to the active commodity factors. -/
theorem stronglySeparable_activeCoordinates [DecidableEq I]
    {V : (∀ i, B i) → ℝ} (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) :
    StronglySeparable (UtilityPref (fun x => V (ActiveCoordinateExtend P z x))) := by
  intro s a b x y
  simp only [UtilityPref, activeCoordinateExtend_piecewise]
  exact hs (s.image Subtype.val) _ _ _ _

/-- Extend additive coordinate utilities by zero on inactive factors. -/
noncomputable def ActiveCoordinateUtility (w : ∀ i : Subtype P, B i.val → ℝ)
    (i : I) (x : B i) : ℝ := by
  classical
  exact if h : P i then w ⟨i, h⟩ x else 0

/-- Extending by zero does not change the active coordinates' utility sum. -/
theorem additiveUtility_activeCoordinates [Fintype I] [Fintype (Subtype P)]
    (w : ∀ i : Subtype P, B i.val → ℝ) (x : ∀ i, B i) :
    AdditiveUtility (ActiveCoordinateUtility P w) x =
      AdditiveUtility w (ActiveCoordinateRestrict P x) := by
  classical
  unfold AdditiveUtility
  calc
    _ = ∑ i ∈ Finset.univ.filter P, ActiveCoordinateUtility P w i (x i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hp : ¬ P i := fun hp => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      simp only [ActiveCoordinateUtility, dite_eq_right hp]
    _ = ∑ i : Subtype P, ActiveCoordinateUtility P w i.val (x i.val) :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [ActiveCoordinateUtility, dite_eq_left i.property, ActiveCoordinateRestrict]

/-- The inactive zero functions and the active continuous functions are all continuous. -/
theorem activeCoordinateUtility_continuous [∀ i, TopologicalSpace (B i)]
    {w : ∀ i : Subtype P, B i.val → ℝ} (hw : ∀ i, Continuous (w i)) (i : I) :
    Continuous (ActiveCoordinateUtility P w i) := by
  classical
  change Continuous (fun x => ActiveCoordinateUtility P w i x)
  by_cases hi : P i
  · simpa only [ActiveCoordinateUtility, dite_eq_left hi] using hw ⟨i, hi⟩
  · simpa only [ActiveCoordinateUtility, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : B i => (0 : ℝ)))

/-- Strict increase is retained, including its vacuous meaning on singleton factors. -/
theorem activeCoordinateUtility_strictMono [∀ i, PartialOrder (B i)]
    {w : ∀ i : Subtype P, B i.val → ℝ} (hw : ∀ i, StrictMono (w i))
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) (i : I) :
    StrictMono (ActiveCoordinateUtility P w i) := by
  classical
  change StrictMono (fun x => ActiveCoordinateUtility P w i x)
  by_cases hi : P i
  · simpa only [ActiveCoordinateUtility, dite_eq_left hi] using hw ⟨i, hi⟩
  · intro a b hab
    exact False.elim (hab.ne ((htriv i hi).elim a b))

/-- An active additive representation represents the full product after zero extension. -/
theorem represents_activeCoordinates [Fintype I] [Fintype (Subtype P)]
    {V : (∀ i, B i) → ℝ} (z : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i))
    {w : ∀ i : Subtype P, B i.val → ℝ}
    (hw : Represents (AdditiveUtility w)
      (UtilityPref (fun x => V (ActiveCoordinateExtend P z x)))) :
    Represents (AdditiveUtility (ActiveCoordinateUtility P w)) (UtilityPref V) := by
  intro x y
  have hh := hw (ActiveCoordinateRestrict P x) (ActiveCoordinateRestrict P y)
  simp only [UtilityPref, activeCoordinateExtend_restrict P z _ htriv] at hh
  simpa only [UtilityPref, additiveUtility_activeCoordinates] using hh

end Kreps.PreferenceProperties
