/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.InteriorCoordinateBounds
import PreferenceProperties.InteriorAdditiveExtension
import PreferenceProperties.InteriorScalarRestriction

/-!
# Completing an interior additive representation at every attained endpoint

For Proposition 2.14, the interior scales have finite limits at any attained
endpoints, because the original scalar utility is continuous and strictly
increasing. The extended scales preserve all comparisons on the full product.
No endpoint boundedness, endpoint limits or full-domain representation is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Interior additive scales extend continuously and strictly to the complete interval product. -/
theorem exists_full_interval_additive_extension {I : Type*} [Fintype I] [Nontrivial I]
    {S : I → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hne : ∀ i, (interior (S i)).Nonempty) {V : (∀ i, S i) → ℝ}
    (hc : Continuous V) (hm : StrictMono V) {f : ∀ i, interior (S i) → ℝ}
    (hf : ∀ i, Continuous (f i)) (hfm : ∀ i, StrictMono (f i))
    (hr : Represents (AdditiveUtility f) (UtilityPref (V ∘ InteriorScalarInclusion))) :
    ∃ g : ∀ i, S i → ℝ, (∀ i, Continuous (g i)) ∧ (∀ i, StrictMono (g i)) ∧
      Represents (AdditiveUtility g) (UtilityPref V) ∧
      ∀ i (x : interior (S i)), g i (Set.inclusion interior_subset x) = f i x := by
  classical
  have hr' : ∀ x y : ∀ i, interior (S i),
      V (fun i => Set.inclusion interior_subset (x i)) ≤
          V (fun i => Set.inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i) := fun x y => hr y x
  have hext (i : I) : ∃ g : S i → ℝ, Continuous g ∧ StrictMono g ∧
      ∀ x : interior (S i), g (Set.inclusion interior_subset x) = f i x := by
    have hb := interior_additive_scale_bounds hS hne hc hm hr' i
    exact interval_exists_continuous_strictMono_extension (hS i) (hne i) (hf i) (hfm i)
      (fun x _ hx => hb.1 x hx) (fun x _ hx => hb.2 x hx)
  choose g hg hgm heq using hext
  refine ⟨g, hg, hgm, ?_, heq⟩
  apply additive_comparison_of_interior hS hne hc hm hg hgm
  intro x y
  simpa only [heq] using hr' x y

end Kreps.PreferenceProperties
