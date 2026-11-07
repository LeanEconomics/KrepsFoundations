/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AffineIntervalContinuation

/-!
# Gluing interval coordinates in fixed cardinal units

If every chart transition is a translation, a global scale normalized on a seed chart uses
the same unit in every chart. This specialization preserves the common units obtained by
calibrating additive utility charts against fixed companion coordinates.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Constants attached to an open cover of a connected set agree when they agree on overlaps. -/
theorem open_cover_constants_eq {X ι Y : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hUS : ∀ i, U i ⊆ S) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (v : ι → Y) (he : ∀ i j, (U i ∩ U j).Nonempty → v i = v j)
    {seed : ι} (hne : (U seed).Nonempty) :
    ∀ i, (U i).Nonempty → v i = v seed := by
  classical
  choose c hc using fun x : S => hcover x x.property
  let f : S → Y := fun x => v (c x)
  have hlocal : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨Subtype.val ⁻¹' U (c x), (hU (c x)).preimage continuous_subtype_val, hc x, ?_⟩
    intro y hy
    exact he (c y) (c x) ⟨y, hc y, hy⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  obtain ⟨z, hz⟩ := hne
  intro i hi
  obtain ⟨x, hx⟩ := hi
  calc
    v i = f ⟨x, hUS i hx⟩ := he i (c ⟨x, hUS i hx⟩) ⟨x, hx, hc ⟨x, hUS i hx⟩⟩
    _ = f ⟨z, hUS seed hz⟩ := hlocal.apply_eq_of_preconnectedSpace _ _
    _ = v seed := he (c ⟨z, hUS seed hz⟩) seed ⟨z, hc ⟨z, hUS seed hz⟩, hz⟩

/-- Translation transitions force all affine chart slopes to equal the normalized seed slope. -/
theorem PositiveAffineIntervalAtlas.slopes_eq_one {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) {seed : ι}
    (hne : (a.domain seed).Nonempty)
    (ht : ∀ i j, ∃ B : ℝ, ∀ x ∈ a.domain i ∩ a.domain j,
      a.coord i x = a.coord j x + B)
    {f : ℝ → ℝ} (hseed : ∀ x ∈ a.domain seed, f x = a.coord seed x)
    {A B : ι → ℝ} (he : ∀ i x, x ∈ a.domain i → f x = A i * a.coord i x + B i) :
    ∀ i, (a.domain i).Nonempty → A i = 1 := by
  have hsame : ∀ i j, (a.domain i ∩ a.domain j).Nonempty → A i = A j := by
    intro i j hij
    obtain ⟨C, hC⟩ := ht i j
    have hcoeff := affine_coefficients_unique (a.increasing j)
      ((a.isOpen i).inter (a.isOpen j)) hij inter_subset_right
      (A := A i) (B := A i * C + B i) (C := A j) (D := B j) (fun x hx => by
        have hfi := he i x hx.1
        have hfj := he j x hx.2
        rw [hC x hx] at hfi
        nlinarith)
    exact hcoeff.1
  have hunit : A seed = 1 := by
    have hcoeff := affine_coefficients_unique (a.increasing seed) (a.isOpen seed)
      hne Subset.rfl (A := A seed) (B := B seed) (C := 1) (D := 0) (fun x hx => by
        have hfx := he seed x hx
        rw [hseed x hx] at hfx
        simpa only [one_mul, add_zero] using hfx.symm)
    exact hcoeff.1
  intro i hi
  exact (open_cover_constants_eq hS.isPreconnected a.domain a.isOpen a.subset a.cover
    A hsame hne i hi).trans hunit

/-- An atlas with translation transitions glues without changing any chart's cardinal unit. -/
theorem PositiveAffineIntervalAtlas.globalize_translations {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty)
    (ht : ∀ i j, ∃ B : ℝ, ∀ x ∈ a.domain i ∩ a.domain j,
      a.coord i x = a.coord j x + B) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ a.domain seed, f x = a.coord seed x) ∧
      ∀ i, ∃ B : ℝ, ∀ x ∈ a.domain i, f x = a.coord i x + B := by
  classical
  obtain ⟨f, hc, hm, hseed, hf⟩ := a.globalize hS seed hne
  choose A B _ he using hf
  have hA := a.slopes_eq_one hS hne ht hseed he
  refine ⟨f, hc, hm, hseed, fun i => ⟨B i, fun x hx => ?_⟩⟩
  simpa only [hA i ⟨x, hx⟩, one_mul] using he i x hx

end Kreps.PreferenceProperties
