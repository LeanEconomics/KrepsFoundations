/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Local affine coordinates on real intervals

Supporting mathematics for the globalization of additive utility scales in Proposition 2.14.
Affine coefficients that agree locally are constant on a connected interval. Strict increase
provides uniqueness of the coefficients without imposing differentiability on the coordinates.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Near every point of `S`, one coordinate is a positive affine function of another. -/
def LocallyPositiveAffineOn (f g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
    ∃ A B : ℝ, 0 < A ∧ ∀ y ∈ U, f y = A * g y + B

/-- Two affine expressions in an increasing coordinate agree only with equal coefficients. -/
theorem affine_coefficients_unique {S U : Set ℝ} {g : ℝ → ℝ}
    (hg : StrictMonoOn g S) (hU : IsOpen U) (hne : U.Nonempty) (hUS : U ⊆ S)
    {A B C D : ℝ} (he : ∀ x ∈ U, A * g x + B = C * g x + D) :
    A = C ∧ B = D := by
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have hc : c ∈ U := hsub ⟨hac, hcb⟩
  have hd : d ∈ U := hsub ⟨hac.trans hcd, hdb⟩
  have hlt := hg (hUS hc) (hUS hd) hcd
  have hec := he c hc
  have hed := he d hd
  have hAC : A = C := by nlinarith
  exact ⟨hAC, by rw [hAC] at hec; linarith⟩

/-- Positive affine coefficients that exist locally on a nonempty interval exist globally. -/
theorem locallyPositiveAffineOn_global {S : Set ℝ} {f g : ℝ → ℝ}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hg : StrictMonoOn g S)
    (h : LocallyPositiveAffineOn f g S) :
    ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ S, f x = A * g x + B := by
  classical
  choose U hU hxU hUS A B hA he using fun x : S => h x x.property
  let c : S → ℝ × ℝ := fun x => (A x, B x)
  have hlocal : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨Subtype.val ⁻¹' U x, (hU x).preimage continuous_subtype_val, hxU x, ?_⟩
    intro y hy
    have hcoeff := affine_coefficients_unique hg ((hU x).inter (hU y))
      ⟨y, hy, hxU y⟩ (fun _ hz => hUS x hz.1)
      (fun z hz => (he x z hz.1).symm.trans (he y z hz.2))
    exact Prod.ext hcoeff.1.symm hcoeff.2.symm
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  obtain ⟨x, hx⟩ := hne
  refine ⟨A ⟨x, hx⟩, B ⟨x, hx⟩, hA ⟨x, hx⟩, fun y hy => ?_⟩
  have hc := hlocal.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩
  have hAy : A ⟨y, hy⟩ = A ⟨x, hx⟩ := congrArg Prod.fst hc
  have hBy : B ⟨y, hy⟩ = B ⟨x, hx⟩ := congrArg Prod.snd hc
  simpa only [hAy, hBy] using he ⟨y, hy⟩ y (hxU ⟨y, hy⟩)

/-- On an open set, a fixed positive affine relation is in particular a local one. -/
theorem locallyPositiveAffineOn_of_affine {S : Set ℝ} {f g : ℝ → ℝ}
    (hS : IsOpen S) {A B : ℝ} (hA : 0 < A)
    (he : ∀ x ∈ S, f x = A * g x + B) : LocallyPositiveAffineOn f g S :=
  fun _ hx => ⟨S, hS, hx, Subset.rfl, A, B, hA, he⟩

/-- Restricting a local affine relation to an open set preserves it. -/
theorem locallyPositiveAffineOn_mono {S T : Set ℝ} {f g : ℝ → ℝ}
    (h : LocallyPositiveAffineOn f g S) (hT : IsOpen T) (hTS : T ⊆ S) :
    LocallyPositiveAffineOn f g T := by
  intro x hx
  obtain ⟨U, hU, hxU, _, A, B, hA, he⟩ := h x (hTS hx)
  exact ⟨U ∩ T, hU.inter hT, ⟨hxU, hx⟩, inter_subset_right,
    A, B, hA, fun _ hy => he _ hy.1⟩

/-- Increasing functions on two intersecting intervals are increasing on their union. -/
theorem strictMonoOn_union_intervals {S T : Set ℝ} {f : ℝ → ℝ}
    (hS : S.OrdConnected) (hT : T.OrdConnected) (hne : (S ∩ T).Nonempty)
    (hfS : StrictMonoOn f S) (hfT : StrictMonoOn f T) : StrictMonoOn f (S ∪ T) := by
  obtain ⟨c, hcS, hcT⟩ := hne
  have hcross : ∀ x ∈ S, ∀ y ∈ T, x < y → f x < f y := by
    intro x hx y hy hxy
    by_cases hxc : x < c
    · by_cases hcy : c < y
      · exact (hfS hx hcS hxc).trans (hfT hcT hy hcy)
      · have hyS : y ∈ S := hS.out hx hcS ⟨hxy.le, le_of_not_gt hcy⟩
        exact hfS hx hyS hxy
    · have hxT : x ∈ T := hT.out hcT hy ⟨le_of_not_gt hxc, hxy.le⟩
      exact hfT hxT hy hxy
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hfS hx hy hxy
  · exact hcross x hx y hy hxy
  · by_cases hxc : x < c
    · by_cases hcy : c < y
      · exact (hfT hx hcT hxc).trans (hfS hcS hy hcy)
      · exact hfT hx (hT.out hx hcT ⟨hxy.le, le_of_not_gt hcy⟩) hxy
    · exact hfS (hS.out hcS hy ⟨le_of_not_gt hxc, hxy.le⟩) hy hxy
  · exact hfT hx hy hxy

end Kreps.PreferenceProperties
