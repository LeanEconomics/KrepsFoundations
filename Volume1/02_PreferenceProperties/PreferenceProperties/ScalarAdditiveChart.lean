/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.LocalScalarChart

/-!
# Additive charts with ambient real coordinate functions

Open subtype neighborhoods become real interval domains. Their cardinal
functions extend arbitrarily outside those domains, while retaining continuity,
strict increase and the represented preference wherever the chart applies.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] {S : I → Set ℝ}

/-- An additive coordinate chart on an open interval box of the scalar commodity domain. -/
structure ScalarAdditiveChart (V : (∀ i, S i) → ℝ) where
  domain : I → Set ℝ
  coord : I → ℝ → ℝ
  open_domain : ∀ i, IsOpen (domain i)
  interval : ∀ i, (domain i).OrdConnected
  subset : ∀ i, domain i ⊆ S i
  continuous : ∀ i, ContinuousOn (coord i) (domain i)
  increasing : ∀ i, StrictMonoOn (coord i) (domain i)
  represents : Represents (AdditiveUtility (fun i (x : domain i) => coord i x.val))
    (UtilityPref (fun x => V (fun i => Set.inclusion (subset i) (x i))))

/-- Every subtype additive chart gives a chart with ambient real domains
and coordinate functions. -/
theorem localScalarChart_to_scalarAdditiveChart {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i)) (z : ∀ i, S i)
    (h : HasLocalScalarAdditiveChart V z) :
    ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i := by
  classical
  obtain ⟨U, hU, ψ, hψ, hrep⟩ := h
  let D (i : I) : Set ℝ := Subtype.val '' U i
  let f (i : I) (x : U i) : ℝ := x.val.val
  have hfi (i : I) : Function.Injective (f i) :=
    Subtype.val_injective.comp Subtype.val_injective
  let w (i : I) : ℝ → ℝ := Function.extend (f i) (ψ i) (fun _ => 0)
  have hwe (i : I) (x : U i) : w i (f i x) = ψ i x :=
    (hfi i).extend_apply (ψ i) (fun _ => 0) x
  have hDo (i : I) : IsOpen (D i) := (ho i).isOpenMap_subtype_val _ (hU i).1
  have hDi (i : I) : (D i).OrdConnected := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ r hr
    let q : S i := ⟨r, (hS i).out x.property y.property hr⟩
    exact ⟨q, (hU i).2.2.out hx hy hr, rfl⟩
  have hDs (i : I) : D i ⊆ S i := by
    rintro r ⟨x, _, rfl⟩
    exact x.property
  have hwi (i : I) : StrictMonoOn (w i) (D i) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hxw := hwe i ⟨x, hx⟩
    have hyw := hwe i ⟨y, hy⟩
    change w i x.val = _ at hxw
    change w i y.val = _ at hyw
    rw [hxw, hyw]
    exact (hψ i).2 hxy
  have hwc (i : I) : ContinuousOn (w i) (D i) := by
    have hfind : Topology.IsInducing (f i) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    have hrange : f i '' Set.univ = D i := by
      ext r
      constructor
      · rintro ⟨x, _, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    rw [← hrange]
    apply hfind.continuousOn_image_iff.mpr
    have he : w i ∘ f i = ψ i := funext (hwe i)
    rw [he]
    exact (hψ i).1.continuousOn
  let lift (i : I) (x : D i) : U i := ⟨x.property.choose, x.property.choose_spec.1⟩
  have hlift (i : I) (x : D i) : f i (lift i x) = x.val := x.property.choose_spec.2
  have hwL (i : I) (x : D i) : w i x.val = ψ i (lift i x) := by
    rw [← hlift i x]
    exact hwe i (lift i x)
  have hV (x : ∀ i, D i) : (fun i => (lift i (x i)).val) =
      (fun i => Set.inclusion (hDs i) (x i)) := by
    funext i
    exact Subtype.ext (hlift i (x i))
  have hwrep : Represents (AdditiveUtility (fun i (x : D i) => w i x.val))
      (UtilityPref (fun x => V (fun i => Set.inclusion (hDs i) (x i)))) := by
    intro x y
    have hh := hrep (fun i => lift i (x i)) (fun i => lift i (y i))
    simp only [UtilityPref, AdditiveUtility] at hh ⊢
    rw [hV x, hV y] at hh
    simpa only [hwL] using hh
  exact ⟨⟨D, w, hDo, hDi, hDs, hwc, hwi, hwrep⟩,
    fun i => ⟨z i, (hU i).2.1, rfl⟩⟩

/-- Continuous strongly separable utility on open intervals has an additive chart at every point. -/
theorem exists_scalarAdditiveChart_at_of_open [DecidableEq I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i :=
  localScalarChart_to_scalarAdditiveChart hS ho z
    (exists_local_scalar_additive_chart_of_open hS ho hs hm hc z hthree)

end Kreps.PreferenceProperties
