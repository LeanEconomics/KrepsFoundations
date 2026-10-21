/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.OpenScalarAdditiveExistence
import PreferenceProperties.FullIntervalAdditiveExtension

/-!
# Additive existence on nondegenerate real interval products

The scalar form of Kreps I, Proposition 2.14, p. 42. Continuous strong
separability and strict increase give an actual continuous additive
representation on every finite product of nondegenerate real intervals with
at least three coordinates. The intervals may include either endpoint and
need not be bounded. No local or global additive representation is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Strong separability gives continuous additive scales on full nondegenerate intervals. -/
theorem exists_nondegenerate_scalar_additive {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} [∀ i, Nontrivial (S i)] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ g : ∀ i, S i → ℝ, (∀ i, Continuous (g i)) ∧ (∀ i, StrictMono (g i)) ∧
      Represents (AdditiveUtility g) (UtilityPref V) := by
  classical
  have hne (i : I) : (interior (S i)).Nonempty :=
    nontrivial_interval_interior_nonempty (hS i)
  let : Nontrivial I := by
    obtain ⟨i, j, _, hij, _, _⟩ := hthree
    exact ⟨⟨i, j, hij⟩⟩
  let z : ∀ i, interior (S i) := fun i => ⟨(hne i).choose, (hne i).choose_spec⟩
  obtain ⟨f, hf, hfm, hr⟩ := exists_open_scalar_additive_representation
    (fun i => (hS i).interior) (fun _ => isOpen_interior)
    (interiorScalarInclusion_stronglySeparable hs)
    (hm.comp interiorScalarInclusion_strictMono)
    (hc.comp interiorScalarInclusion_continuous) z hthree
  obtain ⟨g, hg, hgm, hgr, _⟩ :=
    exists_full_interval_additive_extension hS hne hc hm hf hfm hr
  exact ⟨g, hg, hgm, hgr⟩

end Kreps.PreferenceProperties
