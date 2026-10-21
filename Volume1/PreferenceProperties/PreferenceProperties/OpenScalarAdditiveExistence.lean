/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SharedCompanionPairScale
import PreferenceProperties.SharedCompanionSelection
import PreferenceProperties.ReferencePairAdditiveRepresentation

/-!
# Additive existence on open scalar intervals

Pointwise additive charts supply coordinate scales. Two companions for each
coordinate synchronize their units, with a common companion for every pair.
The resulting pair comparisons determine the complete additive representation.
No additive representation or cardinal scale is assumed in the hypotheses.
-/

namespace Kreps.PreferenceProperties

/-- Strong separability on at least three open scalar intervals gives
continuous additive utility. -/
theorem exists_open_scalar_additive_representation
    {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    {V : (∀ i, S i) → ℝ} (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  classical
  let : ∀ i, PreconnectedSpace (S i) :=
    fun i => isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  have hl (t : ∀ i, S i) :
      ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i :=
    exists_scalarAdditiveChart_at_of_open hS ho hs hm hc t hthree
  obtain ⟨seed, hz⟩ := hl z
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hthree
  obtain ⟨first, second, hdistinct, hshared⟩ := exists_shared_companions hab hac hbc
  let G (i : I) : GlobalCoordinateScale V z seed i (first i) (second i) :=
    Classical.choice (exists_globalCoordinateScale hl hS hs z seed hz
      (hdistinct i).1.symm (hdistinct i).2.1.symm (hdistinct i).2.2)
  let w (i : I) (x : S i) : ℝ := (G i).scale x.val
  have hwc (i : I) : Continuous (w i) :=
    continuousOn_iff_continuous_domRestrict.mp (G i).continuous
  have hwm (i : I) : StrictMono (w i) :=
    fun x y hxy => (G i).increasing x.property y.property hxy
  refine ⟨w, hwc, hwm, represents_additive_of_reference_pair_comparisons hs hm z w hwc hwm ?_⟩
  intro i j hij a a' b b'
  obtain ⟨q, hqi, hqj, hqG, hqH⟩ := hshared i j hij
  exact globalCoordinateScale_pair_comparison (G i) (G j) hl hS hs hz hij
    hqi.symm hqj.symm hqG hqH (a, b) (a', b')

end Kreps.PreferenceProperties
