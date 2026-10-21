/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AllPairsLocalScale
import PreferenceProperties.PairwiseAdditiveRepresentation

/-!
# Local additive charts in the original scalar coordinates

Renormalizing at a specified interior bundle gives a common cardinal scale.
Pulling it back through the baseline coordinate utilities produces open interval
neighborhoods in the original coordinates and a full finite additive chart.
-/

namespace Kreps.PreferenceProperties

/-- An order-connected subset of a real interval is preconnected in its subtype topology. -/
theorem ordConnected_subtype_preconnected {S : Set ℝ} (hS : S.OrdConnected)
    {U : Set S} (hU : U.OrdConnected) : IsPreconnected U := by
  have himage : (Subtype.val '' U).OrdConnected := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    let q : S := ⟨z, hS.out x.property y.property hz⟩
    exact ⟨q, hU.out hx hy hz, rfl⟩
  exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp himage.isPreconnected

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- A local additive chart has open interval coordinate domains containing the reference bundle. -/
def HasLocalScalarAdditiveChart [Fintype I] (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) : Prop :=
  ∃ U : ∀ i, Set (S i), (∀ i, IsOpen (U i) ∧ z i ∈ U i ∧ (U i).OrdConnected) ∧
    ∃ ψ : ∀ i, U i → ℝ, (∀ i, Continuous (ψ i) ∧ StrictMono (ψ i)) ∧
      Represents (AdditiveUtility ψ) (UtilityPref (fun x => V (fun i => (x i).val)))

/-- An interior reference bundle has a full local additive chart
in the original scalar coordinates. -/
theorem exists_local_scalar_additive_chart [Fintype I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i)
    (hint : ∀ i, V z ∈ interior (Set.range (BaselineScores V z i)))
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    HasLocalScalarAdditiveChart V z := by
  let : ∀ i, PreconnectedSpace (S i) :=
    fun i => isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  have hu : Represents V (UtilityPref V) := fun _ _ => Iff.rfl
  let w := BaselineScores V z
  let A := ScoreAggregator V z
  let q₀ := BlockScores w z
  have ht : ∃ i ∈ (Set.univ : Set I), ∃ j ∈ Set.univ, ∃ l ∈ Set.univ,
      i ≠ j ∧ i ≠ l ∧ j ≠ l := by
    obtain ⟨i, j, l, hij, hil, hjl⟩ := hthree
    exact ⟨i, Set.mem_univ i, j, Set.mem_univ j, l, Set.mem_univ l, hij, hil, hjl⟩
  have hlocal := exists_all_pairs_local_scale
    (scoreAggregator_stronglySeparable hu hs z) (scoreAggregator_strictMono hu hs z)
    (scoreAggregator_continuous hu hs hc z) q₀ (scoreAggregator_reference_axis hu hs z)
    (baselineScores_reference V z) (fun i _ => hint i) ht
  obtain ⟨a, b, hab, hsub, φ, hac, hcb, hφc, hφm, _, _, hpair⟩ := hlocal
  let U (i : I) : Set (S i) := (w i) ⁻¹' Set.Ioo a b
  have hwc (i : I) : Continuous (w i) := baselineScores_continuous hc z i
  have hwm (i : I) : StrictMono (w i) := by
    intro x y hxy
    exact hm (Function.update_strictMono hxy)
  have hUo (i : I) : IsOpen (U i) := isOpen_Ioo.preimage (hwc i)
  have hzU (i : I) : z i ∈ U i := by
    change BaselineScores V z i (z i) ∈ Set.Ioo a b
    rw [baselineScores_reference]
    exact ⟨hac, hcb⟩
  have hUc (i : I) : (U i).OrdConnected := Set.ordConnected_Ioo.preimage_mono (hwm i).monotone
  let : ∀ i, PreconnectedSpace (U i) := fun i =>
    isPreconnected_iff_preconnectedSpace.mp (ordConnected_subtype_preconnected (hS i) (hUc i))
  let s (i : I) (x : U i) : Set.Icc a b :=
    ⟨w i x.val, x.property.1.le, x.property.2.le⟩
  let ψ (i : I) (x : U i) : ℝ := φ (s i x)
  have hψc (i : I) : Continuous (ψ i) :=
    hφc.comp (((hwc i).comp continuous_subtype_val).subtype_mk _)
  have hψm (i : I) : StrictMono (ψ i) := by
    intro x y hxy
    exact hφm (hwm i hxy)
  let F (x : ∀ i, U i) : ℝ := V (fun i => (x i).val)
  have hFm : StrictMono F := by
    intro x y hxy
    apply hm
    exact ⟨fun i => hxy.le i, fun h => hxy.not_ge (fun i => h i)⟩
  have hp : ∀ (x : ∀ i, U i) (i j : I) (u : U i) (v : U j), i ≠ j →
      ψ i u + ψ j v = ψ i (x i) + ψ j (x j) →
        F (Function.update (Function.update x i u) j v) = F x := by
    intro x i j u v hij he
    let y : ∀ i, S i := fun i => (x i).val
    let Q := BlockScores w y
    let k := CommonActiveScoreEmbedding q₀ Set.univ hsub
    have hki (t : U i) : k i (s i t) =
        (⟨w i t.val, t.val, rfl⟩ : Set.range (w i)) := by
      exact commonActiveScoreEmbedding_active q₀ Set.univ hsub (Set.mem_univ i) (s i t)
    have hkj (t : U j) : k j (s j t) =
        (⟨w j t.val, t.val, rfl⟩ : Set.range (w j)) := by
      exact commonActiveScoreEmbedding_active q₀ Set.univ hsub (Set.mem_univ j) (s j t)
    have hle := (hpair Q i (Set.mem_univ i) j (Set.mem_univ j) hij
      (s i u) (s j v) (s i (x i)) (s j (x j))).2 he.le
    have hge := (hpair Q i (Set.mem_univ i) j (Set.mem_univ j) hij
      (s i (x i)) (s j (x j)) (s i u) (s j v)).2 he.ge
    have heq := le_antisymm hle hge
    change CoordinatePairUtility A Q k i j (s i u) (s j v) =
      CoordinatePairUtility A Q k i j (s i (x i)) (s j (x j)) at heq
    unfold CoordinatePairUtility at heq
    rw [hki, hkj, hki, hkj] at heq
    have hqi : (⟨w i (x i).val, (x i).val, rfl⟩ : Set.range (w i)) = Q i := rfl
    have hqj : (⟨w j (x j).val, (x j).val, rfl⟩ : Set.range (w j)) = Q j := rfl
    rw [hqi, Function.update_eq_self, hqj, Function.update_eq_self] at heq
    change V (fun l => (Function.update (Function.update x i u) j v l).val) = V y
    rw [coordinateMap_update, coordinateMap_update]
    rw [scoreAggregator_factors hu hs z, scoreAggregator_factors hu hs z]
    rw [blockScores_update, blockScores_update]
    exact heq
  exact ⟨U, fun i => ⟨hUo i, hzU i, hUc i⟩, ψ, fun i => ⟨hψc i, hψm i⟩,
    represents_additive_of_pair_scale_invariance hFm ψ hψc hψm hp⟩

/-- At a point of an open interval product, every strictly increasing baseline score is interior. -/
theorem baselineScores_interior_of_open_strictMono {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i) (i : I) :
    V z ∈ interior (Set.range (BaselineScores V z i)) := by
  let : PreconnectedSpace (S i) :=
    isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  obtain ⟨L, R, hzLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((ho i).mem_nhds (z i).property)
  obtain ⟨lo, hLlo, hloz⟩ := exists_between hzLR.1
  obtain ⟨up, hzup, hupR⟩ := exists_between hzLR.2
  let low : S i := ⟨lo, hLR ⟨hLlo, hloz.trans hzLR.2⟩⟩
  let high : S i := ⟨up, hLR ⟨hzLR.1.trans hzup, hupR⟩⟩
  have hlow : BaselineScores V z i low < BaselineScores V z i (z i) :=
    hm (Function.update_strictMono hloz)
  have hhigh : BaselineScores V z i (z i) < BaselineScores V z i high :=
    hm (Function.update_strictMono hzup)
  rw [baselineScores_reference] at hlow hhigh
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds hlow hhigh)
  intro x hx
  exact (baselineScores_ordConnected hc z i).out ⟨low, rfl⟩ ⟨high, rfl⟩
    ⟨hx.1.le, hx.2.le⟩

/-- Every point of an open interval product has an open local additive chart. -/
theorem exists_local_scalar_additive_chart_of_open [Fintype I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    HasLocalScalarAdditiveChart V z :=
  exists_local_scalar_additive_chart hS hs hm hc z
    (baselineScores_interior_of_open_strictMono hS ho hm hc z) hthree

end Kreps.PreferenceProperties
