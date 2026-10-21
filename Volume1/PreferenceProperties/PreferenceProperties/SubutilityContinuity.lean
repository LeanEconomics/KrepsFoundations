/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.WeakSeparability
import PreferenceProperties.UtilityEquivalence
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Connected.Basic

/-!
# Continuous block scores

Preparation for Kreps I, Proposition 2.14. Continuous representations on a
connected space have interval ranges. Equivalent representations therefore
induce an order homeomorphism between their attained ranges. For a weakly
separable preference, this proves continuity of each coordinate of the exact
baseline aggregator, without requiring a continuous choice of representatives.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop} {u v : X → ℝ}

/-- Equivalent utilities identify their attained ranges by an order isomorphism. -/
noncomputable def UtilityRangeOrderIso (hu : Represents u r) (hv : Represents v r) :
    Set.range u ≃o Set.range v where
  toFun q := ⟨UtilityTransform u v q.val, by
    obtain ⟨x, hx⟩ := q.property
    rw [← hx, utilityTransform_apply hu hv]
    exact ⟨x, rfl⟩⟩
  invFun q := ⟨UtilityTransform v u q.val, by
    obtain ⟨x, hx⟩ := q.property
    rw [← hx, utilityTransform_apply hv hu]
    exact ⟨x, rfl⟩⟩
  left_inv := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change UtilityTransform v u (UtilityTransform u v (u x)) = u x
    rw [utilityTransform_apply hu hv, utilityTransform_apply hv hu]
  right_inv := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change UtilityTransform u v (UtilityTransform v u (v x)) = v x
    rw [utilityTransform_apply hv hu, utilityTransform_apply hu hv]
  map_rel_iff' := by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    change UtilityTransform u v (u x) ≤ UtilityTransform u v (u y) ↔ u x ≤ u y
    rw [utilityTransform_apply hu hv, utilityTransform_apply hu hv]
    exact (hv y x).symm.trans (hu y x)

/-- On connected continuous utility ranges, the ordinal change of scale is continuous. -/
theorem utilityTransform_continuous_range [TopologicalSpace X] [PreconnectedSpace X]
    (hu : Represents u r) (hv : Represents v r) (huc : Continuous u) (hvc : Continuous v) :
    Continuous (fun q : Set.range u => UtilityTransform u v q.val) := by
  let : Set.OrdConnected (Set.range u) := (isPreconnected_range huc).ordConnected
  let : Set.OrdConnected (Set.range v) := (isPreconnected_range hvc).ordConnected
  exact continuous_subtype_val.comp (UtilityRangeOrderIso hu hv).continuous

variable {I : Type*} [DecidableEq I] {B : I → Type*} {L : Type*}

/-- Replacing a single block depends continuously on the replacement. -/
theorem replaceBlock_continuous [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    (s : BlockBundle B L) (i : I) : Continuous (ReplaceBlock s i) :=
  (continuous_const.update i continuous_id).prodMk continuous_const

/-- Continuous overall utility gives continuous baseline subutilities. -/
theorem baselineSubutility_continuous [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} (hu : Continuous u) (s : BlockBundle B L) (i : I) :
    Continuous (BaselineSubutility u s i) := hu.comp (replaceBlock_continuous s i)

/-- Connected commodity blocks yield interval-valued continuous baseline scores. -/
theorem baselineSubutility_ordConnected [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} (hu : Continuous u) (s : BlockBundle B L) (i : I)
    [PreconnectedSpace (B i)] : Set.OrdConnected (Set.range (BaselineSubutility u s i)) :=
  (isPreconnected_range (baselineSubutility_continuous hu s i)).ordConnected

/-- Separability identifies utility in every surrounding bundle with the baseline preference. -/
theorem baselineSubutility_represents_context {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ s : BlockBundle B L) (i : I) :
    Represents (BaselineSubutility u s i)
      (fun a b => r (ReplaceBlock s₀ i a) (ReplaceBlock s₀ i b)) := by
  intro a b
  exact (hs i a b s₀ s).trans (hu _ _)

/-- Changing the surrounding goods changes a connected block's scale continuously. -/
theorem baselineSubutility_transform_continuous
    [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (hc : Continuous u)
    (s₀ s : BlockBundle B L) (i : I) [PreconnectedSpace (B i)] :
    Continuous (fun q : Set.range (BaselineSubutility u s₀ i) =>
      UtilityTransform (BaselineSubutility u s₀ i) (BaselineSubutility u s i) q.val) :=
  utilityTransform_continuous_range
    (baselineSubutility_represents_context hu hs s₀ s₀ i)
    (baselineSubutility_represents_context hu hs s₀ s i)
    (baselineSubutility_continuous hc s₀ i) (baselineSubutility_continuous hc s i)

/-- Choosing representatives commutes with changing a single score coordinate. -/
theorem scoreRepresentatives_update (w : ∀ i, B i → ℝ) (q : ∀ i, Set.range (w i))
    (i : I) (t : Set.range (w i)) :
    (fun j => ScoreRepresentative w j (Function.update q i t j)) =
      Function.update (fun j => ScoreRepresentative w j (q j)) i
        (ScoreRepresentative w i t) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

/-- Each coordinate of the exact weak-separability aggregator is continuous. -/
theorem subutilityAggregator_coordinate_continuous
    [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (hc : Continuous u)
    (s₀ : BlockBundle B L) (q : ∀ i, Set.range (BaselineSubutility u s₀ i))
    (l : L) (i : I) [PreconnectedSpace (B i)] :
    Continuous (fun t => SubutilityAggregator u (BaselineSubutility u s₀)
      (Function.update q i t, l)) := by
  let w := BaselineSubutility u s₀
  let s : BlockBundle B L := ((fun j => ScoreRepresentative w j (q j)), l)
  have hf := baselineSubutility_represents_context hu hs s₀ s₀ i
  have hg := baselineSubutility_represents_context hu hs s₀ s i
  convert baselineSubutility_transform_continuous hu hs hc s₀ s i using 1
  funext t
  change u ((fun j => ScoreRepresentative w j (Function.update q i t j)), l) = _
  rw [scoreRepresentatives_update]
  change BaselineSubutility u s i (ScoreRepresentative w i t) =
    UtilityTransform (w i) (BaselineSubutility u s i) t.val
  rw [← scoreRepresentative_spec w i t]
  exact (utilityTransform_apply hf hg (ScoreRepresentative w i t)).symm

end Kreps.PreferenceProperties
