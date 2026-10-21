/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommodityBlocks
import PreferenceProperties.GeneralContinuousRepresentation

/-!
# The topology of a full commodity partition

A partition assigns every original commodity to exactly one block. Grouping the
nonnegative orthant by that assignment is a homeomorphism onto the product of
the nonnegative block orthants, with no leftover commodity factor.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k n : ℕ}

/-- The nonnegative quantities assigned to one member of a full commodity partition. -/
abbrev PartitionBlock (owner : Fin k → Fin n) (i : Fin n) :=
  {j : Fin k // owner j = i} → ℝ≥0

/-- Group each original commodity quantity into its unique assigned block. -/
def PartitionGroup (owner : Fin k → Fin n) (x : NonnegativeOrthant k) :
    ∀ i, PartitionBlock owner i :=
  fun _ j => ⟨x.val j.val, x.property j.val⟩

/-- Recover all original quantities from a full collection of partition blocks. -/
def PartitionUngroup (owner : Fin k → Fin n) (x : ∀ i, PartitionBlock owner i) :
    NonnegativeOrthant k :=
  ⟨fun j => (x (owner j) ⟨j, rfl⟩).val, fun j => (x (owner j) ⟨j, rfl⟩).property⟩

/-- Regrouping the original commodity quantities changes nothing. -/
theorem partitionUngroup_group (owner : Fin k → Fin n) (x : NonnegativeOrthant k) :
    PartitionUngroup owner (PartitionGroup owner x) = x := by
  apply Subtype.ext
  rfl

/-- Recovering and then regrouping quantities preserves every partition block. -/
theorem partitionGroup_ungroup (owner : Fin k → Fin n)
    (x : ∀ i, PartitionBlock owner i) :
    PartitionGroup owner (PartitionUngroup owner x) = x := by
  funext i j
  rcases j with ⟨j, hj⟩
  subst i
  rfl

/-- Each grouped quantity is a continuous coordinate of the original orthant. -/
theorem partitionGroup_continuous (owner : Fin k → Fin n) :
    Continuous (PartitionGroup owner) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply j.val).comp continuous_subtype_val).subtype_mk _

/-- Recovering the original quantities is continuous. -/
theorem partitionUngroup_continuous (owner : Fin k → Fin n) :
    Continuous (PartitionUngroup owner) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact continuous_subtype_val.comp
    ((continuous_apply (⟨j, rfl⟩ : {j' : Fin k // owner j' = owner j})).comp
      (continuous_apply (owner j)))

/-- A full partition is a homeomorphic regrouping of the original nonnegative orthant. -/
def partitionGroupingHomeomorph (owner : Fin k → Fin n) :
    NonnegativeOrthant k ≃ₜ (∀ i, PartitionBlock owner i) where
  toFun := PartitionGroup owner
  invFun := PartitionUngroup owner
  left_inv := partitionUngroup_group owner
  right_inv := partitionGroup_ungroup owner
  continuous_toFun := partitionGroup_continuous owner
  continuous_invFun := partitionUngroup_continuous owner

/-- Every partition block is connected, including empty blocks containing just one sub-bundle. -/
theorem partitionBlock_preconnected (owner : Fin k → Fin n) (i : Fin n) :
    PreconnectedSpace (PartitionBlock owner i) := by
  infer_instance

/-- A finite commodity partition has a separable product domain. -/
theorem partitionBlocks_separable (owner : Fin k → Fin n) :
    TopologicalSpace.SeparableSpace (∀ i, PartitionBlock owner i) := by
  infer_instance

/-- Every disjoint covering family of commodity subsets has a unique-owner assignment. -/
theorem exists_partition_assignment (J : Fin n → Set (Fin k))
    (hd : ∀ i j, i ≠ j → Disjoint (J i) (J j)) (hc : ∀ j, ∃ i, j ∈ J i) :
    ∃ owner : Fin k → Fin n, ∀ i j, owner j = i ↔ j ∈ J i := by
  classical
  let owner := fun j => (hc j).choose
  refine ⟨owner, fun i j => ?_⟩
  have hj : j ∈ J (owner j) := (hc j).choose_spec
  constructor
  · intro he
    exact he ▸ hj
  · intro hji
    by_contra hne
    exact Set.disjoint_left.mp (hd _ _ hne) hj hji

end Kreps.PreferenceProperties
