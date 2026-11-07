/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.WeakSeparability
import PreferenceProperties.OrthantRepresentation
import Mathlib.Basic.NNReal.Basic

/-!
# Commodity-index blocks and leftover goods

Kreps I, the notation preceding Definition 2.11, p. 40. Each commodity is
assigned to a selected block or to the leftover bundle. Every family of disjoint
commodity subsets admits such an assignment. Grouping is a genuine equivalence
with the original orthant, and block replacement changes exactly its assigned goods.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k n : ℕ}

/-- The nonnegative quantities of goods assigned to a selected block. -/
abbrev AssignedBlock (owner : Fin k → Option (Fin n)) (i : Fin n) :=
  {j : Fin k // owner j = some i} → ℝ≥0

/-- The goods belonging to none of the selected blocks. -/
abbrev LeftoverBlock (owner : Fin k → Option (Fin n)) :=
  {j : Fin k // owner j = none} → ℝ≥0

/-- Read each selected block and the leftover quantities from a full bundle. -/
def GroupCommodities (owner : Fin k → Option (Fin n)) (x : Fin k → ℝ≥0) :
    BlockBundle (AssignedBlock owner) (LeftoverBlock owner) :=
  ((fun _ j => x j.val), fun j => x j.val)

/-- Recover a commodity quantity from its uniquely assigned block. -/
def UngroupCommodities (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (j : Fin k) : ℝ≥0 :=
  match h : owner j with
  | none => x.2 ⟨j, h⟩
  | some i => x.1 i ⟨j, h⟩

/-- Recover a quantity from a known selected block. -/
theorem ungroupCommodities_some (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (j : Fin k) (hj : owner j = some i) :
    UngroupCommodities owner x j = x.1 i ⟨j, hj⟩ := by
  unfold UngroupCommodities
  split
  · rename_i hn
    have hf := hn.symm.trans hj
    cases hf
  · rename_i l hl
    have he : l = i := Option.some.inj (hl.symm.trans hj)
    subst l
    rfl

/-- Recover a quantity known to lie in the leftover bundle. -/
theorem ungroupCommodities_none (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner))
    (j : Fin k) (hj : owner j = none) :
    UngroupCommodities owner x j = x.2 ⟨j, hj⟩ := by
  unfold UngroupCommodities
  split
  · rfl
  · rename_i i hi
    have hf := hi.symm.trans hj
    cases hf

/-- Grouping and recovering leave every commodity quantity unchanged. -/
theorem ungroup_groupCommodities (owner : Fin k → Option (Fin n)) (x : Fin k → ℝ≥0) :
    UngroupCommodities owner (GroupCommodities owner x) = x := by
  funext j
  unfold UngroupCommodities
  split <;> rfl

/-- Recovering and regrouping preserve all selected blocks and all leftover goods. -/
theorem group_ungroupCommodities (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) :
    GroupCommodities owner (UngroupCommodities owner x) = x := by
  apply Prod.ext
  · funext i j
    exact ungroupCommodities_some owner x i j.val j.property
  · funext j
    exact ungroupCommodities_none owner x j.val j.property

/-- The commodity grouping is a bijective change of coordinates. -/
def commodityGroupingEquiv (owner : Fin k → Option (Fin n)) :
    (Fin k → ℝ≥0) ≃ BlockBundle (AssignedBlock owner) (LeftoverBlock owner) where
  toFun := GroupCommodities owner
  invFun := UngroupCommodities owner
  left_inv := ungroup_groupCommodities owner
  right_inv := group_ungroupCommodities owner

/-- Coordinatewise nonnegative reals are exactly the chapter's nonnegative orthant. -/
def orthantNNRealEquiv (k : ℕ) : NonnegativeOrthant k ≃ (Fin k → ℝ≥0) where
  toFun x j := .mk (x.val j) (x.property j)
  invFun x := ⟨fun j => (x j : ℝ), fun j => (x j).property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    funext j
    exact NNReal.coe_injective rfl

/-- Group the original orthant into selected commodity blocks and their complement. -/
def orthantGrouping (owner : Fin k → Option (Fin n)) :
    NonnegativeOrthant k ≃ BlockBundle (AssignedBlock owner) (LeftoverBlock owner) :=
  (orthantNNRealEquiv k).trans (commodityGroupingEquiv owner)

/-- A grouped block coordinate is precisely the original commodity coordinate. -/
theorem orthantGrouping_block (owner : Fin k → Option (Fin n)) (x : NonnegativeOrthant k)
    (i : Fin n) (j : {j : Fin k // owner j = some i}) :
    (((orthantGrouping owner x).1 i j) : ℝ) = x.val j.val := rfl

/-- The same coordinate identity holds for leftover goods. -/
theorem orthantGrouping_leftover (owner : Fin k → Option (Fin n)) (x : NonnegativeOrthant k)
    (j : {j : Fin k // owner j = none}) :
    (((orthantGrouping owner x).2 j) : ℝ) = x.val j.val := rfl

/-- Replacing a block changes its assigned commodity to the specified new quantity. -/
theorem ungroup_replace_in_block (owner : Fin k → Option (Fin n))
    (s : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (a : AssignedBlock owner i) (j : Fin k) (hj : owner j = some i) :
    UngroupCommodities owner (ReplaceBlock s i a) j = a ⟨j, hj⟩ := by
  rw [ungroupCommodities_some owner (ReplaceBlock s i a) i j hj]
  simp [ReplaceBlock]

/-- Replacing a block leaves every unassigned commodity unchanged. -/
theorem ungroup_replace_outside (owner : Fin k → Option (Fin n))
    (s : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (a : AssignedBlock owner i) (j : Fin k) (hj : owner j ≠ some i) :
    UngroupCommodities owner (ReplaceBlock s i a) j = UngroupCommodities owner s j := by
  cases h : owner j with
  | none =>
    rw [ungroupCommodities_none owner (ReplaceBlock s i a) j h,
      ungroupCommodities_none owner s j h]
    rfl
  | some l =>
    have hli : l ≠ i := by
      intro he
      subst l
      exact hj h
    rw [ungroupCommodities_some owner (ReplaceBlock s i a) l j h,
      ungroupCommodities_some owner s l j h]
    simp [ReplaceBlock, Function.update_of_ne hli]

/-- Two distinct selected blocks cannot contain the same commodity. -/
theorem assigned_blocks_disjoint (owner : Fin k → Option (Fin n))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint {a | owner a = some i} {a | owner a = some j} := by
  apply Set.disjoint_left.mpr
  intro a hai haj
  exact hij (Option.some.inj (hai.symm.trans haj))

/-- Leftovers are exactly the complement of the union of selected blocks. -/
theorem assigned_leftover_iff (owner : Fin k → Option (Fin n)) (j : Fin k) :
    owner j = none ↔ ∀ i, owner j ≠ some i := by
  cases h : owner j <;> simp

/-- Every disjoint family of subsets has an assignment, including an explicit leftover class. -/
theorem exists_commodity_assignment (J : Fin n → Set (Fin k))
    (hd : ∀ i j, i ≠ j → Disjoint (J i) (J j)) :
    ∃ owner : Fin k → Option (Fin n),
      (∀ i j, owner j = some i ↔ j ∈ J i) ∧
      ∀ j, owner j = none ↔ ∀ i, j ∉ J i := by
  classical
  let owner := fun j => if h : ∃ i, j ∈ J i then some (Classical.choose h) else none
  have hblocks (i : Fin n) (j : Fin k) : owner j = some i ↔ j ∈ J i := by
    by_cases h : ∃ i, j ∈ J i
    · have hs := Classical.choose_spec h
      have he : owner j = some (Classical.choose h) := by simp [owner, h]
      rw [he, Option.some.injEq]
      constructor
      · intro hi
        exact hi ▸ hs
      · intro hji
        by_contra hne
        exact Set.disjoint_left.mp (hd _ _ hne) hs hji
    · have hji : j ∉ J i := fun hji => h ⟨i, hji⟩
      simp [owner, h, hji]
  refine ⟨owner, hblocks, ?_⟩
  intro j
  rw [assigned_leftover_iff]
  constructor
  · intro h i hi
    exact h i ((hblocks i j).mpr hi)
  · intro h i hi
    exact h i ((hblocks i j).mp hi)

/-- **Proposition 2.12** transported to the original commodity orthant. -/
theorem proposition_2_12_orthant (owner : Fin k → Option (Fin n))
    {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hu : Represents u r) :
    WeaklySeparable (fun x y => r ((orthantGrouping owner).symm x)
      ((orthantGrouping owner).symm y)) ↔
    WeakSeparabilityRepresentation (fun x => u ((orthantGrouping owner).symm x)) :=
  proposition_2_12 (fun x y => hu ((orthantGrouping owner).symm x)
    ((orthantGrouping owner).symm y))

end Kreps.PreferenceProperties
