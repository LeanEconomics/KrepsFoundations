/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.WeakSeparability
import PreferenceProperties.ContinuousUtility
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Strong separability and additive utility

Kreps I, Definition 2.13 and the additive-to-strong direction of Proposition 2.14,
p. 42. Strong separability applies to every union of blocks, and nontriviality
does not depend on the other goods. The converse existence theorem with three
nontrivial blocks is a separate pending obligation.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*}

/-- **Definition 2.13:** comparisons on every union of blocks ignore its complement. -/
def StronglySeparable [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∀ (S : Finset I) a b z t, r (S.piecewise a z) (S.piecewise b z) ↔
    r (S.piecewise a t) (S.piecewise b t)

/-- A block is nontrivial when some two of its bundles can be strictly ranked. -/
def NontrivialBlock [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) (i : I) : Prop :=
  ∃ a b z, Strict r (Function.update z i a) (Function.update z i b)

/-- The substantive three-block hypothesis in **Proposition 2.14**. -/
def ThreeNontrivialBlocks [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∃ i j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
    NontrivialBlock r i ∧ NontrivialBlock r j ∧ NontrivialBlock r l

/-- Strong separability includes each individual block's weak separability. -/
theorem stronglySeparable_weakly [DecidableEq I]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hs : StronglySeparable r) :
    WeaklySeparable (fun x y : BlockBundle B Unit => r x.1 y.1) := by
  intro i a b z t
  simpa [ReplaceBlock, Finset.piecewise_singleton] using
    hs {i} (Function.update z.1 i a) (Function.update z.1 i b) z.1 t.1

/-- The same pair witnesses block nontriviality under every surrounding bundle. -/
theorem nontrivialBlock_iff_every_context [DecidableEq I] [Nonempty (∀ i, B i)]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hs : StronglySeparable r) (i : I) :
    NontrivialBlock r i ↔
      ∃ a b, ∀ z, Strict r (Function.update z i a) (Function.update z i b) := by
  constructor
  · rintro ⟨a, b, z₀, hz⟩
    refine ⟨a, b, fun z => ?_⟩
    exact (weaklySeparable_strict (stronglySeparable_weakly hs) i a b (z₀, ()) (z, ())).mp hz
  · rintro ⟨a, b, hz⟩
    obtain ⟨z₀⟩ := ‹Nonempty (∀ i, B i)›
    exact ⟨a, b, z₀, hz z₀⟩

/-- Three distinct nontrivial blocks require at least three block indices. -/
theorem threeNontrivialBlocks_card [DecidableEq I] [Fintype I]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (h : ThreeNontrivialBlocks r) :
    3 ≤ Fintype.card I := by
  obtain ⟨i, j, l, hij, hil, hjl, _⟩ := h
  have hc : ({i, j, l} : Finset I).card = 3 := by simp [hij, hil, hjl]
  calc
    3 = ({i, j, l} : Finset I).card := hc.symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card I := Finset.card_univ

/-- Additive utility sums the individual block subutilities. -/
def AdditiveUtility [Fintype I] (w : ∀ i, B i → ℝ) (x : ∀ i, B i) : ℝ :=
  ∑ i, w i (x i)

/-- A preference admits an additive representation over the specified blocks. -/
def AdditivelyRepresentable [Fintype I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∃ w : ∀ i, B i → ℝ, Represents (AdditiveUtility w) r

/-- A union's utility contribution separates from the unchanged complementary blocks. -/
theorem additiveUtility_piecewise [Fintype I] [DecidableEq I]
    (w : ∀ i, B i → ℝ) (S : Finset I) (a z : ∀ i, B i) :
    AdditiveUtility w (S.piecewise a z) =
      (∑ i ∈ S, w i (a i)) + ∑ i ∈ Sᶜ, w i (z i) := by
  unfold AdditiveUtility
  rw [← Finset.sum_add_sum_compl S]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.piecewise_eq_of_mem _ _ _ hi]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp hi)]

/-- **Proposition 2.14**, converse: every additive representation is strongly separable. -/
theorem proposition_2_14_additive [Fintype I] [DecidableEq I]
    {w : ∀ i, B i → ℝ} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hu : Represents (AdditiveUtility w) r) : StronglySeparable r := by
  intro S a b z t
  rw [hu, hu]
  simp only [additiveUtility_piecewise, add_le_add_iff_right]

/-- Summing continuous subutilities gives a continuous utility on the product domain. -/
theorem additiveUtility_continuous [Fintype I] [∀ i, TopologicalSpace (B i)]
    {w : ∀ i, B i → ℝ} (hw : ∀ i, Continuous (w i)) : Continuous (AdditiveUtility w) :=
  continuous_finsetSum Finset.univ (fun i _ => (hw i).comp (continuous_apply i))

/-- Continuous additive subutilities therefore also give continuous preferences. -/
theorem continuousPreference_of_additive [Fintype I] [∀ i, TopologicalSpace (B i)]
    {w : ∀ i, B i → ℝ} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hu : Represents (AdditiveUtility w) r) (hw : ∀ i, Continuous (w i)) :
    ContinuousPreference r :=
  proposition_2_9_forward hu (additiveUtility_continuous hw)

end Kreps.PreferenceProperties
