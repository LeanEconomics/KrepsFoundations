/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.OrthantRepresentation

/-!
# Pareto and majority comparisons

Kreps I, Problems 1.6-1.7, pp. 25-26. All bundles in the examples belong to the
nonnegative orthant. Pareto preference is transitive but incomplete; majority
preference is complete but can cycle. Both strict parts fail negative transitivity.
-/

namespace Kreps.ChoicePreferenceUtility

/-- Coordinatewise weak dominance on the nonnegative orthant. -/
def ParetoPreference {k : ℕ} (x y : NonnegativeOrthant k) : Prop := y ≤ x

/-- **Problem 1.6a**, transitivity. -/
theorem problem_1_6_transitive (k : ℕ) :
    TransitivePref (ParetoPreference (k := k)) := fun _ _ _ hxy hyz => hyz.trans hxy

/-- **Problem 1.6a**, incompleteness for any two or more commodities. -/
theorem problem_1_6_not_complete (k : ℕ) (hk : 2 ≤ k) :
    ¬Complete (ParetoPreference (k := k)) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  let x : NonnegativeOrthant k := ⟨fun t => if t = i then 1 else 0,
    by intro t; dsimp only; split_ifs <;> norm_num⟩
  let y : NonnegativeOrthant k := ⟨fun t => if t = i then 0 else 1,
    by intro t; dsimp only; split_ifs <;> norm_num⟩
  intro hc
  rcases hc x y with h | h
  · have hh := h j
    norm_num [x, y, Ne.symm hij] at hh
  · have hh := h i
    norm_num [x, y] at hh

/-- **Problem 1.6b**, strict dominance means weak dominance and a strict coordinate. -/
theorem problem_1_6_strict {k : ℕ} (x y : NonnegativeOrthant k) :
    Strict ParetoPreference x y ↔
      (∀ i, y.val i ≤ x.val i) ∧ ∃ i, y.val i < x.val i := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hn
    push Not at hn
    exact h.2 hn
  · rintro ⟨h, i, hi⟩
    exact ⟨h, fun hrev => (not_le_of_gt hi) (hrev i)⟩

/-- **Problem 1.6b**, asymmetry of strict Pareto preference. -/
theorem problem_1_6_asymmetric (k : ℕ) :
    AsymmetricPref (Strict (ParetoPreference (k := k))) := proposition_1_9b _

/-- **Problem 1.6b**, negative transitivity fails for two or more commodities. -/
theorem problem_1_6_not_negativelyTransitive (k : ℕ) (hk : 2 ≤ k) :
    ¬NegativelyTransitive (Strict (ParetoPreference (k := k))) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  let x : NonnegativeOrthant k := ⟨fun t => if t = i then 2 else 1,
    by intro t; dsimp only; split_ifs <;> norm_num⟩
  let y : NonnegativeOrthant k := ⟨fun _ => 1, by intro t; norm_num⟩
  let z : NonnegativeOrthant k := ⟨fun t => if t = i then 0 else 2,
    by intro t; dsimp only; split_ifs <;> norm_num⟩
  have hxy : Strict ParetoPreference x y := by
    apply (problem_1_6_strict x y).mpr
    constructor
    · intro t
      dsimp [x, y]
      split_ifs <;> norm_num
    · exact ⟨i, by norm_num [x, y]⟩
  intro hn
  rcases hn x y z hxy with h | h
  · have hh := h.1 i
    norm_num [y, z] at hh
  · have hh := h.1 j
    norm_num [x, z, Ne.symm hij] at hh

/-- **Problem 1.6c**, indifference is equality of bundles. -/
theorem problem_1_6_indifference {k : ℕ} (x y : NonnegativeOrthant k) :
    Indifferent ParetoPreference x y ↔ x = y := by
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-- **Problem 1.6c**, all three equivalence-relation properties. -/
theorem problem_1_6_equivalence (k : ℕ) :
    (∀ x : NonnegativeOrthant k, Indifferent ParetoPreference x x) ∧
      (∀ x y : NonnegativeOrthant k, Indifferent ParetoPreference x y →
        Indifferent ParetoPreference y x) ∧
      TransitivePref (Indifferent (ParetoPreference (k := k))) :=
  ⟨fun _ => ⟨le_rfl, le_rfl⟩, fun _ _ h => proposition_1_9e h,
    fun _ _ _ hxy hyz => proposition_1_9f (problem_1_6_transitive k) hxy hyz⟩

/-- At least two of the three coordinates weakly favor the first bundle. -/
def MajorityPreference (x y : NonnegativeOrthant 3) : Prop :=
  (y.val 0 ≤ x.val 0 ∧ y.val 1 ≤ x.val 1) ∨
    (y.val 0 ≤ x.val 0 ∧ y.val 2 ≤ x.val 2) ∨
    (y.val 1 ≤ x.val 1 ∧ y.val 2 ≤ x.val 2)

/-- **Problem 1.7a**, completeness by the three coordinate comparisons. -/
theorem problem_1_7_complete : Complete MajorityPreference := by
  intro x y
  dsimp [MajorityPreference]
  rcases le_total (x.val 0) (y.val 0) with h0 | h0 <;>
    rcases le_total (x.val 1) (y.val 1) with h1 | h1 <;>
    rcases le_total (x.val 2) (y.val 2) with h2 | h2 <;> tauto

/-- **Problem 1.7b**, strict majority is strict improvement in at least two coordinates. -/
theorem problem_1_7_strict (x y : NonnegativeOrthant 3) :
    Strict MajorityPreference x y ↔
      (y.val 0 < x.val 0 ∧ y.val 1 < x.val 1) ∨
        (y.val 0 < x.val 0 ∧ y.val 2 < x.val 2) ∨
        (y.val 1 < x.val 1 ∧ y.val 2 < x.val 2) := by
  rw [proposition_1_9a problem_1_7_complete]
  simp only [MajorityPreference, not_or, not_and_or, not_le]
  tauto

/-- **Problem 1.7b**, asymmetry follows from the definition of the strict part. -/
theorem problem_1_7_asymmetric : AsymmetricPref (Strict MajorityPreference) :=
  proposition_1_9b _

/-- First bundle in the majority cycle: (3,2,1). -/
def MajorityX : NonnegativeOrthant 3 :=
  ⟨fun i => if i = 0 then 3 else if i = 1 then 2 else 1,
    by intro i; dsimp only; split_ifs <;> norm_num⟩

/-- Second bundle in the majority cycle: (2,1,3). -/
def MajorityY : NonnegativeOrthant 3 :=
  ⟨fun i => if i = 0 then 2 else if i = 1 then 1 else 3,
    by intro i; dsimp only; split_ifs <;> norm_num⟩

/-- Third bundle in the majority cycle: (1,3,2). -/
def MajorityZ : NonnegativeOrthant 3 :=
  ⟨fun i => if i = 0 then 1 else if i = 1 then 3 else 2,
    by intro i; dsimp only; split_ifs <;> norm_num⟩

/-- **Problem 1.7a**, the explicit majority cycle refutes transitivity. -/
theorem problem_1_7_not_transitive : ¬TransitivePref MajorityPreference := by
  intro ht
  have hxy : MajorityPreference MajorityX MajorityY := by
    norm_num [MajorityPreference, MajorityX, MajorityY]
  have hyz : MajorityPreference MajorityY MajorityZ := by
    norm_num [MajorityPreference, MajorityY, MajorityZ]
  have hxz := ht MajorityX MajorityY MajorityZ hxy hyz
  norm_num [MajorityPreference, MajorityX, MajorityZ] at hxz

/-- **Problem 1.7b**, the strict majority cycle also refutes negative transitivity. -/
theorem problem_1_7_not_negativelyTransitive :
    ¬NegativelyTransitive (Strict MajorityPreference) := by
  intro hn
  have hxy : Strict MajorityPreference MajorityX MajorityY := by
    norm_num [Strict, MajorityPreference, MajorityX, MajorityY]
  have hbad := hn MajorityX MajorityY MajorityZ hxy
  norm_num [Strict, MajorityPreference, MajorityX, MajorityY, MajorityZ] at hbad

end Kreps.ChoicePreferenceUtility
