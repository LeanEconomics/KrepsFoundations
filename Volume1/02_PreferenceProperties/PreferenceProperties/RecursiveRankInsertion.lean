/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CountableUtility
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# One step of the recursive utility assignment

Kreps I, Problem 2.14(d), p. 49. A previously available numerical representation
supplies only comparisons. The new assigned value copies an indifferent point,
exceeds the previous maximum by one, falls below the previous minimum by one,
or is the midpoint between the adjacent assigned values. This file verifies that
one insertion preserves all comparisons with the previously assigned points.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*}

/-- The old numerical values preserve the order of the original ranks. -/
def RankPreserving (v u : I → ℝ) : Prop := ∀ i j, v i ≤ v j ↔ u i ≤ u j

/-- An order-preserving reassignment preserves strict comparisons too. -/
theorem rankPreserving_lt {v u : I → ℝ} (h : RankPreserving v u) (i j : I) :
    v i < v j ↔ u i < u j := by
  simp only [lt_iff_le_not_ge, ← h i j, ← h j i]

/-- The finite set of already assigned values strictly below a new rank. -/
def PreviousLowerRanks (v u : I → ℝ) (a : ℝ) : Set ℝ := u '' {i | v i < a}

/-- The finite set of already assigned values strictly above a new rank. -/
def PreviousUpperRanks (v u : I → ℝ) (a : ℝ) : Set ℝ := u '' {i | a < v i}

/-- The book's four-case rule for inserting one new rank. -/
noncomputable def InsertedRank (v u : I → ℝ) (a : ℝ) : ℝ := by
  classical
  exact if ht : ∃ i, v i = a then u ht.choose
    else if ∀ i, v i < a then sSup (Set.range u) + 1
    else if ∀ i, a < v i then sInf (Set.range u) - 1
    else (sSup (PreviousLowerRanks v u a) + sInf (PreviousUpperRanks v u a)) / 2

/-- Ties may be copied from any prior representative of that rank. -/
theorem insertedRank_tie {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} (i : I) (hi : v i = a) : InsertedRank v u a = u i := by
  classical
  have ht : ∃ j, v j = a := ⟨i, hi⟩
  rw [InsertedRank, dite_eq_left ht]
  apply le_antisymm
  · exact (h _ i).mp (le_of_eq (ht.choose_spec.trans hi.symm))
  · exact (h i _).mp (le_of_eq (hi.trans ht.choose_spec.symm))

/-- A strictly new highest rank receives the preceding maximum plus one. -/
theorem insertedRank_above {v u : I → ℝ} {a : ℝ} (ha : ∀ i, v i < a) :
    InsertedRank v u a = sSup (Set.range u) + 1 := by
  classical
  have ht : ¬ ∃ i, v i = a := by rintro ⟨i, hi⟩; exact (ha i).ne hi
  simp only [InsertedRank, dite_eq_right ht, ite_eq_left ha]

/-- A strictly new lowest rank receives the preceding minimum minus one. -/
theorem insertedRank_below [Nonempty I] {v u : I → ℝ} {a : ℝ}
    (ha : ∀ i, a < v i) : InsertedRank v u a = sInf (Set.range u) - 1 := by
  classical
  have ht : ¬ ∃ i, v i = a := by rintro ⟨i, hi⟩; exact (ha i).ne hi.symm
  have hn : ¬ ∀ i, v i < a := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (ha i).not_gt (h i)
  simp only [InsertedRank, dite_eq_right ht, ite_eq_right hn, ite_eq_left ha]

/-- With ranks on both sides and no tie, the insertion is the midpoint of its neighbors. -/
theorem insertedRank_between {v u : I → ℝ} {a : ℝ}
    (ht : ¬ ∃ i, v i = a) (hl : ∃ i, v i < a) (hh : ∃ i, a < v i) :
    InsertedRank v u a =
      (sSup (PreviousLowerRanks v u a) + sInf (PreviousUpperRanks v u a)) / 2 := by
  classical
  have hnlo : ¬ ∀ i, a < v i := by obtain ⟨i, hi⟩ := hl; exact fun h => hi.not_gt (h i)
  have hnhi : ¬ ∀ i, v i < a := by obtain ⟨i, hi⟩ := hh; exact fun h => hi.not_gt (h i)
  simp only [InsertedRank, dite_eq_right ht, ite_eq_right hnhi, ite_eq_right hnlo]

/-- The maximum lower assigned rank is strictly below the minimum upper assigned rank. -/
theorem previousRanks_gap [Finite I] {v u : I → ℝ} (h : RankPreserving v u) {a : ℝ}
    (hl : ∃ i, v i < a) (hh : ∃ i, a < v i) :
    sSup (PreviousLowerRanks v u a) < sInf (PreviousUpperRanks v u a) := by
  have hln : (PreviousLowerRanks v u a).Nonempty := by
    obtain ⟨i, hi⟩ := hl
    exact ⟨u i, i, hi, rfl⟩
  have hhn : (PreviousUpperRanks v u a).Nonempty := by
    obtain ⟨i, hi⟩ := hh
    exact ⟨u i, i, hi, rfl⟩
  have hlf : (PreviousLowerRanks v u a).Finite := (Set.toFinite _).image u
  have hhf : (PreviousUpperRanks v u a).Finite := (Set.toFinite _).image u
  obtain ⟨i, hi, he⟩ := hln.csSup_mem hlf
  obtain ⟨j, hj, hf⟩ := hhn.csInf_mem hhf
  rw [← he, ← hf]
  exact (rankPreserving_lt h i j).mp (hi.trans hj)

/-- Every lower old rank remains strictly below the newly assigned value. -/
theorem insertedRank_gt [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} {i : I} (hi : v i < a) : u i < InsertedRank v u a := by
  classical
  by_cases ht : ∃ j, v j = a
  · obtain ⟨j, hj⟩ := ht
    rw [insertedRank_tie h j hj]
    exact (rankPreserving_lt h i j).mp (hi.trans_eq hj.symm)
  by_cases hhi : ∀ j, v j < a
  · rw [insertedRank_above hhi]
    have hb := le_csSup (Set.finite_range u).bddAbove (Set.mem_range_self i)
    linarith
  have hh : ∃ j, a < v j := by
    push Not at hhi
    obtain ⟨j, hj⟩ := hhi
    exact ⟨j, lt_of_le_of_ne hj (fun he => ht ⟨j, he.symm⟩)⟩
  rw [insertedRank_between ht ⟨i, hi⟩ hh]
  have hgap := previousRanks_gap h ⟨i, hi⟩ hh
  have hb : u i ≤ sSup (PreviousLowerRanks v u a) :=
    le_csSup ((Set.toFinite _).image u).bddAbove ⟨i, hi, rfl⟩
  linarith

/-- Every higher old rank remains strictly above the newly assigned value. -/
theorem insertedRank_lt [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} {i : I} (hi : a < v i) : InsertedRank v u a < u i := by
  classical
  by_cases ht : ∃ j, v j = a
  · obtain ⟨j, hj⟩ := ht
    rw [insertedRank_tie h j hj]
    exact (rankPreserving_lt h j i).mp (hj.trans_lt hi)
  by_cases hlo : ∀ j, a < v j
  · rw [insertedRank_below hlo]
    have hb := csInf_le (Set.finite_range u).bddBelow (Set.mem_range_self i)
    linarith
  have hl : ∃ j, v j < a := by
    push Not at hlo
    obtain ⟨j, hj⟩ := hlo
    exact ⟨j, lt_of_le_of_ne hj (fun he => ht ⟨j, he⟩)⟩
  rw [insertedRank_between ht hl ⟨i, hi⟩]
  have hgap := previousRanks_gap h hl ⟨i, hi⟩
  have hb : sInf (PreviousUpperRanks v u a) ≤ u i :=
    csInf_le ((Set.toFinite _).image u).bddBelow ⟨i, hi, rfl⟩
  linarith

/-- The insertion preserves both weak comparisons with every previously assigned point. -/
theorem insertedRank_compare [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    (a : ℝ) (i : I) :
    (v i ≤ a ↔ u i ≤ InsertedRank v u a) ∧
      (a ≤ v i ↔ InsertedRank v u a ≤ u i) := by
  rcases lt_trichotomy (v i) a with hi | hi | hi
  · have hu := insertedRank_gt h hi
    exact ⟨iff_of_true hi.le hu.le, iff_of_false (not_le_of_gt hi) (not_le_of_gt hu)⟩
  · rw [insertedRank_tie h i hi, hi]
    simp
  · have hu := insertedRank_lt h hi
    exact ⟨iff_of_false (not_le_of_gt hi) (not_le_of_gt hu), iff_of_true hi.le hu.le⟩

end Kreps.PreferenceProperties
