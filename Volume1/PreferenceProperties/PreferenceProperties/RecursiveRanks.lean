/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RecursiveRankInsertion

/-!
# Recursive utility values on an enumerated domain

Kreps I, Problem 2.14(d), p. 49. Start at zero and apply the preceding insertion
rule successively. Old assignments never change. The resulting sequence preserves
every comparison of the original numerical ranks, including ties and repeated
points in the enumeration. Thus the construction gives a representation on the
enumerated subset rather than merely on its finite prefixes.
-/

namespace Kreps.PreferenceProperties

/-- The first `n + 1` assigned values after `n` successive insertions. -/
noncomputable def RecursiveRankStage (v : ℕ → ℝ) : (n : ℕ) → Fin (n + 1) → ℝ
  | 0 => fun _ => 0
  | n + 1 => Fin.lastCases
      (InsertedRank (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) (v (n + 1)))
      (RecursiveRankStage v n)

/-- A new stage retains each previously assigned value. -/
theorem recursiveRankStage_castSucc (v : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    RecursiveRankStage v (n + 1) i.castSucc = RecursiveRankStage v n i := by
  simp only [RecursiveRankStage, Fin.lastCases_castSucc]

/-- The newly appended value is computed by the book's insertion rule. -/
theorem recursiveRankStage_last (v : ℕ → ℝ) (n : ℕ) :
    RecursiveRankStage v (n + 1) (Fin.last (n + 1)) =
      InsertedRank (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) (v (n + 1)) := by
  simp only [RecursiveRankStage, Fin.lastCases_last]

/-- Every finite stage preserves all original rank comparisons. -/
theorem recursiveRankStage_preserving (v : ℕ → ℝ) (n : ℕ) :
    RankPreserving (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) := by
  induction n with
  | zero =>
      intro i j
      fin_cases i
      fin_cases j
      simp [RecursiveRankStage]
  | succ n ih =>
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · simpa only [Fin.val_last, Fin.val_castSucc, recursiveRankStage_last,
            recursiveRankStage_castSucc] using
            (insertedRank_compare ih (v (n + 1)) j).2
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.val_last, Fin.val_castSucc, recursiveRankStage_last,
            recursiveRankStage_castSucc] using
            (insertedRank_compare ih (v (n + 1)) i).1
        · simpa only [Fin.val_castSucc, recursiveRankStage_castSucc] using ih i j

/-- The value permanently assigned to the `n`th enumerated point. -/
noncomputable def RecursiveRank (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  RecursiveRankStage v n (Fin.last n)

/-- The arbitrary initial normalization is zero. -/
theorem recursiveRank_zero (v : ℕ → ℝ) : RecursiveRank v 0 = 0 := rfl

/-- Each finite stage consists of the already permanent assigned values. -/
theorem recursiveRankStage_eq_rank (v : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    RecursiveRankStage v n i = RecursiveRank v i := by
  induction n with
  | zero =>
      fin_cases i
      rfl
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rfl
      · rw [recursiveRankStage_castSucc]
        exact ih i

/-- The permanent sequence satisfies the four-case recursion on its previous values. -/
theorem recursiveRank_succ (v : ℕ → ℝ) (n : ℕ) :
    RecursiveRank v (n + 1) =
      InsertedRank (fun i : Fin (n + 1) => v i)
        (fun i => RecursiveRank v i) (v (n + 1)) := by
  change RecursiveRankStage v (n + 1) (Fin.last (n + 1)) = _
  rw [recursiveRankStage_last]
  congr 1
  funext i
  exact recursiveRankStage_eq_rank v n i

/-- All comparisons are preserved in the infinite enumerated sequence. -/
theorem recursiveRank_preserving (v : ℕ → ℝ) : RankPreserving v (RecursiveRank v) := by
  intro i j
  let n := max i j
  let i' : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le (le_max_left i j)⟩
  let j' : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le (le_max_right i j)⟩
  have h := recursiveRankStage_preserving v n i' j'
  simpa only [recursiveRankStage_eq_rank] using h

/-- Equal original ranks receive equal assigned values, even at different enumeration indices. -/
theorem recursiveRank_eq_iff (v : ℕ → ℝ) (i j : ℕ) :
    RecursiveRank v i = RecursiveRank v j ↔ v i = v j := by
  simp only [le_antisymm_iff, ← recursiveRank_preserving v i j,
    ← recursiveRank_preserving v j i]

/-- Strict original comparisons are preserved. -/
theorem recursiveRank_lt_iff (v : ℕ → ℝ) (i j : ℕ) :
    RecursiveRank v i < RecursiveRank v j ↔ v i < v j :=
  (rankPreserving_lt (recursiveRank_preserving v) i j).symm

/-- **Problem 2.14(d):** the recursively assigned sequence represents the sampled preference. -/
theorem problem_2_14d_sequence {X : Type*} {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) (q : ℕ → X) :
    Represents (RecursiveRank (v ∘ q)) (fun i j => r (q i) (q j)) := by
  intro i j
  exact (hv (q i) (q j)).trans (recursiveRank_preserving (v ∘ q) j i)

/-- A sampled preference needs only rationality for the recursive representation to exist. -/
theorem problem_2_14d_exists {X : Type*} {r : X → X → Prop}
    (hr : Rational r) (q : ℕ → X) :
    ∃ v : ℕ → ℝ, Represents (RecursiveRank v) (fun i j => r (q i) (q j)) := by
  have hs : Rational (fun i j => r (q i) (q j)) :=
    ⟨fun i j => hr.1 (q i) (q j), fun i j k => hr.2 (q i) (q j) (q k)⟩
  obtain ⟨v, hv⟩ := proposition_1_11 hs
  refine ⟨v, ?_⟩
  intro i j
  exact (hv i j).trans (recursiveRank_preserving v j i)

/-- Copy the permanent value of any enumeration index of a point in the sampled range. -/
noncomputable def RecursiveRangeUtility {X : Type*} (q : ℕ → X) (v : X → ℝ)
    (x : Set.range q) : ℝ := RecursiveRank (v ∘ q) x.property.choose

/-- Choosing an enumeration index does not affect the assigned value. -/
theorem recursiveRangeUtility_apply {X : Type*} (q : ℕ → X) (v : X → ℝ) (n : ℕ) :
    RecursiveRangeUtility q v ⟨q n, Set.mem_range_self n⟩ = RecursiveRank (v ∘ q) n := by
  apply (recursiveRank_eq_iff (v ∘ q) _ n).mpr
  change v (q _) = v (q n)
  exact congrArg v (Set.mem_range_self n).choose_spec

/-- **Problem 2.14(d):** a well-defined representation on the enumerated subset itself. -/
theorem problem_2_14d {X : Type*} {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) (q : ℕ → X) :
    Represents (RecursiveRangeUtility q v) (fun x y => r x.val y.val) := by
  intro x y
  have hx := x.property.choose_spec
  have hy := y.property.choose_spec
  have h := problem_2_14d_sequence hv q x.property.choose y.property.choose
  simpa only [hx, hy, RecursiveRangeUtility] using h

end Kreps.PreferenceProperties
