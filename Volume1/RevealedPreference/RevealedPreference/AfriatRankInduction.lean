/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.RevealedRanks

/-!
# Varian's rank-class induction for the Afriat inequalities

Kreps I, Lemma 4.5, pp. 72-73, and Problem 4.2, p. 78. Remove the lowest
rank class, retain the inductively constructed coefficients on its complement,
and assign the removed class the minimum of the finitely many cross-class affine
values. Strictly positive cross-class costs permit positive new multipliers.
The all-minimal case is treated separately, including empty datasets.
-/

namespace Kreps.RevealedPreference

variable {I : Type*}

/-- A finite collection of inequalities with positive slopes has a positive common bound. -/
theorem exists_positive_finite_multiplier (s : Finset I) (a b : I → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ l : ℝ, 0 < l ∧ ∀ i ∈ s, b i ≤ l * a i := by
  classical
  by_cases hn : s.Nonempty
  · obtain ⟨m, _, hm⟩ := s.exists_max_image (fun i => b i / a i) hn
    refine ⟨max 1 (b m / a m), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi
    exact (div_le_iff₀ (ha i hi)).mp ((hm i hi).trans (le_max_right _ _))
  · exact ⟨1, zero_lt_one, fun i hi => (hn ⟨i, hi⟩).elim⟩

/-- **Problem 4.2, all-minimal case:** nonnegative costs admit zero values and unit weights. -/
theorem afriat_all_minimal (C : I → I → ℝ) (s : Finset I)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C j i) :
    ∃ v l : I → ℝ, (∀ i ∈ s, 0 < l i) ∧
      ∀ i ∈ s, ∀ j ∈ s, v i ≤ v j + l j * C j i := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ _ => zero_lt_one, ?_⟩
  simpa using hC

/-- The finite rank-class construction solves the inequalities on every finite subdataset. -/
theorem afriat_of_rank_on_finset (C : I → I → ℝ) (rank : I → ℕ)
    (hstrict : ∀ i j, rank i < rank j → 0 < C i j)
    (hequal : ∀ i j, rank i = rank j → 0 ≤ C i j) (s : Finset I) :
    ∃ v l : I → ℝ, (∀ i ∈ s, 0 < l i) ∧
      ∀ i ∈ s, ∀ j ∈ s, v i ≤ v j + l j * C j i := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hn : s.Nonempty
  · obtain ⟨m, hm, hmin⟩ := s.exists_min_image rank hn
    let H := s.filter (fun i => rank m < rank i)
    have hHs : H ⊆ s := Finset.filter_subset _ _
    have hmH : m ∉ H := by simp [H]
    have hsmall : H ⊂ s := by
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨hHs, fun he => hmH (he.symm ▸ hm)⟩
    have hbase (i : I) (hi : i ∈ s) (hiH : i ∉ H) : rank i = rank m := by
      have hnot : ¬rank m < rank i := fun hh => hiH (Finset.mem_filter.mpr ⟨hi, hh⟩)
      exact le_antisymm (le_of_not_gt hnot) (hmin i hi)
    by_cases hH : H.Nonempty
    · obtain ⟨v, l, hl, hv⟩ := ih H hsmall
      let Z := s \ H
      have hZ : Z.Nonempty := ⟨m, Finset.mem_sdiff.mpr ⟨hm, hmH⟩⟩
      obtain ⟨p, _, hp⟩ := (Z.product H).exists_min_image
        (fun q : I × I => v q.2 + l q.2 * C q.2 q.1) (hZ.product hH)
      let v0 := v p.2 + l p.2 * C p.2 p.1
      have hfloor (i : I) (hi : i ∈ Z) (j : I) (hj : j ∈ H) :
          v0 ≤ v j + l j * C j i := hp (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
      have hnew : ∀ j, ∃ t : ℝ, 0 < t ∧
          (j ∈ Z → ∀ i ∈ H, v i - v0 ≤ t * C j i) := by
        intro j
        by_cases hj : j ∈ Z
        · obtain ⟨t, ht, hti⟩ := exists_positive_finite_multiplier H (C j)
            (fun i => v i - v0) (by
              intro i hi
              apply hstrict
              rw [hbase j (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2]
              exact (Finset.mem_filter.mp hi).2)
          exact ⟨t, ht, fun _ => hti⟩
        · exact ⟨1, zero_lt_one, fun h => (hj h).elim⟩
      choose t ht hti using hnew
      refine ⟨fun i => if i ∈ H then v i else v0,
        fun i => if i ∈ H then l i else t i, ?_, ?_⟩
      · intro i hi
        change 0 < if i ∈ H then l i else t i
        split_ifs with hiH
        · exact hl i hiH
        · exact ht i
      · intro i hi j hj
        by_cases hiH : i ∈ H <;> by_cases hjH : j ∈ H
        · simpa only [ite_eq_left hiH, ite_eq_left hjH] using hv i hiH j hjH
        · simp only [ite_eq_left hiH, ite_eq_right hjH]
          have hh := hti j (Finset.mem_sdiff.mpr ⟨hj, hjH⟩) i hiH
          linarith
        · simpa only [ite_eq_right hiH, ite_eq_left hjH] using
            hfloor i (Finset.mem_sdiff.mpr ⟨hi, hiH⟩) j hjH
        · simp only [ite_eq_right hiH, ite_eq_right hjH, le_add_iff_nonneg_right]
          exact mul_nonneg (ht j).le
            (hequal j i ((hbase j hj hjH).trans (hbase i hi hiH).symm))
    · apply afriat_all_minimal C s
      intro i hi j hj
      exact hequal j i ((hbase j hj (fun h => hH ⟨j, h⟩)).trans
        (hbase i hi (fun h => hH ⟨i, h⟩)).symm)
  · exact afriat_all_minimal C s (fun i hi => (hn ⟨i, hi⟩).elim)

/-- **Lemma 4.5:** GARP yields positive Afriat multipliers on arbitrary finite data. -/
theorem lemma_4_5 [Finite I] {C : I → I → ℝ} (hG : MatrixGARP C) :
    ∃ v l : I → ℝ, (∀ i, 0 < l i) ∧ ∀ i j, v i ≤ v j + l j * C j i := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨v, l, hl, hv⟩ := afriat_of_rank_on_finset C (RevealedRank C)
    (fun _ _ => lemma_4_4a) (fun _ _ => lemma_4_4b hG) Finset.univ
  exact ⟨v, l, fun i => hl i (Finset.mem_univ i),
    fun i j => hv i (Finset.mem_univ i) j (Finset.mem_univ j)⟩

end Kreps.RevealedPreference
