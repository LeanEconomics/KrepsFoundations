/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.RevealedChains

/-!
# The finite rank used in Varian's proof

Kreps I, Lemma 4.4, p. 72. The rank counts observations strictly below an
observation by a revealed chain. Weak revealed comparisons include all successors
of the lower observation; strict comparisons include at least one more. A
minimum-rank observation therefore has no strict successors.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} [Fintype I]

/-- The indices of observations strictly revealed below a given observation. -/
noncomputable def StrictSuccessors (C : I → I → ℝ) (i : I) : Finset I := by
  classical
  exact Finset.univ.filter (RevealedStrict C i)

/-- The cardinal rank `n(i)` from Lemma 4.4. -/
noncomputable def RevealedRank (C : I → I → ℝ) (i : I) : ℕ :=
  (StrictSuccessors C i).card

/-- Membership in the finite successor set is exactly strict revealed preference. -/
theorem mem_strictSuccessors {C : I → I → ℝ} {i j : I} :
    j ∈ StrictSuccessors C i ↔ RevealedStrict C i j := by
  classical
  simp [StrictSuccessors]

/-- A weak chain preserves the inclusion of strict successor sets. -/
theorem strictSuccessors_subset {C : I → I → ℝ} {i j : I}
    (hij : RevealedWeak C i j) : StrictSuccessors C j ⊆ StrictSuccessors C i := by
  intro l hl
  exact mem_strictSuccessors.mpr (revealedWeak_strict_trans hij (mem_strictSuccessors.mp hl))

/-- A weak revealed comparison can only decrease the finite rank. -/
theorem revealedRank_le {C : I → I → ℝ} {i j : I} (hij : RevealedWeak C i j) :
    RevealedRank C j ≤ RevealedRank C i :=
  Finset.card_le_card (strictSuccessors_subset hij)

/-- A strict revealed comparison strictly decreases rank when GARP holds. -/
theorem revealedRank_lt {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedStrict C i j) : RevealedRank C j < RevealedRank C i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨strictSuccessors_subset (revealedStrict_weak hij), ?_⟩
  intro he
  have hj : j ∈ StrictSuccessors C i := mem_strictSuccessors.mpr hij
  rw [← he] at hj
  exact hG j (mem_strictSuccessors.mp hj)

/-- **Lemma 4.4a:** a higher-rank observation is strictly unaffordable at a lower rank. -/
theorem lemma_4_4a {C : I → I → ℝ} {i j : I}
    (hij : RevealedRank C i < RevealedRank C j) : 0 < C i j := by
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt hij) (revealedRank_le (directWeak_revealedWeak h))

/-- **Lemma 4.4b:** equal-rank observations cannot be strictly affordable under GARP. -/
theorem lemma_4_4b {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedRank C i = RevealedRank C j) : 0 ≤ C i j := by
  apply le_of_not_gt
  intro h
  have hr := revealedRank_lt hG (directStrict_revealedStrict h)
  rw [hij] at hr
  exact lt_irrefl _ hr

/-- **Lemma 4.4c:** a nonempty finite dataset satisfying GARP has a rank-zero observation. -/
theorem lemma_4_4c [Nonempty I] {C : I → I → ℝ} (hG : MatrixGARP C) :
    ∃ i, RevealedRank C i = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image (RevealedRank C) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  by_contra hn
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  have hji := revealedRank_lt hG (mem_strictSuccessors.mp hj)
  exact (not_le_of_gt hji) (hi j (Finset.mem_univ j))

end Kreps.RevealedPreference
