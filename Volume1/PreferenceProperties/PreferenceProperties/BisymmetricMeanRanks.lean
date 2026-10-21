/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.BisymmetricMeanDensity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cardinal ranks on the dyadic mean grid

An index `k` at subdivision level `n` receives rank `k / 2 ^ n`. The strict
ordering of every common refinement makes this assignment independent of the
chosen subdivision level. Suprema of lower ranks then extend it to all points.
-/

namespace Kreps.PreferenceProperties

variable {α : Type*} [LinearOrder α]

/-- The numerical rank of an index in a dyadic grid. -/
noncomputable def MeanDyadicRank (n k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ n

/-- Valid grid indices have ranks between zero and one. -/
theorem meanDyadicRank_mem (n k : ℕ) (hk : k ≤ 2 ^ n) :
    MeanDyadicRank n k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg k) (by positivity)
  · apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).2
    exact_mod_cast hk

/-- Cross-level grid comparisons coincide exactly with comparisons of their dyadic ranks. -/
theorem meanDyadicGrid_le_iff_rank (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (n m i j : ℕ) (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ m) :
    MeanDyadicGrid M.mean a b n i ≤ MeanDyadicGrid M.mean a b m j ↔
      MeanDyadicRank n i ≤ MeanDyadicRank m j := by
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hleft := meanDyadicGrid_refine M a b n m i
  have hright := meanDyadicGrid_refine M a b m n j
  rw [Nat.add_comm m n] at hright
  rw [← hleft, ← hright,
    (meanDyadicGrid_strictMonoOn M hab (n + m)).le_iff_le hi' hj']
  unfold MeanDyadicRank
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast

/-- The lower numerical ranks at an arbitrary point. -/
def MeanRankCut (M : OrderedBisymmetricMean α) (a b x : α) : Set ℝ :=
  {q | ∃ n k, k ≤ 2 ^ n ∧ q = MeanDyadicRank n k ∧ MeanDyadicGrid M.mean a b n k ≤ x}

/-- The left endpoint's rank ensures each cut is nonempty. -/
theorem meanRankCut_nonempty (M : OrderedBisymmetricMean α) (a b x : α) (hax : a ≤ x) :
    (MeanRankCut M a b x).Nonempty := by
  refine ⟨0, 0, 0, by norm_num, by simp [MeanDyadicRank], ?_⟩
  simpa only [meanDyadicGrid_left] using hax

/-- One bounds every lower dyadic cut. -/
theorem meanRankCut_bddAbove (M : OrderedBisymmetricMean α) (a b x : α) :
    BddAbove (MeanRankCut M a b x) := by
  refine ⟨1, ?_⟩
  rintro q ⟨n, k, hk, rfl, _⟩
  exact (meanDyadicRank_mem n k hk).2

/-- Extending the prescribed dyadic ranks by their lower-cut suprema. -/
noncomputable def MeanCardinalScale (M : OrderedBisymmetricMean α) (a b x : α) : ℝ :=
  sSup (MeanRankCut M a b x)

/-- The completed scale stays in the unit interval. -/
theorem meanCardinalScale_mem (M : OrderedBisymmetricMean α) (a b x : α) (hax : a ≤ x) :
    MeanCardinalScale M a b x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply le_csSup (meanRankCut_bddAbove M a b x)
    refine ⟨0, 0, by norm_num, by simp [MeanDyadicRank], ?_⟩
    simpa only [meanDyadicGrid_left] using hax
  · apply csSup_le (meanRankCut_nonempty M a b x hax)
    rintro q ⟨n, k, hk, rfl, _⟩
    exact (meanDyadicRank_mem n k hk).2

/-- Inclusion of lower cuts makes the scale monotone. -/
theorem meanCardinalScale_mono (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) : Monotone (MeanCardinalScale M a b) := by
  intro x y hxy
  apply csSup_le (meanRankCut_nonempty M a b x (ha x))
  rintro q ⟨n, k, hk, rfl, hx⟩
  exact le_csSup (meanRankCut_bddAbove M a b y) ⟨n, k, hk, rfl, hx.trans hxy⟩

/-- The supremum extension agrees with every original grid rank. -/
theorem meanCardinalScale_grid (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    MeanCardinalScale M a b (MeanDyadicGrid M.mean a b n k) = MeanDyadicRank n k := by
  apply le_antisymm
  · apply csSup_le (meanRankCut_nonempty M a b _ (ha _))
    rintro q ⟨m, i, hi, rfl, hle⟩
    exact (meanDyadicGrid_le_iff_rank M hab m n i k hi hk).1 hle
  · exact le_csSup (meanRankCut_bddAbove M a b _) ⟨n, k, hk, rfl, le_rfl⟩

/-- Density of the grid makes the completed scale strictly increasing. -/
theorem meanCardinalScale_strictMono [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (ha : ∀ x, a ≤ x) (hd : Dense (MeanDyadicPoints M a b)) :
    StrictMono (MeanCardinalScale M a b) := by
  intro x y hxy
  obtain ⟨u, hu, hxu, huy⟩ := hd.exists_between hxy
  obtain ⟨v, hv, huv, hvy⟩ := hd.exists_between huy
  obtain ⟨n, i, hi, rfl⟩ := hu
  obtain ⟨m, j, hj, rfl⟩ := hv
  have hlt : MeanDyadicRank n i < MeanDyadicRank m j := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt huv) ((meanDyadicGrid_le_iff_rank M hab m n j i hj hi).2 h)
  calc
    MeanCardinalScale M a b x ≤ MeanDyadicRank n i := by
      rw [← meanCardinalScale_grid M hab ha n i hi]
      exact meanCardinalScale_mono M a b ha hxu.le
    _ < MeanDyadicRank m j := hlt
    _ ≤ MeanCardinalScale M a b y := by
      rw [← meanCardinalScale_grid M hab ha m j hj]
      exact meanCardinalScale_mono M a b ha hvy.le

end Kreps.PreferenceProperties
