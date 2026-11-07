/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.BisymmetricArithmeticMean

/-!
# Continuous cardinal scales for strict bisymmetric means

The lower-cut scale is continuous because its range contains all dyadic ranks.
Density of the original mean grid makes the scale strict, and continuity
extends the grid midpoint identity to every pair of points.
-/

namespace Kreps.PreferenceProperties

variable {α : Type*} [LinearOrder α]

/-- The completed scale with its unit-interval codomain made explicit. -/
noncomputable def MeanUnitScale (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) (x : α) : Set.Icc (0 : ℝ) 1 :=
  ⟨MeanCardinalScale M a b x, meanCardinalScale_mem M a b x (ha x)⟩

/-- The completed scale has dense range, since it attains every dyadic rank. -/
theorem meanUnitScale_denseRange (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) : DenseRange (MeanUnitScale M a b ha) := by
  apply unitArithmeticMean_dense.mono
  rintro q ⟨n, k, hk, rfl⟩
  refine ⟨MeanDyadicGrid M.mean a b n k, ?_⟩
  apply Subtype.ext
  exact (meanCardinalScale_grid M hab ha n k hk).trans
    (unitArithmeticMean_grid n k hk).symm

/-- Monotonicity and dense numerical range make the completed scale continuous. -/
theorem meanCardinalScale_continuous [TopologicalSpace α] [OrderTopology α]
    (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) (ha : ∀ x, a ≤ x) :
    Continuous (MeanCardinalScale M a b) := by
  have hm : Monotone (MeanUnitScale M a b ha) := meanCardinalScale_mono M a b ha
  exact continuous_subtype_val.comp
    (hm.continuous_of_denseRange (meanUnitScale_denseRange M hab ha))

/-- The completed scale preserves means of arbitrary dyadic grid points. -/
theorem meanCardinalScale_grid_mean (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (n m i j : ℕ)
    (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ m) :
    MeanCardinalScale M a b
      (M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b m j)) =
      (MeanCardinalScale M a b (MeanDyadicGrid M.mean a b n i) +
        MeanCardinalScale M a b (MeanDyadicGrid M.mean a b m j)) / 2 := by
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hsum : i * 2 ^ m + j * 2 ^ n ≤ 2 ^ (n + m + 1) := by
    rw [pow_succ]
    omega
  have hleft := meanDyadicGrid_refine M a b n m i
  have hright := meanDyadicGrid_refine M a b m n j
  rw [Nat.add_comm m n] at hright
  have hmean : M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b m j) =
      MeanDyadicGrid M.mean a b (n + m + 1) (i * 2 ^ m + j * 2 ^ n) := by
    rw [← hleft, ← hright]
    exact meanDyadicGrid_midpoint M a b (n + m) _ _ hi' hj'
  rw [hmean, meanCardinalScale_grid M hab ha _ _ hsum,
    meanCardinalScale_grid M hab ha _ _ hi, meanCardinalScale_grid M hab ha _ _ hj]
  simp only [MeanDyadicRank, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_succ, pow_add]
  field_simp

/-- Continuity extends the midpoint identity from the dense grid to all points. -/
theorem meanCardinalScale_mean [TopologicalSpace α] [OrderTopology α]
    (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) (ha : ∀ x, a ≤ x)
    (hd : Dense (MeanDyadicPoints M a b))
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) (x y : α) :
    MeanCardinalScale M a b (M.mean x y) =
      (MeanCardinalScale M a b x + MeanCardinalScale M a b y) / 2 := by
  have hs := meanCardinalScale_continuous M hab ha
  have hclosed : IsClosed {p : α × α | MeanCardinalScale M a b (M.mean p.1 p.2) =
      (MeanCardinalScale M a b p.1 + MeanCardinalScale M a b p.2) / 2} :=
    isClosed_eq (hs.comp hc) ((hs.comp continuous_fst).add
      (hs.comp continuous_snd) |>.div_const 2)
  have hsub : MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b ⊆
      {p : α × α | MeanCardinalScale M a b (M.mean p.1 p.2) =
        (MeanCardinalScale M a b p.1 + MeanCardinalScale M a b p.2) / 2} := by
    rintro ⟨u, v⟩ ⟨⟨n, i, hi, rfl⟩, ⟨m, j, hj, rfl⟩⟩
    exact meanCardinalScale_grid_mean M hab ha n m i j hi hj
  have hxy : (x, y) ∈ closure (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) := by
    rw [closure_prod_eq]
    exact ⟨hd x, hd y⟩
  exact closure_minimal hsub hclosed hxy

/-- A compact interval's continuous strict bisymmetric mean admits a continuous cardinal scale. -/
theorem exists_continuous_bisymmetricMean_scale [TopologicalSpace α] [OrderTopology α]
    [CompactSpace α] [DenselyOrdered α] (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) :
    ∃ φ : α → ℝ, Continuous φ ∧ StrictMono φ ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ x y, φ (M.mean x y) = (φ x + φ y) / 2 := by
  have hd := meanDyadicPoints_dense M a b ha hb hc
  refine ⟨MeanCardinalScale M a b, meanCardinalScale_continuous M hab ha,
    meanCardinalScale_strictMono M hab ha hd, ?_, ?_, meanCardinalScale_mean M hab ha hd hc⟩
  · simpa only [meanDyadicGrid_left, MeanDyadicRank, Nat.cast_zero, zero_div] using
      meanCardinalScale_grid M hab ha 0 0 (by norm_num)
  · simpa [MeanDyadicGrid, MeanDyadicRank] using
      meanCardinalScale_grid M hab ha 0 1 (by norm_num)

end Kreps.PreferenceProperties
