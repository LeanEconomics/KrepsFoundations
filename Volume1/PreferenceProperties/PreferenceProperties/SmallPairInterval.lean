/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommonScoreInterval

/-!
# A compact interval with attainable pair values

Continuity at an interior normalized baseline supplies a smaller closed
interval whose two-factor utility values remain in the common open score
domain. The midpoint construction can therefore use the derived medial law.
-/

namespace Kreps.PreferenceProperties

/-- Close enough to the normalized baseline, all pair values stay in the common score domain. -/
theorem exists_small_pair_interval {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) (e : J) (he : v (e, e, e) = e.val) :
    ∃ a b : ℝ, a < e.val ∧ e.val < b ∧ Set.Icc a b ⊆ J ∧
      ∀ x y : J, x.val ∈ Set.Icc a b → y.val ∈ Set.Icc a b → v (x, y, e) ∈ J := by
  have hpc : Continuous (fun p : J × J => v (p.1, p.2, e)) :=
    hc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hmem : v (e, e, e) ∈ J := by rw [he]; exact e.property
  have hn := (hJ.preimage hpc).mem_nhds
    (show (e, e) ∈ (fun p : J × J => v (p.1, p.2, e)) ⁻¹' J from hmem)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨W, hW, hWsub⟩ := (mem_nhds_subtype J e (U ∩ V)).mp (Filter.inter_mem hU hV)
  obtain ⟨L, R, heLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hW (hJ.mem_nhds e.property))
  let a := (L + e.val) / 2
  let b := (e.val + R) / 2
  have hal : L < a := by dsimp [a]; linarith [heLR.1]
  have hae : a < e.val := by dsimp [a]; linarith [heLR.1]
  have heb : e.val < b := by dsimp [b]; linarith [heLR.2]
  have hbr : b < R := by dsimp [b]; linarith [heLR.2]
  have hab : Set.Icc a b ⊆ Set.Ioo L R :=
    fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hbr⟩
  refine ⟨a, b, hae, heb, fun x hx => (hLR (hab hx)).2, ?_⟩
  intro x y hx hy
  have hxu : x ∈ U := (hWsub (show x.val ∈ W from (hLR (hab hx)).1)).1
  have hyv : y ∈ V := (hWsub (show y.val ∈ W from (hLR (hab hy)).1)).2
  exact hUV (show (x, y) ∈ U ×ˢ V from ⟨hxu, hyv⟩)

/-- Normalized axes give the baseline identity needed for the compact-interval construction. -/
theorem normalizedThreeAxes_small_pair_interval {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) {e : J}
    (hn : NormalizedThreeAxes v Subtype.val e) :
    ∃ a b : ℝ, a < e.val ∧ e.val < b ∧ Set.Icc a b ⊆ J ∧
      ∀ x y : J, x.val ∈ Set.Icc a b → y.val ∈ Set.Icc a b → v (x, y, e) ∈ J :=
  exists_small_pair_interval hJ hc e (hn.1 e)

end Kreps.PreferenceProperties
