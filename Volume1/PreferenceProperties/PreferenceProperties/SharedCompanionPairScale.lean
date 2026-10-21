/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SharedCompanionChartAlignment
import PreferenceProperties.ScalarChartPairOrder
import PreferenceProperties.PairLocalToGlobal

/-!
# Synchronizing global coordinate scales through a common companion

At any pair of coordinate values, a new additive chart overlaps each global
coordinate's slice chart. A shared fixed companion forces their two affine
slopes to agree. The resulting local pair representations globalize along
continuous paths in the two score intervals.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ} {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
  {i j a b c d q : I}

/-- Shared companions synchronize the two global scales on a neighborhood of every pair. -/
theorem globalCoordinateScale_local_pair_comparison
    (G : GlobalCoordinateScale V z seed i a b) (H : GlobalCoordinateScale V z seed j c d)
    (hl : ∀ t : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i)
    (hs : StronglySeparable (UtilityPref V)) (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q)
    (hqG : q = a ∨ q = b) (hqH : q = c ∨ q = d) (p : S i × S j) :
    ∃ N : Set (S i × S j), IsOpen N ∧ p ∈ N ∧
      ∀ r ∈ N, ∀ s ∈ N,
        V (Function.update (Function.update z i r.1) j r.2) ≤
            V (Function.update (Function.update z i s.1) j s.2) ↔
          G.scale r.1.val + H.scale r.2.val ≤ G.scale s.1.val + H.scale s.2.val := by
  let t := Function.update (Function.update z i p.1) j p.2
  obtain ⟨C, hC⟩ := hl t
  let center : ∀ n, C.domain n := fun n => ⟨(t n).val, hC n⟩
  have hiC : p.1.val ∈ C.domain i := by simpa [t, hij] using hC i
  have hjC : p.2.val ∈ C.domain j := by simpa [t] using hC j
  have hqC : (z q).val ∈ C.domain q := by simpa [t, hiq.symm, hjq.symm] using hC q
  obtain ⟨A, B, D, hA, hiA, hqA⟩ := G.align_chart hs hz hqG hiq C center p.1 hiC hqC
  obtain ⟨A', B', D', _, hjA, hqA'⟩ := H.align_chart hs hz hqH hjq C center p.2 hjC hqC
  let L := G.family.chart p.1
  let R := H.family.chart p.2
  have hqL : (z q).val ∈ L.domain q := by simpa [hiq.symm] using G.family.center p.1 q
  have hqR : (z q).val ∈ R.domain q := by simpa [hjq.symm] using H.family.center p.2 q
  let T := ((seed.domain q ∩ C.domain q) ∩ L.domain q) ∩ R.domain q
  have hTo : IsOpen T := (((seed.open_domain q).inter (C.open_domain q)).inter
    (L.open_domain q)).inter (R.open_domain q)
  have hTm : StrictMonoOn (seed.coord q) T :=
    (seed.increasing q).mono (fun _ hr => hr.1.1.1)
  have hAA : A = A' := common_companion_affine_slopes_equal hTo
    ⟨⟨⟨hz q, hqC⟩, hqL⟩, hqR⟩ hTm
    (fun r hr => hqA r hr.1) (fun r hr => hqA' r ⟨hr.1.1, hr.2⟩)
  subst A'
  let U := C.domain i ∩ L.domain i
  let W := C.domain j ∩ R.domain j
  let N : Set (S i × S j) := {r | r.1.val ∈ U ∧ r.2.val ∈ W}
  have hNo : IsOpen N :=
    (((C.open_domain i).inter (L.open_domain i)).preimage
      (continuous_subtype_val.comp continuous_fst)).inter
      (((C.open_domain j).inter (R.open_domain j)).preimage
        (continuous_subtype_val.comp continuous_snd))
  have hpN : p ∈ N := by
    refine ⟨⟨hiC, ?_⟩, ⟨hjC, ?_⟩⟩
    · simpa using G.family.center p.1 i
    · simpa using H.family.center p.2 j
  refine ⟨N, hNo, hpN, ?_⟩
  intro r hr s hsN
  have h := C.pair_comparison_iff hs center z hij
    r.1.val hr.1.1 s.1.val hsN.1.1 r.2.val hr.2.1 s.2.val hsN.2.1
  rw [hiA r.1.val hr.1, hiA s.1.val hsN.1, hjA r.2.val hr.2, hjA s.2.val hsN.2] at h
  refine h.trans ?_
  have he (u : S i × S j) :
      (A * G.scale u.1.val + B) + (A * H.scale u.2.val + B') =
        A * (G.scale u.1.val + H.scale u.2.val) + (B + B') := by ring
  rw [he r, he s, add_le_add_iff_right, mul_le_mul_iff_right₀ hA]

/-- Every pair of global coordinate scales with a common companion represents its full slice. -/
theorem globalCoordinateScale_pair_comparison
    (G : GlobalCoordinateScale V z seed i a b) (H : GlobalCoordinateScale V z seed j c d)
    (hl : ∀ t : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i)
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q)
    (hqG : q = a ∨ q = b) (hqH : q = c ∨ q = d) :
    ∀ p r : S i × S j,
      V (Function.update (Function.update z i p.1) j p.2) ≤
          V (Function.update (Function.update z i r.1) j r.2) ↔
        G.scale p.1.val + H.scale p.2.val ≤ G.scale r.1.val + H.scale r.2.val := by
  exact pair_global_order_of_local_comparisons (hS i) (hS j)
    (continuousOn_iff_continuous_domRestrict.mp G.continuous)
    (continuousOn_iff_continuous_domRestrict.mp H.continuous)
    (fun x y hxy => G.increasing x.property y.property hxy)
    (fun x y hxy => H.increasing x.property y.property hxy)
    (globalCoordinateScale_local_pair_comparison G H hl hs hz hij hiq hjq hqG hqH)

end Kreps.PreferenceProperties
