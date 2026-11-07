/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.LocalToGlobalOrder
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Convex.Basic

/-!
# Globalizing aligned local pair comparisons

Continuous increasing coordinate scales identify real intervals with their interval images.
Straight interpolation in those score images gives paths whose total score is monotone.
The local comparison cover therefore globalizes, including indifference, without assuming
smoothness or a common size for chart neighborhoods.
-/

namespace Kreps.PreferenceProperties

open Set
open scoped unitInterval

/-- A continuous increasing interval coordinate admits a path affine in its score. -/
theorem exists_affine_score_path {S : Set ℝ} (hS : S.OrdConnected) {f : S → ℝ}
    (hf : Continuous f) (hm : StrictMono f) (x y : S) :
    ∃ p : I → S, Continuous p ∧ p 0 = x ∧ p 1 = y ∧
      ∀ t, f (p t) = (1 - t.val) * f x + t.val * f y := by
  let : Fact S.OrdConnected := ⟨hS⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  have hR : (range f).OrdConnected := (isPreconnected_range hf).ordConnected
  let : Fact (range f).OrdConnected := ⟨hR⟩
  let e : S ≃o range f := StrictMono.orderIso f hm
  let r : I → range f := fun t =>
    ⟨(1 - t.val) * f x + t.val * f y, by
      simpa only [smul_eq_mul] using hR.convex ⟨x, rfl⟩ ⟨y, rfl⟩
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩
  have hrc : Continuous r :=
    (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)).subtype_mk _
  have hr0 : r 0 = e x := Subtype.ext (by simp [r, e])
  have hr1 : r 1 = e y := Subtype.ext (by simp [r, e])
  refine ⟨fun t => e.symm (r t), e.symm.continuous.comp hrc, ?_, ?_, ?_⟩
  · change e.symm (r 0) = x
    rw [hr0]
    exact e.symm_apply_apply x
  · change e.symm (r 1) = y
    rw [hr1]
    exact e.symm_apply_apply y
  · intro t
    exact congrArg Subtype.val (e.apply_symm_apply (r t))

/-- Locally represented pair preferences have the same additive representation globally. -/
theorem pair_global_order_of_local_comparisons {S T : Set ℝ}
    (hS : S.OrdConnected) (hT : T.OrdConnected) {f : S → ℝ} {g : T → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfm : StrictMono f) (hgm : StrictMono g)
    {U : S × T → ℝ}
    (hl : ∀ p : S × T, ∃ N : Set (S × T), IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ N, ∀ r ∈ N, U q ≤ U r ↔ f q.1 + g q.2 ≤ f r.1 + g r.2) :
    ∀ p q : S × T, U p ≤ U q ↔ f p.1 + g p.2 ≤ f q.1 + g q.2 := by
  apply global_order_of_local_comparisons hl
  intro x y hxy
  obtain ⟨p, hpc, hp0, hp1, hpf⟩ := exists_affine_score_path hS hf hfm x.1 y.1
  obtain ⟨q, hqc, hq0, hq1, hqg⟩ := exists_affine_score_path hT hg hgm x.2 y.2
  refine ⟨fun t => (p t, q t), hpc.prodMk hqc, ?_, ?_, ?_⟩
  · simp only [hp0, hq0]
  · simp only [hp1, hq1]
  · intro a b hab
    change a.val ≤ b.val at hab
    change f (p a) + g (q a) ≤ f (p b) + g (q b)
    rw [hpf, hqg, hpf, hqg]
    have hnonneg := mul_nonneg (sub_nonneg.mpr hab)
      (sub_nonneg.mpr hxy)
    change 0 ≤ (b.val - a.val) * ((f y.1 + g y.2) - (f x.1 + g x.2)) at hnonneg
    nlinarith

end Kreps.PreferenceProperties
