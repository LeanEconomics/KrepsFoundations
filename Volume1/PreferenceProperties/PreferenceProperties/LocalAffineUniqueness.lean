/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixExtrema

/-!
# Local midpoint identities and affine uniqueness

Supporting the overlap argument for Proposition 2.14. A continuous function
on an interval satisfying the midpoint identity for all sufficiently small
steps is affine. The proof uses a compact maximum argument, including the
endpoints, rather than assuming differentiability of utility.
-/

namespace Kreps.PreferenceProperties

/-- A local midpoint identity propagates nonpositive endpoint bounds over a compact interval. -/
theorem local_midpoint_nonpos {f : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : f b ≤ 0) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∀ x ∈ Set.Icc a b, f x ≤ 0 := by
  let : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  let F : Set.Icc a b → ℝ := fun x => f x.val
  have hF : Continuous F := continuousOn_iff_continuous_domRestrict.mp hc
  obtain ⟨m, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuousOn
  have hK : IsCompact {x : Set.Icc a b | F x = F m} :=
    (isClosed_eq hF continuous_const).isCompact
  obtain ⟨z, hz⟩ := hK.exists_isLeast ⟨m, rfl⟩
  have hzM : f z.val = f m.val := hz.1
  have hM : f m.val ≤ 0 := by
    by_contra h
    have hpos : 0 < f z.val := by linarith
    have hza : a < z.val := lt_of_le_of_ne z.property.1 (by
      intro he; have : f z.val = f a := congrArg f he.symm; linarith)
    have hzb : z.val < b := lt_of_le_of_ne z.property.2 (by
      intro he; have : f z.val = f b := congrArg f he; linarith)
    let d := min δ (min (z.val - a) (b - z.val))
    have hd : 0 < d := lt_min hδ (lt_min (sub_pos.mpr hza) (sub_pos.mpr hzb))
    have hdδ : d ≤ δ := min_le_left _ _
    have hda : d ≤ z.val - a := (min_le_right _ _).trans (min_le_left _ _)
    have hdb : d ≤ b - z.val := (min_le_right _ _).trans (min_le_right _ _)
    let u : Set.Icc a b := ⟨z.val - d / 2, by constructor <;> linarith⟩
    let v : Set.Icc a b := ⟨z.val + d / 2, by constructor <;> linarith⟩
    have hu : f u.val ≤ f m.val := hmax (Set.mem_univ u)
    have hv : f v.val ≤ f m.val := hmax (Set.mem_univ v)
    have hmid := hm z.val (d / 2) (by linarith) (by linarith) u.property.1 v.property.2
    have he : F u = F m := by dsimp [F, u, v] at *; linarith
    have hzle : z ≤ u := hz.2 he
    change z.val ≤ z.val - d / 2 at hzle
    linarith
  intro x hx
  exact (hmax (Set.mem_univ (⟨x, hx⟩ : Set.Icc a b))).trans hM

/-- A uniform local midpoint identity makes a continuous function affine on a compact interval. -/
theorem local_midpoint_affine_Icc {f : ℝ → ℝ} {a b δ : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∃ A B : ℝ, ∀ x ∈ Set.Icc a b, f x = A * x + B := by
  let A := (f b - f a) / (b - a)
  let g := fun x => f x - (A * (x - a) + f a)
  have hga : g a = 0 := by dsimp [g]; ring
  have hgb : g b = 0 := by
    dsimp [g, A]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hcg : ContinuousOn g (Set.Icc a b) := hc.sub
    (((continuous_const.mul (continuous_id.sub continuous_const)).add
      continuous_const).continuousOn)
  have hgm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      g x = (g (x - h) + g (x + h)) / 2 := by
    intro x h hh hhδ hxa hxb
    have := hm x h hh hhδ hxa hxb
    dsimp [g]
    linarith
  have hle := local_midpoint_nonpos hab.le hcg hga.le hgb.le hδ hgm
  have hge := local_midpoint_nonpos hab.le hcg.neg (by simp [hga]) (by simp [hgb]) hδ
    (fun x h hh hhδ hxa hxb => by
      have := hgm x h hh hhδ hxa hxb
      dsimp
      linarith)
  refine ⟨A, f a - A * a, fun x hx => ?_⟩
  have h₁ := hle x hx
  have h₂ := hge x hx
  dsimp [g] at h₁ h₂
  linarith

/-- Local midpoint identities with a common positive radius give one affine scale on an interval. -/
theorem local_midpoint_affine_interval {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S) {a b δ : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → x - h ∈ S → x + h ∈ S →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∃ A B : ℝ, ∀ x ∈ S, f x = A * x + B := by
  refine ⟨(f b - f a) / (b - a), f a - (f b - f a) / (b - a) * a, ?_⟩
  intro x hx
  have hL : min a x ∈ S := by
    by_cases h : a ≤ x
    · simpa only [min_eq_left h] using ha
    · simpa only [min_eq_right (le_of_not_ge h)] using hx
  have hR : max b x ∈ S := by
    by_cases h : b ≤ x
    · simpa only [max_eq_right h] using hx
    · simpa only [max_eq_left (le_of_not_ge h)] using hb
  have hLR : min a x < max b x := (min_le_left _ _).trans_lt
    (hab.trans_le (le_max_left _ _))
  have hsub : Set.Icc (min a x) (max b x) ⊆ S := hS.out hL hR
  obtain ⟨A, B, h⟩ := local_midpoint_affine_Icc hLR (hc.mono hsub) hδ
    (fun y t ht htδ hlo hhi => hm y t ht htδ
      (hsub ⟨hlo, by linarith⟩) (hsub ⟨by linarith, hhi⟩))
  have hfa := h a ⟨min_le_left _ _, hab.le.trans (le_max_left _ _)⟩
  have hfb := h b ⟨(min_le_left _ _).trans hab.le, le_max_left _ _⟩
  have hfx := h x ⟨min_le_right _ _, le_max_right _ _⟩
  have hA : A = (f b - f a) / (b - a) :=
    (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr (by linarith)
  rw [← hA]
  linarith

end Kreps.PreferenceProperties
