/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.GlobalCoordinateScale

/-!
# Aligning a new chart through a shared fixed companion

A chart that meets a global coordinate scale and contains the reference value
of one of its calibrated companions has one positive affine slope relative to
both that global coordinate and the companion's seed scale. Two target
coordinates sharing that companion therefore have the same local cardinal unit.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ} {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
  {i j k q : I}

/-- A new local chart aligns simultaneously with a global target scale and a seed companion. -/
theorem GlobalCoordinateScale.align_chart (G : GlobalCoordinateScale V z seed i j k)
    (hs : StronglySeparable (UtilityPref V)) (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hq : q = j ∨ q = k) (hiq : i ≠ q) (C : ScalarAdditiveChart V)
    (center : ∀ p, C.domain p) (x : S i)
    (hx : x.val ∈ C.domain i) (href : (z q).val ∈ C.domain q) :
    ∃ A B D : ℝ, 0 < A ∧
      (∀ r ∈ C.domain i ∩ (G.family.chart x).domain i,
        C.coord i r = A * G.scale r + B) ∧
      ∀ r ∈ (seed.domain q ∩ C.domain q) ∩ (G.family.chart x).domain q,
        C.coord q r = A * seed.coord q r + D := by
  let L := G.family.chart x
  have hxl : x.val ∈ L.domain i := by simpa using G.family.center x i
  have hql : (z q).val ∈ L.domain q := by
    simpa [hiq.symm] using G.family.center x q
  obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
    ((C.open_domain i).inter (L.open_domain i)) ⟨hx, hxl⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := open_real_set_has_pair
    (((seed.open_domain q).inter (C.open_domain q)).inter (L.open_domain q))
    ⟨⟨hz q, href⟩, hql⟩
  have hp : ∀ a ∈ C.domain i ∩ L.domain i, ∀ b ∈ C.domain i ∩ L.domain i,
      ∀ c ∈ (seed.domain q ∩ C.domain q) ∩ L.domain q,
      ∀ d ∈ (seed.domain q ∩ C.domain q) ∩ L.domain q,
      L.coord i a + L.coord q c = L.coord i b + L.coord q d →
        C.coord i a + C.coord q c = C.coord i b + C.coord q d := by
    intro a ha b hb c hc d hd he
    exact L.pair_compatible C hs
      (fun p => ⟨(Function.update z i x p).val, G.family.center x p⟩) center hiq
      a ⟨ha.2, ha.1⟩ b ⟨hb.2, hb.1⟩ c ⟨hc.2, hc.1.2⟩ d ⟨hd.2, hd.1.2⟩ he
  obtain ⟨A, B, D, hA, htarget, hcompanion⟩ := pair_chart_positive_affine_unique_on
    ((C.interval i).inter (L.interval i))
    (((seed.interval q).inter (C.interval q)).inter (L.interval q))
    ((L.continuous i).mono Set.inter_subset_right)
    ((C.continuous i).mono Set.inter_subset_left)
    ((L.continuous q).mono (fun _ hr => hr.2))
    ((C.continuous q).mono (fun _ hr => hr.1.2))
    ((L.increasing i).mono Set.inter_subset_right)
    ((C.increasing i).mono Set.inter_subset_left)
    ((L.increasing q).mono (fun _ hr => hr.2))
    ((C.increasing q).mono (fun _ hr => hr.1.2)) hp ha hb hab hc hd hcd
  obtain ⟨β, hβ⟩ := G.chart_agrees x
  obtain ⟨γ, hγ⟩ := G.companion_calibration q hq x
  refine ⟨A * G.slope x, B - A * G.slope x * β, A * γ + D,
    mul_pos hA (G.positive x), ?_, ?_⟩
  · intro r hr
    rw [htarget r hr, hβ r hr.2]
    field_simp [(G.positive x).ne']
    ring
  · intro r hr
    rw [hcompanion r hr, hγ r ⟨hr.1.1, hr.2⟩]
    ring

/-- Two positive affine descriptions of the same strict companion have equal slopes. -/
theorem common_companion_affine_slopes_equal {T : Set ℝ} (hT : IsOpen T)
    {x : ℝ} (hx : x ∈ T) {f g : ℝ → ℝ} (hm : StrictMonoOn f T)
    {A B C D : ℝ} (h₁ : ∀ r ∈ T, g r = A * f r + B)
    (h₂ : ∀ r ∈ T, g r = C * f r + D) : A = C := by
  obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair hT hx
  have hlt := hm ha hb hab
  have h₁a := h₁ a ha
  have h₁b := h₁ b hb
  have h₂a := h₂ a ha
  have h₂b := h₂ b hb
  nlinarith

end Kreps.PreferenceProperties
