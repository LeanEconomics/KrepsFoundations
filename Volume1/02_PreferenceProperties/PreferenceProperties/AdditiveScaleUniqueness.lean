/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.LocalAffineUniqueness

/-!
# Uniqueness of additive scales on interval rectangles

Preparation for Proposition 2.14. Preserving the indifferences of an additive
representation on two nontrivial intervals forces a common affine scale.
Strict increase makes its slope positive. No smoothness assumption is used.
-/

namespace Kreps.PreferenceProperties

/-- Transformed coordinate scores preserve equal sums on a rectangle. -/
def PreservesPairSumEquality (f g : ℝ → ℝ) (S T : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
    x + y = x' + y' → f x + g y = f x' + g y'

/-- The equal-sum condition is symmetric in its two coordinates. -/
theorem preservesPairSumEquality_symm {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) : PreservesPairSumEquality g f T S := by
  intro y hy y' hy' x hx x' hx' he
  have := h x hx x' hx' y hy y' hy' (by linarith)
  linarith

/-- Short compensating changes in the second coordinate give a local midpoint law in the first. -/
theorem preservesPairSumEquality_midpoint {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    {a b : ℝ} (ha : a ∈ T) (hb : b ∈ T) (x t : ℝ) (ht : 0 < t) (htb : t < b - a)
    (hlo : x - t ∈ S) (hhi : x + t ∈ S) :
    f x = (f (x - t) + f (x + t)) / 2 := by
  have hx : x ∈ S := hS.out hlo hhi ⟨by linarith, by linarith⟩
  have hat : a + t ∈ T := hT.out ha hb ⟨by linarith, by linarith⟩
  have h₁ := h (x - t) hlo x hx (a + t) hat a ha (by ring)
  have h₂ := h x hx (x + t) hhi (a + t) hat a ha (by ring)
  linarith

/-- Equal-sum preservation makes the first coordinate transformation affine. -/
theorem preservesPairSumEquality_affine_left {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hc : ContinuousOn f S) {a b c d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hcT : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B : ℝ, ∀ x ∈ S, f x = A * x + B :=
  local_midpoint_affine_interval hS hc ha hb hab (sub_pos.mpr hcd)
    (fun x t ht htd hlo hhi => preservesPairSumEquality_midpoint h hS hT hcT hd
      x t ht htd hlo hhi)

/-- Two continuous additive scales on nontrivial intervals differ by one common affine slope. -/
theorem pair_additive_affine_unique {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hf : ContinuousOn f S) (hg : ContinuousOn g T) {a b c d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B C : ℝ, (∀ x ∈ S, f x = A * x + B) ∧ (∀ y ∈ T, g y = A * y + C) := by
  obtain ⟨A, B, hA⟩ := preservesPairSumEquality_affine_left h hS hT hf ha hb hab hc hd hcd
  obtain ⟨A', C, hA'⟩ := preservesPairSumEquality_affine_left
    (preservesPairSumEquality_symm h) hT hS hg hc hd hcd ha hb hab
  let t := min (b - a) (d - c)
  have ht : 0 < t := lt_min (sub_pos.mpr hab) (sub_pos.mpr hcd)
  have htS : t ≤ b - a := min_le_left _ _
  have htT : t ≤ d - c := min_le_right _ _
  have hat : a + t ∈ S := hS.out ha hb ⟨by linarith, by linarith⟩
  have hct : c + t ∈ T := hT.out hc hd ⟨by linarith, by linarith⟩
  have he := h (a + t) hat a ha c hc (c + t) hct (by ring)
  rw [hA _ hat, hA _ ha, hA' _ hc, hA' _ hct] at he
  have hAA : A = A' := by nlinarith
  exact ⟨A, B, C, hA, hAA ▸ hA'⟩

/-- Strict increase makes the common affine scale positive. -/
theorem pair_additive_positive_affine_unique {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hf : ContinuousOn f S) (hg : ContinuousOn g T) (hmono : StrictMonoOn f S)
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B C : ℝ, 0 < A ∧ (∀ x ∈ S, f x = A * x + B) ∧
      (∀ y ∈ T, g y = A * y + C) := by
  obtain ⟨A, B, C, hA, hC⟩ := pair_additive_affine_unique h hS hT hf hg ha hb hab hc hd hcd
  have hlt := hmono ha hb hab
  rw [hA _ ha, hA _ hb] at hlt
  exact ⟨A, B, C, by nlinarith, hA, hC⟩

/-- Two nontrivial coordinates fix one positive affine slope for an entire family of intervals. -/
theorem family_additive_positive_affine_unique {I : Type*} {S : I → Set ℝ}
    {f : I → ℝ → ℝ} (hS : ∀ i, (S i).OrdConnected) (hf : ∀ i, ContinuousOn (f i) (S i))
    (hp : ∀ i j, i ≠ j → PreservesPairSumEquality (f i) (f j) (S i) (S j))
    (z : I → ℝ) (hz : ∀ i, z i ∈ S i) {i₀ j₀ : I} (hij : i₀ ≠ j₀)
    (hmono : StrictMonoOn (f i₀) (S i₀)) {a b c d : ℝ}
    (ha : a ∈ S i₀) (hb : b ∈ S i₀) (hab : a < b)
    (hc : c ∈ S j₀) (hd : d ∈ S j₀) (hcd : c < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ i x, x ∈ S i →
      f i x = A * x + (f i (z i) - A * z i) := by
  classical
  obtain ⟨A, B, _, hpos, hA, _⟩ := pair_additive_positive_affine_unique (hp i₀ j₀ hij)
    (hS i₀) (hS j₀) (hf i₀) (hf j₀) hmono ha hb hab hc hd hcd
  refine ⟨A, hpos, fun i x hx => ?_⟩
  by_cases hi : i = i₀
  · subst i
    have hxA := hA x hx
    have hzA := hA (z i₀) (hz i₀)
    linarith
  · by_cases hnt : (S i).Nontrivial
    · obtain ⟨c', hc', d', hd', hcd'⟩ := hnt.exists_lt
      obtain ⟨A', B', C', hA', hC'⟩ := pair_additive_affine_unique
        (hp i₀ i (Ne.symm hi)) (hS i₀) (hS i) (hf i₀) (hf i) ha hb hab hc' hd' hcd'
      have hAa := hA a ha
      have hAb := hA b hb
      have hA'a := hA' a ha
      have hA'b := hA' b hb
      have he : A = A' := by nlinarith
      have hxA := hC' x hx
      have hzA := hC' (z i) (hz i)
      rw [← he] at hxA hzA
      linarith
    · have he : x = z i := by
        by_contra hne
        exact hnt ⟨x, hx, z i, hz i, hne⟩
      rw [he]
      ring

/-- Fixing every baseline and one unit increment removes all affine freedom on an overlap. -/
theorem normalized_additive_scales_unique {I : Type*} {S : I → Set ℝ} {f : I → ℝ → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hf : ∀ i, ContinuousOn (f i) (S i))
    (hp : ∀ i j, i ≠ j → PreservesPairSumEquality (f i) (f j) (S i) (S j))
    (hz : ∀ i, (0 : ℝ) ∈ S i) (hzero : ∀ i, f i 0 = 0)
    {i₀ j₀ : I} (hij : i₀ ≠ j₀) (hmono : StrictMonoOn (f i₀) (S i₀))
    (hunit : (1 : ℝ) ∈ S i₀) (hone : f i₀ 1 = 1) {c d : ℝ}
    (hc : c ∈ S j₀) (hd : d ∈ S j₀) (hcd : c < d) :
    ∀ i x, x ∈ S i → f i x = x := by
  obtain ⟨A, _, hA⟩ := family_additive_positive_affine_unique hS hf hp (fun _ => 0) hz hij
    hmono (hz i₀) hunit zero_lt_one hc hd hcd
  have hAu := hA i₀ 1 hunit
  have hAone : A = 1 := by simpa only [hone, hzero, mul_one, mul_zero, sub_zero, add_zero]
    using hAu.symm
  intro i x hx
  simpa only [hAone, one_mul, hzero, mul_zero, sub_zero, add_zero] using hA i x hx

end Kreps.PreferenceProperties
