/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.AlternativeMixtureAxioms

/-!
# Equivalence of the two mixture axiom systems

Kreps I, Proposition 5.11, pp. 100–101. A small move toward the common
background strictly improves or worsens a tied endpoint when that background
has a different rank. Endpoint continuity then prevents any strict comparison
between mixtures of initially tied alternatives.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Nested mixtures with the same baseline commute in the two weights. -/
theorem mix_shared_baseline_comm (a t : Weight) (x z : Z) :
    Mix t (Mix a x z) z = Mix a (Mix t x z) z := by
  let w : Weight := ⟨t.val * a.val, mul_nonneg t.property.1 a.property.1,
    (mul_le_mul_of_nonneg_left a.property.2 t.property.1).trans (by simpa using t.property.2)⟩
  exact (mix_toward_baseline t a w rfl x z).trans
    (mix_toward_baseline a t w (mul_comm _ _) x z).symm

/-- Strict independence and endpoint continuity preserve ties under common mixtures. -/
theorem alt_no_strict_of_indifferent (hr : Rational r) (hb : StrictIndependence r)
    (hc : MixtureContinuous r) {x y : Z} (he : Indifferent r x y)
    (a : Weight) (ha₀ : 0 < a.val) (ha₁ : a.val < 1) (z : Z) :
    ¬Strict r (Mix a x z) (Mix a y z) := by
  intro hs
  obtain ⟨c, hc', ht⟩ := hc _ _ hs z
  let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc'.1, hc'.2]⟩
  have hct : c < t.val := by dsimp [t]; linarith [hc'.2]
  have ht₀ : 0 < (Complement t).val := by dsimp [Complement, t]; linarith [hc'.2]
  have ht₁ : (Complement t).val < 1 := by dsimp [Complement, t]; linarith [hc'.1]
  obtain ⟨hleft, hright⟩ := ht t hct
  rw [mix_shared_baseline_comm] at hleft hright
  by_cases hxz : r x z
  · by_cases hzx : r z x
    · have hyz := hr.2 y x z he.2 hxz
      exact hs.2 (hr.2 _ z _ (alt_segment_bounds hr hb hyz a).2
        (hr.2 z x _ hzx (alt_segment_bounds hr hb hxz a).1))
    · have hx := (proposition_1_9a hr.1 _ _).mpr hzx
      have hd := hb x z hx (Complement t) ht₀ ht₁ x
      rw [mix_self, mix_complement] at hd
      exact hleft.2 (hb y _ (weak_strict_trans hr.2 he.2 hd) a ha₀ ha₁ z).1
  · have hzy := strict_weak_trans hr.2 ((proposition_1_9a hr.1 _ _).mpr hxz) he.1
    have hd := hb z y hzy (Complement t) ht₀ ht₁ y
    rw [mix_complement, mix_self] at hd
    exact hright.2 (hb _ x (strict_weak_trans hr.2 hd he.2) a ha₀ ha₁ z).1

/-- At each interior weight, strict comparisons in a common mixture reflect the input ranking. -/
theorem alt_mix_strict_iff (hr : Rational r) (hb : StrictIndependence r)
    (hc : MixtureContinuous r) (a : Weight) (ha₀ : 0 < a.val) (ha₁ : a.val < 1)
    (x y z : Z) : Strict r (Mix a x z) (Mix a y z) ↔ Strict r x y := by
  refine ⟨fun hs => ?_, fun hh => hb x y hh a ha₀ ha₁ z⟩
  apply (proposition_1_9a hr.1 _ _).mpr
  intro hyx
  by_cases hxy : r x y
  · exact alt_no_strict_of_indifferent hr hb hc ⟨hxy, hyx⟩ a ha₀ ha₁ z hs
  · exact hs.2 (hb y x ⟨hyx, hxy⟩ a ha₀ ha₁ z).1

/-- **Proposition 5.11:** the alternative pair of axioms is equivalent to the original pair. -/
theorem proposition_5_11 (hr : Rational r) :
    (BackgroundIndependent r ∧ MixtureContinuous r) ↔ StrictIndependence r ∧ ArchimedeanMix r := by
  constructor
  · rintro ⟨hb, hc⟩
    have h : MixtureAxioms r := ⟨hr, hb, hc⟩
    refine ⟨fun _ _ hxy a hp _ z => mix_strict h hxy a hp z, ?_⟩
    intro x y z hxy hyz
    obtain ⟨l, hl, h₁⟩ := hc x y hxy z
    obtain ⟨m, hm, h₂⟩ := hc y z hyz x
    let a : Weight := ⟨(l + 1) / 2, by constructor <;> linarith [hl.1, hl.2]⟩
    let b : Weight := ⟨(m + 1) / 2, by constructor <;> linarith [hm.1, hm.2]⟩
    refine ⟨a, Complement b, ?_, ?_, (h₁ a (by dsimp [a]; linarith [hl.2])).1, ?_⟩
    · dsimp [a]
      constructor <;> linarith [hl.1, hl.2]
    · dsimp [b, Complement]
      constructor <;> linarith [hm.1, hm.2]
    · rw [mix_complement]
      exact (h₂ b (by dsimp [b]; linarith [hm.2])).2
  · rintro ⟨hb, hc⟩
    have hc' := alt_mixtureContinuous hr hb hc
    refine ⟨?_, hc'⟩
    intro a x y z w
    by_cases h0 : a.val = 0
    · rw [show a = 0 from Subtype.ext h0, mix_zero, mix_zero, mix_zero, mix_zero]
      simp [Strict]
    by_cases h1 : a.val = 1
    · rw [show a = 1 from Subtype.ext h1, mix_one, mix_one, mix_one, mix_one]
    have hp := lt_of_le_of_ne a.property.1 (Ne.symm h0)
    have hl := lt_of_le_of_ne a.property.2 h1
    exact (alt_mix_strict_iff hr hb hc' a hp hl x y z).trans
      (alt_mix_strict_iff hr hb hc' a hp hl x y w).symm

end Kreps.ChoiceUnderUncertainty
