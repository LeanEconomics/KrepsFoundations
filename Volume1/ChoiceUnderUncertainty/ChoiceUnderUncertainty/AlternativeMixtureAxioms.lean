/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureRepresentation

/-!
# Strict independence and the Archimedean mixture axiom

Kreps I, Proposition 5.11, pp. 100–101. This module derives the original
endpoint continuity condition from the alternative strict-independence and
intermediate-mixture conditions. The proof uses both directions of the
reference order and covers mixtures of tied endpoints.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Proposition 5.11(b′): every interior common-background mixture preserves strict preference. -/
def StrictIndependence (r : Z → Z → Prop) : Prop :=
  ∀ x y, Strict r x y → ∀ (a : Weight), 0 < a.val → a.val < 1 → ∀ z,
    Strict r (Mix a x z) (Mix a y z)

/-- Proposition 5.11(c′): a strictly intermediate alternative lies between two interior mixtures. -/
def ArchimedeanMix (r : Z → Z → Prop) : Prop :=
  ∀ x y z, Strict r x y → Strict r y z → ∃ (a b : Weight),
    (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
    Strict r (Mix a x z) y ∧ Strict r y (Mix b x z)

/-- Complementary probabilities exchange the two outcomes. -/
theorem mix_complement (a : Weight) (x y : Z) : Mix (Complement a) y x = Mix a x y :=
  (mix_swap a x y).symm

/-- Reversal preserves the strict triple axiom, with complementary probabilities. -/
theorem archimedeanMix_reverse (hc : ArchimedeanMix r) :
    ArchimedeanMix (fun x y => r y x) := by
  intro x y z hxy hyz
  obtain ⟨a, b, ha, hb, h₁, h₂⟩ := hc z y x hyz hxy
  refine ⟨Complement b, Complement a, ?_, ?_, ?_, ?_⟩
  · exact ⟨sub_pos.mpr hb.2, sub_lt_self _ hb.1⟩
  · exact ⟨sub_pos.mpr ha.2, sub_lt_self _ ha.1⟩
  · rwa [mix_complement]
  · rwa [mix_complement]

/-- Strict improvements in both components strictly improve an interior mixture. -/
theorem mix_strict_both (hr : Rational r) (hb : StrictIndependence r)
    {x x' y y' : Z} (hx : Strict r x x') (hy : Strict r y y')
    (a : Weight) (h₀ : 0 < a.val) (h₁ : a.val < 1) :
    Strict r (Mix a x y) (Mix a x' y') := by
  apply proposition_1_9h hr.2 _ (Mix a x' y) _ (hb x x' hx a h₀ h₁ y)
  rw [mix_swap a x' y, mix_swap a x' y']
  exact hb y y' hy _ (sub_pos.mpr h₁) (sub_lt_self _ h₀) x'

/-- Strict independence alone puts mixtures between weakly ordered endpoints. -/
theorem alt_segment_bounds (hr : Rational r) (hb : StrictIndependence r)
    {x y : Z} (hxy : r x y) (a : Weight) : r x (Mix a x y) ∧ r (Mix a x y) y := by
  by_cases h₀ : a.val = 0
  · rw [show a = 0 from Subtype.ext h₀, mix_zero]
    exact ⟨hxy, complete_refl hr.1 _⟩
  by_cases h₁ : a.val = 1
  · rw [show a = 1 from Subtype.ext h₁, mix_one]
    exact ⟨complete_refl hr.1 _, hxy⟩
  have hp := lt_of_le_of_ne a.property.1 (Ne.symm h₀)
  have hl := lt_of_le_of_ne a.property.2 h₁
  constructor
  · by_contra hn
    have hs := (proposition_1_9a hr.1 _ _).mpr hn
    have bad := mix_strict_both hr hb hs (strict_weak_trans hr.2 hs hxy) a hp hl
    rw [mix_self] at bad
    exact bad.2 bad.1
  · by_contra hn
    have hs := (proposition_1_9a hr.1 _ _).mpr hn
    have bad := mix_strict_both hr hb (weak_strict_trans hr.2 hxy hs) hs a hp hl
    rw [mix_self] at bad
    exact bad.2 bad.1

/-- Reducing the probability of the first endpoint multiplies its two weights. -/
theorem mix_toward_baseline (a t s : Weight) (he : a.val * t.val = s.val) (x y : Z) :
    Mix a (Mix t x y) y = Mix s x y := by
  calc
    _ = Mix a (Mix t x y) (Mix 0 x y) := by rw [mix_zero]
    _ = Mix (WeightMean a t 0) x y := mix_mix ..
    _ = _ := by
      apply congrArg (fun v => Mix v x y)
      apply Subtype.ext
      simpa [WeightMean] using he

/-- Ordered endpoints give weak monotonicity in the probability under strict independence. -/
theorem alt_segment_mono (hr : Rational r) (hb : StrictIndependence r) {x y : Z}
    (hxy : r x y) (s t : Weight) (hst : s.val ≤ t.val) : r (Mix t x y) (Mix s x y) := by
  by_cases h₀ : t.val = 0
  · have he : s = t := Subtype.ext (le_antisymm hst (h₀ ▸ s.property.1))
    rw [he]
    exact complete_refl hr.1 _
  have hp := lt_of_le_of_ne t.property.1 (Ne.symm h₀)
  let a : Weight := ⟨s.val / t.val, div_nonneg s.property.1 hp.le, (div_le_one hp).mpr hst⟩
  have he := mix_toward_baseline a t s (div_mul_cancel₀ _ hp.ne') x y
  exact he ▸ (alt_segment_bounds hr hb (alt_segment_bounds hr hb hxy t).2 a).1

/-- Some threshold makes mixtures near the better outcome strictly better than the lower one. -/
theorem alt_near_better (hr : Rational r) (hb : StrictIndependence r) (hc : ArchimedeanMix r)
    {x y : Z} (hxy : Strict r x y) (z : Z) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ a : Weight, c < a.val → Strict r (Mix a x z) y := by
  by_cases hzx : r z x
  · refine ⟨1 / 2, by constructor <;> norm_num, fun a _ => ?_⟩
    rw [mix_swap]
    exact weak_strict_trans hr.2 (alt_segment_bounds hr hb hzx _).2 hxy
  have hxz := (proposition_1_9a hr.1 _ _).mpr hzx
  by_cases hzy : r z y
  · refine ⟨1 / 2, by constructor <;> norm_num, fun a ha => ?_⟩
    by_cases he : a.val = 1
    · rwa [show a = 1 from Subtype.ext he, mix_one]
    have hp := hb x z hxz a (by linarith) (lt_of_le_of_ne a.property.2 he) z
    rw [mix_self] at hp
    exact strict_weak_trans hr.2 hp hzy
  · obtain ⟨a, _, ha, _, hs, _⟩ := hc x y z hxy ((proposition_1_9a hr.1 _ _).mpr hzy)
    exact ⟨a.val, ha, fun d hd => weak_strict_trans hr.2
      (alt_segment_mono hr hb hxz.1 a d hd.le) hs⟩

/-- The two-sided endpoint condition follows from the alternative axioms. -/
theorem alt_mixtureContinuous (hr : Rational r) (hb : StrictIndependence r)
    (hc : ArchimedeanMix r) : MixtureContinuous r := by
  intro x y hxy z
  obtain ⟨l, hl, h₁⟩ := alt_near_better hr hb hc hxy z
  have hr' : Rational (fun x y => r y x) :=
    ⟨fun a b => (hr.1 b a), fun a b c h₁ h₂ => hr.2 c b a h₂ h₁⟩
  have hb' : StrictIndependence (fun x y => r y x) :=
    fun a b hh t hp hl w => hb b a hh t hp hl w
  obtain ⟨m, hm, h₂⟩ := alt_near_better hr' hb' (archimedeanMix_reverse hc)
    (show Strict (fun x y => r y x) y x from hxy) z
  exact ⟨max l m, ⟨hl.1.trans_le (le_max_left _ _), max_lt hl.2 hm.2⟩,
    fun a ha => ⟨h₁ a ((le_max_left _ _).trans_lt ha), h₂ a ((le_max_right _ _).trans_lt ha)⟩⟩

end Kreps.ChoiceUnderUncertainty
