/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryBoundedCalibration

/-!
Local prerequisite copy of ChoiceUnderUncertainty.UnboundedCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Calibration without global best and worst alternatives

Kreps I, pp. 94–95 and Problem 5.3, p. 118. Normalize two strictly ranked
anchors at one and zero. Alternatives between, above, and below them receive
the three values in the book's construction. Any normalized affine index on
an interval containing the three alternatives must give the same value.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The three possible calibrations relative to an anchor at one and an anchor at zero. -/
def Calibrates (r : Z → Z → Prop) (g b z : Z) (t : ℝ) : Prop :=
  (∃ a : Weight, Indifferent r z (Mix a g b) ∧ t = a.val) ∨
  (∃ a : Weight, 0 < a.val ∧ Indifferent r g (Mix a z b) ∧ t = 1 / a.val) ∨
  (∃ a : Weight, a.val < 1 ∧ Indifferent r b (Mix a g z) ∧ t = -a.val / (1 - a.val))

/-- Problem 5.3: the three calibration cases exhaust every alternative. -/
theorem exists_calibration (h : MixtureAxioms r) {g b : Z} (hgb : Strict r g b) (z : Z) :
    ∃ t, Calibrates r g b z t := by
  by_cases hg : r g z
  · by_cases hb : r z b
    · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r g b z from ⟨hg, hb⟩)
      exact ⟨a.val, Or.inl ⟨a, ha, rfl⟩⟩
    · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r g z b from
        ⟨hgb.1, (h.1.1 b z).resolve_right hb⟩)
      have hh : a.val < 1 := by
        by_contra! hle
        have he : a = 1 := Subtype.ext (le_antisymm a.property.2 hle)
        rw [he, mix_one] at ha
        exact hgb.2 ha.1
      exact ⟨_, Or.inr (Or.inr ⟨a, hh, ha, rfl⟩)⟩
  · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r z b g from
      ⟨(h.1.1 z g).resolve_right hg, hgb.1⟩)
    have hh : 0 < a.val := by
      by_contra! hle
      have he : a = 0 := Subtype.ext (le_antisymm hle a.property.1)
      rw [he, mix_zero] at ha
      exact hgb.2 ha.2
    exact ⟨_, Or.inr (Or.inl ⟨a, hh, ha, rfl⟩)⟩

/-- A finite list and the two fixed anchors fit inside a strictly ordered pair of bounds. -/
theorem exists_preference_enclosure {T : Type*} {r : T → T → Prop}
    (hr : Rational r) {g b : T} (hgb : Strict r g b)
    (zs : List T) : ∃ H L, Strict r H L ∧ Between r H L g ∧ Between r H L b ∧
      ∀ z ∈ zs, Between r H L z := by
  induction zs with
  | nil =>
    exact ⟨g, b, hgb, ⟨complete_refl hr.1 _, hgb.1⟩,
      ⟨hgb.1, complete_refl hr.1 _⟩, by simp⟩
  | cons z zs ih =>
    obtain ⟨H, L, hHL, hg, hb, hall⟩ := ih
    obtain ⟨H', hH, hzH⟩ : ∃ H', r H' H ∧ r H' z := by
      rcases hr.1 H z with h | h
      · exact ⟨H, complete_refl hr.1 _, h⟩
      · exact ⟨z, h, complete_refl hr.1 _⟩
    obtain ⟨L', hL, hzL⟩ : ∃ L', r L L' ∧ r z L' := by
      rcases hr.1 z L with h | h
      · exact ⟨L, complete_refl hr.1 _, h⟩
      · exact ⟨z, h, complete_refl hr.1 _⟩
    have hw {w} (h : Between r H L w) : Between r H' L' w :=
      ⟨hr.2 _ _ _ hH h.1, hr.2 _ _ _ h.2 hL⟩
    refine ⟨H', L', strict_weak_trans hr.2 (weak_strict_trans hr.2 hH hHL) hL,
      hw hg, hw hb, ?_⟩
    intro w hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hzH, hzL⟩
    · exact hw (hall w hm)

/-- Representing utility on one interval, normalized at any two strictly ranked interior anchors. -/
theorem normalized_interval_utility (h : MixtureAxioms r) {H L g b : Z}
    (hHL : Strict r H L) (hg : Between r H L g) (hb : Between r H L b)
    (hgb : Strict r g b) :
    ∃ v : Z → ℝ, v g = 1 ∧ v b = 0 ∧
      (∀ x y, Between r H L x → Between r H L y → (r x y ↔ v y ≤ v x)) ∧
      (∀ a x y, Between r H L x → Between r H L y →
        v (Mix a x y) = a.val * v x + (1 - a.val) * v y) := by
  let w := fun z => (AnchorWeight r H L z).val
  have hlt : w b < w g := lt_of_not_ge
    (fun hh => hgb.2 ((anchorWeight_represents h hHL hb hg).mpr hh))
  let d := w g - w b
  have hd : 0 < d := sub_pos.mpr hlt
  refine ⟨fun z => (w z - w b) / d, div_self hd.ne', by simp, ?_, ?_⟩
  · intro x y hx hy
    simp only [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right]
    exact anchorWeight_represents h hHL hx hy
  · intro a x y hx hy
    have he : w (Mix a x y) = a.val * w x + (1 - a.val) * w y :=
      congrArg Subtype.val (anchorWeight_affine h hHL hx hy a)
    dsimp only
    rw [he]
    ring

/-- Each normalized interval utility evaluates the three global calibration cases identically. -/
theorem calibration_eq_local (h : MixtureAxioms r) {H L g b z : Z}
    (hg : Between r H L g) (hb : Between r H L b) (hz : Between r H L z)
    (v : Z → ℝ) (hg' : v g = 1) (hb' : v b = 0)
    (hv : ∀ x y, Between r H L x → Between r H L y → (r x y ↔ v y ≤ v x))
    (ha : ∀ a x y, Between r H L x → Between r H L y →
      v (Mix a x y) = a.val * v x + (1 - a.val) * v y)
    {t : ℝ} (ht : Calibrates r g b z t) : t = v z := by
  have hind {x y} (hx : Between r H L x) (hy : Between r H L y) (hxy : Indifferent r x y) :
      v x = v y := le_antisymm ((hv y x hy hx).mp hxy.2) ((hv x y hx hy).mp hxy.1)
  rcases ht with ⟨a, hi, rfl⟩ | ⟨a, hp, hi, rfl⟩ | ⟨a, hp, hi, rfl⟩
  · have he := hind hz (between_mix h hg hb a) hi
    rw [ha a g b hg hb, hg', hb'] at he
    linarith
  · have he := hind hg (between_mix h hz hb a) hi
    rw [ha a z b hz hb, hg', hb'] at he
    apply (div_eq_iff hp.ne').mpr
    linarith only [he]
  · have he := hind hb (between_mix h hg hz a) hi
    rw [ha a g z hg hz, hg', hb'] at he
    apply (div_eq_iff (sub_pos.mpr hp).ne').mpr
    linarith only [he]

end Kreps.UtilityForMoney.LotteryTheory
