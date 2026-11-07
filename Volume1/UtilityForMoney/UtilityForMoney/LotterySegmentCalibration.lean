/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotterySegmentOrder

/-!
Local prerequisite copy of ChoiceUnderUncertainty.SegmentCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Calibration on a preference segment

Kreps I, Lemma 5.9, pp. 92–93. Take the supremum of the probabilities at which
the reference alternative is weakly preferred to the mixture. Either strict
ranking at this cut would contradict endpoint continuity or its supremum property.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- An alternative lies weakly between two ordered reference alternatives. -/
def Between (r : Z → Z → Prop) (hi lo z : Z) : Prop := r hi z ∧ r z lo

/-- On a strictly ordered segment the weak preference compares the weights exactly. -/
theorem segment_compare_iff (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (s t : Weight) : r (Mix s x y) (Mix t x y) ↔ t.val ≤ s.val := by
  refine ⟨fun hw => ?_, segment_mono h hxy.1⟩
  by_contra! hn
  exact (lemma_5_7_strict h hxy hn).2 hw

/-- **Lemma 5.9:** every intermediate alternative is indifferent to a mixture of the endpoints. -/
theorem lemma_5_9 (h : MixtureAxioms r) {x y z : Z} (hz : Between r x y z) :
    ∃ a : Weight, Indifferent r z (Mix a x y) := by
  let A : Set ℝ := {v | ∃ a : Weight, a.val = v ∧ r z (Mix a x y)}
  have hxy : r x y := h.1.2 _ z _ hz.1 hz.2
  have hA0 : (0 : ℝ) ∈ A := ⟨0, rfl, by simpa only [mix_zero] using hz.2⟩
  have hbound : (1 : ℝ) ∈ upperBounds A := fun _ ⟨a, ha, _⟩ => ha ▸ a.property.2
  let a : Weight := ⟨sSup A, le_csSup ⟨1, hbound⟩ hA0, csSup_le ⟨0, hA0⟩ hbound⟩
  refine ⟨a, ?_, ?_⟩
  · by_contra hn
    have hs := (proposition_1_9a h.1.1 _ _).mpr hn
    obtain ⟨c, hc, ht⟩ := h.2.2 _ _ hs y
    let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc.1, hc.2]⟩
    have hp := (ht t (by dsimp [t]; linarith [hc.2])).1
    have hpos : 0 < a.val := by
      by_contra! hzero
      have he : a = 0 := Subtype.ext (le_antisymm hzero a.property.1)
      rw [he, mix_zero] at hn
      exact hn hz.2
    let b := WeightMean t a 0
    have he : Mix t (Mix a x y) y = Mix b x y := by
      calc
        _ = Mix t (Mix a x y) (Mix 0 x y) := by rw [mix_zero]
        _ = _ := mix_mix ..
    rw [he] at hp
    have hb : b.val ∈ upperBounds A := by
      rintro _ ⟨w, rfl, hw⟩
      by_contra! hbw
      exact hp.2 (h.1.2 z _ _ hw (segment_mono h hxy hbw.le))
    have hab : a.val ≤ b.val := csSup_le ⟨0, hA0⟩ hb
    change _ ≤ t.val * a.val + (1 - t.val) * 0 at hab
    have htt : t.val < 1 := by dsimp [t]; linarith [hc.2]
    nlinarith [mul_pos (sub_pos.mpr htt) hpos]
  · by_contra hn
    have hs := (proposition_1_9a h.1.1 _ _).mpr hn
    obtain ⟨c, hc, ht⟩ := h.2.2 _ _ hs x
    let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc.1, hc.2]⟩
    have hp := (ht t (by dsimp [t]; linarith [hc.2])).2
    have hlt : a.val < 1 := by
      by_contra! hone
      have he : a = 1 := Subtype.ext (le_antisymm a.property.2 hone)
      rw [he, mix_one] at hn
      exact hn hz.1
    let b := WeightMean t a 1
    have he : Mix t (Mix a x y) x = Mix b x y := by
      calc
        _ = Mix t (Mix a x y) (Mix 1 x y) := by rw [mix_one]
        _ = _ := mix_mix ..
    rw [he] at hp
    have hab : b.val ≤ a.val := le_csSup ⟨1, hbound⟩ (show b.val ∈ A from ⟨b, rfl, hp.1⟩)
    change t.val * a.val + (1 - t.val) * 1 ≤ _ at hab
    have htt : t.val < 1 := by dsimp [t]; linarith [hc.2]
    nlinarith [mul_pos (sub_pos.mpr htt) (sub_pos.mpr hlt)]

/-- **Lemma 5.9, uniqueness:** strict endpoints identify the calibrating probability. -/
theorem lemma_5_9_unique (h : MixtureAxioms r) {x y z : Z} (hxy : Strict r x y)
    {a b : Weight} (ha : Indifferent r z (Mix a x y)) (hb : Indifferent r z (Mix b x y)) :
    a = b := by
  apply Subtype.ext
  apply le_antisymm
  · exact (segment_compare_iff h hxy b a).mp (h.1.2 _ z _ hb.2 ha.1)
  · exact (segment_compare_iff h hxy a b).mp (h.1.2 _ z _ ha.2 hb.1)

end Kreps.UtilityForMoney.LotteryTheory
