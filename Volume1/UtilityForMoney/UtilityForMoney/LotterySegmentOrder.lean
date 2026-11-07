/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryProbabilityGrids

/-!
Local prerequisite copy of ChoiceUnderUncertainty.SegmentOrder from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Order on a mixture segment

Kreps I, Lemmas 5.6–5.8, pp. 91–92. First transfer weak comparisons on rational
grids to every probability by the endpoint continuity axiom. A strictly ordered
pair then gives strict monotonicity at every positive probability increment.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The lower endpoint is weakly dominated at every probability of the better outcome. -/
theorem segment_base_weak (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (d : Weight) :
    r (Mix d x y) y := by
  by_cases hz : d.val = 0
  · have he : d = 0 := Subtype.ext hz
    rw [he, mix_zero]
    exact complete_refl h.1.1 y
  have hd := lt_of_le_of_ne d.property.1 (Ne.symm hz)
  by_contra hn
  have hrev := (proposition_1_9a h.1.1 _ _).mpr hn
  obtain ⟨c, hc, ht⟩ := h.2.2 y (Mix d x y) hrev y
  obtain ⟨n, m, hN, hM, hMN, hlo, hhi⟩ := exists_gridWeight_between
    (mul_nonneg hc.1.le hd.le) (mul_lt_of_lt_one_left hd hc.2) d.property.2
  let q := GridWeight n m (by omega) hMN
  let a : Weight := ⟨q.val / d.val, div_nonneg q.property.1 hd.le,
    (div_le_one hd).mpr hhi.le⟩
  have hca : c < a.val := (lt_div_iff₀ hd).mpr hlo
  have he : Mix a (Mix d x y) y = Mix q x y := by
    calc
      _ = Mix a (Mix d x y) (Mix 0 x y) := by rw [mix_zero]
      _ = Mix (WeightMean a d 0) x y := mix_mix ..
      _ = Mix q x y := by
        apply congrArg (fun t => Mix t x y)
        apply Subtype.ext
        change q.val / d.val * d.val + _ * 0 = _
        rw [mul_zero, add_zero, div_mul_cancel₀ _ hd.ne']
  have bad := (ht a hca).2
  rw [he] at bad
  exact bad.2 (grid_weak h.1 h.2.1 hxy hN hM hMN)

/-- Increasing the probability of a weakly better endpoint is weakly preferred. -/
theorem segment_mono (h : MixtureAxioms r) {x y : Z} (hxy : r x y)
    {s t : Weight} (hst : s.val ≤ t.val) : r (Mix t x y) (Mix s x y) := by
  let d : Weight := ⟨t.val - s.val, sub_nonneg.mpr hst,
    (sub_le_self _ s.property.1).trans t.property.2⟩
  have he : t.val = s.val + d.val := by dsimp [d]; ring
  by_cases hd : d.val < 1
  · exact (segment_step_weak h.1 h.2.1 x y hd he).mpr (segment_base_weak h hxy d)
  · have h0 : s = 0 := Subtype.ext (by change s.val = 0; linarith [t.property.2, s.property.1])
    have h1 : t = 1 := Subtype.ext (by change t.val = 1; linarith [t.property.2, s.property.1])
    rwa [h0, h1, mix_one, mix_zero]

/-- Every positive probability of a strictly better endpoint strictly improves on the baseline. -/
theorem segment_base_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (d : Weight) (hd : 0 < d.val) : Strict r (Mix d x y) y := by
  obtain ⟨n, m, hN, hM, hMN, _, hhi⟩ := exists_gridWeight_between le_rfl hd d.property.2
  exact weak_strict_trans h.1.2 (segment_mono h hxy.1 hhi.le)
    (grid_strict h.1 h.2.1 hxy hN hM hMN)

/-- **Lemma 5.7:** more probability on a strictly preferred endpoint is strictly preferred. -/
theorem lemma_5_7_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    {s t : Weight} (hst : s.val < t.val) : Strict r (Mix t x y) (Mix s x y) := by
  let d : Weight := ⟨t.val - s.val, sub_nonneg.mpr hst.le,
    (sub_le_self _ s.property.1).trans t.property.2⟩
  have he : t.val = s.val + d.val := by dsimp [d]; ring
  by_cases hd : d.val < 1
  · exact (segment_step_strict h.2.1 x y hd he).mpr
      (segment_base_strict h hxy d (sub_pos.mpr hst))
  · have h0 : s = 0 := Subtype.ext (by change s.val = 0; linarith [t.property.2, s.property.1])
    have h1 : t = 1 := Subtype.ext (by change t.val = 1; linarith [t.property.2, s.property.1])
    rwa [h0, h1, mix_one, mix_zero]

/-- The mixture lies between its weakly ordered endpoints. -/
theorem segment_bounds (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (a : Weight) :
    r x (Mix a x y) ∧ r (Mix a x y) y := by
  refine ⟨?_, segment_base_weak h hxy a⟩
  simpa only [mix_one] using segment_mono h hxy (s := a) (t := 1) a.property.2

/-- **Lemma 5.7:** every mixture of indifferent endpoints is indifferent to both. -/
theorem lemma_5_7_indifferent (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y)
    (a : Weight) : Indifferent r x (Mix a x y) ∧ Indifferent r (Mix a x y) y := by
  obtain ⟨hx, hy⟩ := segment_bounds h hxy.1 a
  exact ⟨⟨hx, h.1.2 _ y x hy hxy.2⟩, ⟨hy, h.1.2 y x _ hxy.2 hx⟩⟩

/-- **Lemma 5.6:** the midpoint lies strictly between strictly ranked endpoints. -/
theorem lemma_5_6_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y) :
    let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
    Strict r x (Mix a x y) ∧ Strict r (Mix a x y) y := by
  intro a
  refine ⟨?_, segment_base_strict h hxy a (by dsimp [a]; norm_num)⟩
  simpa only [mix_one] using lemma_5_7_strict h hxy (s := a) (t := 1) (by dsimp [a]; norm_num)

/-- **Lemma 5.6:** the midpoint of indifferent endpoints is indifferent to both. -/
theorem lemma_5_6_indifferent (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y) :
    let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
    Indifferent r x (Mix a x y) ∧ Indifferent r (Mix a x y) y :=
  lemma_5_7_indifferent h hxy _

/-- Mixing with a common background preserves any weak comparison. -/
theorem mix_monotone (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (a : Weight) (z : Z) :
    r (Mix a x z) (Mix a y z) := by
  apply ((lemma_5_5_weak_iff h.1.1).mp h.2.1 a x y y z).mp
  rw [mix_self]
  exact segment_base_weak h hxy a

/-- Mixing with a common background at positive first weight preserves strict comparison. -/
theorem mix_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (a : Weight) (ha : 0 < a.val) (z : Z) : Strict r (Mix a x z) (Mix a y z) := by
  apply (h.2.1 a x y y z).mp
  rw [mix_self]
  exact segment_base_strict h hxy a ha

/-- **Lemma 5.8:** indifferent alternatives can be substituted into any binary mixture. -/
theorem lemma_5_8 (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y)
    (a : Weight) (z : Z) : Indifferent r (Mix a x z) (Mix a y z) :=
  ⟨mix_monotone h hxy.1 a z, mix_monotone h hxy.2 a z⟩

end Kreps.UtilityForMoney.LotteryTheory
