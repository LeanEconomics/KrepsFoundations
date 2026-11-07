/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotterySegmentCalibration

/-!
Local prerequisite copy of ChoiceUnderUncertainty.BoundedCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Affine utility calibrated between two anchors

Kreps I, Proposition 5.4, pp. 93–95. Within any interval with strictly ranked
endpoints, the unique indifferent probability represents all comparisons and
preserves mixtures. Other alternatives in the surrounding space need not be
bounded by these endpoints.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The calibrating weight whenever a reference segment contains an indifferent point. -/
noncomputable def AnchorWeight (r : Z → Z → Prop) (hi lo z : Z) : Weight := by
  classical
  exact if h : ∃ a : Weight, Indifferent r z (Mix a hi lo) then h.choose else 0

/-- On the reference interval, the chosen probability has the stated indifference property. -/
theorem anchorWeight_indifferent (h : MixtureAxioms r) {hi lo z : Z}
    (hz : Between r hi lo z) : Indifferent r z (Mix (AnchorWeight r hi lo z) hi lo) := by
  have he := lemma_5_9 h hz
  simpa [AnchorWeight, he] using he.choose_spec

/-- Give both endpoints indifferent replacements without changing the compound's rank. -/
theorem mix_congr_indifferent (h : MixtureAxioms r) {x x' y y' : Z}
    (hx : Indifferent r x x') (hy : Indifferent r y y') (a : Weight) :
    Indifferent r (Mix a x y) (Mix a x' y') := by
  apply proposition_1_9f h.1.2 (lemma_5_8 h hx a y)
  rw [mix_swap a x' y, mix_swap a x' y']
  exact lemma_5_8 h hy _ x'

/-- A preference interval is closed under every mixture. -/
theorem between_mix (h : MixtureAxioms r) {hi lo x y : Z}
    (hx : Between r hi lo x) (hy : Between r hi lo y) (a : Weight) :
    Between r hi lo (Mix a x y) := by
  have hbnd {p q p' q' : Z} (hp : r p p') (hq : r q q') : r (Mix a p q) (Mix a p' q') := by
    apply h.1.2 _ (Mix a p' q) _ (mix_monotone h hp a q)
    rw [mix_swap a p' q, mix_swap a p' q']
    exact mix_monotone h hq _ p'
  exact ⟨by simpa only [mix_self] using hbnd hx.1 hy.1,
    by simpa only [mix_self] using hbnd hx.2 hy.2⟩

/-- Anchor probabilities represent preference throughout the interval. -/
theorem anchorWeight_represents (h : MixtureAxioms r) {hi lo x y : Z} (hs : Strict r hi lo)
    (hx : Between r hi lo x) (hy : Between r hi lo y) :
    r x y ↔ (AnchorWeight r hi lo y).val ≤ (AnchorWeight r hi lo x).val := by
  obtain ⟨hx₁, hx₂⟩ := anchorWeight_indifferent h hx
  obtain ⟨hy₁, hy₂⟩ := anchorWeight_indifferent h hy
  rw [← segment_compare_iff h hs]
  exact ⟨fun hxy => h.1.2 _ y _ (h.1.2 _ x _ hx₂ hxy) hy₁,
    fun hxy => h.1.2 x _ y hx₁ (h.1.2 _ _ y hxy hy₂)⟩

/-- Anchor probabilities are affine for any pair of alternatives in the interval. -/
theorem anchorWeight_affine (h : MixtureAxioms r) {hi lo x y : Z} (hs : Strict r hi lo)
    (hx : Between r hi lo x) (hy : Between r hi lo y) (a : Weight) :
    AnchorWeight r hi lo (Mix a x y) =
      WeightMean a (AnchorWeight r hi lo x) (AnchorWeight r hi lo y) := by
  have he := mix_congr_indifferent h (anchorWeight_indifferent h hx)
    (anchorWeight_indifferent h hy) a
  rw [mix_mix] at he
  exact lemma_5_9_unique h hs (anchorWeight_indifferent h (between_mix h hx hy a)) he

/-- The bounded-anchor case of the mixture-space theorem, with explicit probability utility. -/
theorem representation_with_best_worst (h : MixtureAxioms r) {hi lo : Z} (hs : Strict r hi lo)
    (hb : ∀ z, Between r hi lo z) :
    Represents (fun z => (AnchorWeight r hi lo z).val) r ∧
      AffineInMix (fun z => (AnchorWeight r hi lo z).val) := by
  refine ⟨fun x y => anchorWeight_represents h hs (hb x) (hb y), fun a x y => ?_⟩
  exact congrArg Subtype.val (anchorWeight_affine h hs (hb x) (hb y) a)

end Kreps.UtilityForMoney.LotteryTheory
