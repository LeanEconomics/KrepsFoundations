/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryMixtureAlgebra

/-!
Local prerequisite copy of ChoiceUnderUncertainty.Independence from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Background substitution and equally spaced comparisons

Kreps I, Lemmas 5.5–5.7, pp. 91–92. At fixed mixture weight a common
background can be replaced in either a strict or a weak comparison. Along a
single segment, comparisons separated by the same probability increment are
therefore identical. This holds before any continuity assumption is imposed.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Background substitution for weak comparison. -/
def WeakBackgroundIndependent (r : Z → Z → Prop) : Prop :=
  ∀ (a : Weight) x y z w, r (Mix a x z) (Mix a y z) ↔ r (Mix a x w) (Mix a y w)

/-- **Lemma 5.5:** a strict comparison for some common background holds for every background. -/
theorem lemma_5_5_some_iff : BackgroundIndependent r ↔
    ∀ (a : Weight) x y, (∃ z, Strict r (Mix a x z) (Mix a y z)) →
      ∀ w, Strict r (Mix a x w) (Mix a y w) := by
  constructor
  · rintro h a x y ⟨z, hz⟩ w
    exact (h a x y z w).mp hz
  · intro h a x y z w
    exact ⟨fun hz => h a x y ⟨z, hz⟩ w, fun hw => h a x y ⟨w, hw⟩ z⟩

/-- **Lemma 5.5:** weak and strict background-independence are equivalent for complete tastes. -/
theorem lemma_5_5_weak_iff (hc : Complete r) :
    BackgroundIndependent r ↔ WeakBackgroundIndependent r := by
  constructor
  · intro h a x y z w
    have he := h a y x z w
    rw [proposition_1_9a hc, proposition_1_9a hc] at he
    exact not_iff_not.mp he
  · intro h a x y z w
    rw [proposition_1_9a hc, proposition_1_9a hc]
    exact not_congr (h a y x z w)

/-- **Lemma 5.5:** a common background can also be replaced in an indifference comparison. -/
theorem lemma_5_5_indifferent (hc : Complete r) (hi : BackgroundIndependent r)
    (a : Weight) (x y z w : Z) :
    Indifferent r (Mix a x z) (Mix a y z) ↔ Indifferent r (Mix a x w) (Mix a y w) :=
  and_congr ((lemma_5_5_weak_iff hc).mp hi a x y z w)
    ((lemma_5_5_weak_iff hc).mp hi a y x z w)

/-- Moving the common background along a segment translates a probability increment. -/
theorem segment_shift {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val)
    (x y : Z) : ∃ z, Mix d x z = Mix t x y ∧ Mix d y z = Mix s x y := by
  have hp : 0 < 1 - d.val := sub_pos.mpr hd
  let b : Weight := ⟨s.val / (1 - d.val), div_nonneg s.property.1 hp.le,
    (div_le_one hp).mpr (by linarith [t.property.2])⟩
  refine ⟨Mix b x y, ?_, ?_⟩
  · calc
      Mix d x (Mix b x y) = Mix d (Mix 1 x y) (Mix b x y) := by rw [mix_one]
      _ = Mix (WeightMean d 1 b) x y := mix_mix ..
      _ = Mix t x y := by
        apply congrArg (fun a => Mix a x y)
        apply Subtype.ext
        change d.val * 1 + (1 - d.val) * (s.val / (1 - d.val)) = t.val
        rw [mul_comm (1 - d.val), div_mul_cancel₀ _ hp.ne']
        linarith
  · calc
      Mix d y (Mix b x y) = Mix d (Mix 0 x y) (Mix b x y) := by rw [mix_zero]
      _ = Mix (WeightMean d 0 b) x y := mix_mix ..
      _ = Mix s x y := by
        apply congrArg (fun a => Mix a x y)
        apply Subtype.ext
        change d.val * 0 + (1 - d.val) * (s.val / (1 - d.val)) = s.val
        rw [mul_zero, zero_add, mul_comm, div_mul_cancel₀ _ hp.ne']

/-- Equal upward increments have the same weak comparison at every admissible starting point. -/
theorem segment_step_weak (hr : Rational r) (hi : BackgroundIndependent r) (x y : Z)
    {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val) :
    r (Mix t x y) (Mix s x y) ↔ r (Mix d x y) y := by
  obtain ⟨z, hz, hz'⟩ := segment_shift hd he x y
  simpa only [hz, hz', mix_self] using (lemma_5_5_weak_iff hr.1).mp hi d x y z y

/-- Equal upward increments have the same strict comparison at every admissible starting point. -/
theorem segment_step_strict (hi : BackgroundIndependent r) (x y : Z)
    {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val) :
    Strict r (Mix t x y) (Mix s x y) ↔ Strict r (Mix d x y) y := by
  obtain ⟨z, hz, hz'⟩ := segment_shift hd he x y
  simpa only [hz, hz', mix_self] using hi d x y z y

end Kreps.UtilityForMoney.LotteryTheory
