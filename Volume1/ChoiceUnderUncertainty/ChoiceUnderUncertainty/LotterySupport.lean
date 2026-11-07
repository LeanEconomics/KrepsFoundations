/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.SimpleLottery

/-!
# The support of a compound lottery

Kreps I, Definition 5.2 and p. 87, footnote 5. Every positive-mass prize in
either component survives an interior mixture. At endpoint weights only the
selected component remains.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- Membership in the finite support means strictly positive probability. -/
theorem lottery_mem_support_iff {X : Type*} (p : SimpleLottery X) (x : X) :
    x ∈ p.weights.support ↔ 0 < p.weights x :=
  Finsupp.mem_support_iff.trans ⟨fun h => lt_of_le_of_ne (p.nonneg x) (Ne.symm h), ne_of_gt⟩

/-- The exact support of an interior mixture is the union of the component supports. -/
theorem lottery_mix_support {X : Type*} [DecidableEq X] (p q : SimpleLottery X)
    (a : Weight) (ha : 0 < a.val) (ha' : a.val < 1) :
    (Mix a p q).weights.support = p.weights.support ∪ q.weights.support := by
  ext x
  rw [Finset.mem_union, lottery_mem_support_iff, lottery_mem_support_iff,
    lottery_mem_support_iff, lottery_mix_weight]
  constructor
  · intro h
    by_contra! hn
    rw [le_antisymm hn.1 (p.nonneg x), le_antisymm hn.2 (q.nonneg x)] at h
    linarith
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (mul_pos ha h) (mul_nonneg (sub_nonneg.mpr a.property.2)
        (q.nonneg x))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (p.nonneg x)) (mul_pos (sub_pos.mpr ha') h)

/-- The two endpoint supports need no positivity assumption and agree with the selected law. -/
theorem lottery_endpoint_supports {X : Type*} (p q : SimpleLottery X) :
    (Mix 0 p q).weights.support = q.weights.support ∧
      (Mix 1 p q).weights.support = p.weights.support := by rw [mix_zero, mix_one]; exact ⟨rfl, rfl⟩

end Kreps.ChoiceUnderUncertainty
