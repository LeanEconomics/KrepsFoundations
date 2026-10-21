/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.StrongSeparabilityCancellation
import PreferenceProperties.HomotheticIdentification

/-!
# Algebra of three normalized independent utility factors

Preparation for Kreps I, Proposition 2.14. If the three baseline axes have the
same numerical scale, independence makes the induced two-factor operation
symmetric. Pair substitutions give associativity and the medial identity
whenever the pair values are attained on the common axis. These are derived
identities of the original utility, rather than additional representation axioms.
-/

namespace Kreps.PreferenceProperties

variable {A B C : Type*} {u : A × B × C → ℝ}

/-- First-factor independence transports utility equalities. -/
theorem threeFactor_first_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (a a' : A) (b b' : B) (c c' : C) :
    u (a, b, c) = u (a, b', c') ↔ u (a', b, c) = u (a', b', c') := by
  have h := threeFactor_first_indifferent hi a a' b b' c c'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

/-- Second-factor independence transports utility equalities. -/
theorem threeFactor_second_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (b b' : B) (a a' : A) (c c' : C) :
    u (a, b, c) = u (a', b, c') ↔ u (a, b', c) = u (a', b', c') := by
  have h := threeFactor_second_indifferent hi b b' a a' c c'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

/-- Third-factor independence transports utility equalities. -/
theorem threeFactor_third_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (c c' : C) (a a' : A) (b b' : B) :
    u (a, b, c) = u (a', b', c) ↔ u (a, b, c') = u (a', b', c') := by
  have h := threeFactor_third_indifferent hi c c' a a' b b'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

variable {D : Type*} {v : D × D × D → ℝ} {f : D → ℝ} {e : D}

/-- The baseline axes agree with one common numerical scale. -/
def NormalizedThreeAxes (v : D × D × D → ℝ) (f : D → ℝ) (e : D) : Prop :=
  (∀ a, v (a, e, e) = f a) ∧ (∀ a, v (e, a, e) = f a) ∧
    ∀ a, v (e, e, a) = f a

/-- A score can move from the second axis to the third at any fixed first coordinate. -/
theorem normalized_threeFactor_second_third
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (a, e, b) :=
  (threeFactor_first_utility_eq hi e a b e e b).mp ((hn.2.1 b).trans (hn.2.2 b).symm)

/-- A score can move from the first axis to the second at any fixed third coordinate. -/
theorem normalized_threeFactor_first_second
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a c : D) : v (a, e, c) = v (e, a, c) :=
  (threeFactor_third_utility_eq hi e c a e e a).mp ((hn.1 a).trans (hn.2.1 a).symm)

/-- A score can move from the first axis to the third at any fixed second coordinate. -/
theorem normalized_threeFactor_first_third
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (e, b, a) :=
  (threeFactor_second_utility_eq hi e b a e e a).mp ((hn.1 a).trans (hn.2.2 a).symm)

/-- The binary operation on the reference slice is symmetric. -/
theorem normalized_threeFactor_pair_symmetric
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (b, a, e) := by
  calc
    v (a, b, e) = v (a, e, b) := normalized_threeFactor_second_third hi hn a b
    _ = v (e, a, b) := normalized_threeFactor_first_second hi hn a b
    _ = v (b, a, e) := (normalized_threeFactor_first_third hi hn b a).symm

/-- Symmetry of two factors persists at every value of the third factor. -/
theorem normalized_threeFactor_swap_first_two
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c : D) : v (a, b, c) = v (b, a, c) :=
  (threeFactor_third_utility_eq hi e c a b b a).mp
    (normalized_threeFactor_pair_symmetric hi hn a b)

/-- The last two factors use the same binary operation as the first two. -/
theorem normalized_threeFactor_first_base
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (b c : D) : v (e, b, c) = v (b, c, e) :=
  (normalized_threeFactor_first_third hi hn c b).symm.trans
    (normalized_threeFactor_pair_symmetric hi hn c b)

/-- An attained pair value can replace its first two coordinates at any third coordinate. -/
theorem normalized_threeFactor_merge_first
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c p : D) (hp : v (a, b, e) = f p) : v (a, b, c) = v (p, e, c) :=
  (threeFactor_third_utility_eq hi e c a p b e).mp (hp.trans (hn.1 p).symm)

/-- An attained pair value can replace the last two coordinates at any first coordinate. -/
theorem normalized_threeFactor_merge_last
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c q : D) (hq : v (b, c, e) = f q) : v (a, b, c) = v (a, q, e) :=
  (threeFactor_first_utility_eq hi e a b q c e).mp
    ((normalized_threeFactor_first_base hi hn b c).trans (hq.trans (hn.2.1 q).symm))

/-- The binary operation is associative whenever its two intermediate values are attained. -/
theorem normalized_threeFactor_pair_associative
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c p q : D) (hp : v (a, b, e) = f p) (hq : v (b, c, e) = f q) :
    v (p, c, e) = v (a, q, e) := by
  calc
    v (p, c, e) = v (p, e, c) := normalized_threeFactor_second_third hi hn p c
    _ = v (a, b, c) := (normalized_threeFactor_merge_first hi hn a b c p hp).symm
    _ = v (a, q, e) := normalized_threeFactor_merge_last hi hn a b c q hq

/-- The medial identity needs only the four pair values to be attained on the common axis. -/
theorem normalized_threeFactor_pair_medial
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c d p q s t : D)
    (hp : v (a, b, e) = f p) (hq : v (c, d, e) = f q)
    (hs : v (a, c, e) = f s) (ht : v (b, d, e) = f t) :
    v (p, q, e) = v (s, t, e) := by
  have hzero : v (e, b, q) = v (e, c, t) := by
    calc
      v (e, b, q) = v (b, q, e) := normalized_threeFactor_first_base hi hn b q
      _ = v (b, c, d) := (normalized_threeFactor_merge_last hi hn b c d q hq).symm
      _ = v (c, b, d) := normalized_threeFactor_swap_first_two hi hn b c d
      _ = v (c, t, e) := normalized_threeFactor_merge_last hi hn c b d t ht
      _ = v (e, c, t) := (normalized_threeFactor_first_base hi hn c t).symm
  calc
    v (p, q, e) = v (p, e, q) := normalized_threeFactor_second_third hi hn p q
    _ = v (a, b, q) := (normalized_threeFactor_merge_first hi hn a b q p hp).symm
    _ = v (a, c, t) := (threeFactor_first_utility_eq hi e a b c q t).mp hzero
    _ = v (s, e, t) := normalized_threeFactor_merge_first hi hn a c t s hs
    _ = v (s, t, e) := (normalized_threeFactor_second_third hi hn s t).symm

end Kreps.PreferenceProperties
