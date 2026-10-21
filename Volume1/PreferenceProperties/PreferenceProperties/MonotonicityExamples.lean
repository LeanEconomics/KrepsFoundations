/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Monotonicity

/-!
# Monotonicity without continuity

Kreps I, Problem 2.6, p. 46. Lexicographic comparison with reversed second-coordinate
ties is strictly monotone when every coordinate increases, and locally insatiable,
but is neither weakly monotone nor continuous. This completes the distinction between
the unconditional implications and the equivalence requiring continuous preferences.
-/

namespace Kreps.PreferenceProperties

/-- A convenient two-good bundle with explicitly nonnegative coordinates. -/
def PairBundle (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : NonnegativeOrthant 2 :=
  ⟨fun j => if j = 0 then a else b, fun j => by dsimp; split_ifs <;> assumption⟩

/-- Prefer more of the first good; when it ties, prefer less of the second good. -/
def ReverseTiePreference (x y : NonnegativeOrthant 2) : Prop :=
  y.val 0 < x.val 0 ∨ (x.val 0 = y.val 0 ∧ x.val 1 ≤ y.val 1)

/-- The reversed-tie lexicographic relation is still a complete transitive preference. -/
theorem reverseTie_rational : Rational ReverseTiePreference := by
  constructor
  · intro x y
    by_cases he : x.val 0 = y.val 0
    · rcases le_total (x.val 1) (y.val 1) with h | h
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr (Or.inr ⟨he.symm, h⟩)
    · rcases lt_or_gt_of_ne he with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
  · intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxy, hxy'⟩
    · rcases hyz with hyz | ⟨hyz, _⟩
      · exact Or.inl (hyz.trans hxy)
      · exact Or.inl (by linarith)
    · rcases hyz with hyz | ⟨hyz, hyz'⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨hxy.trans hyz, hxy'.trans hyz'⟩

/-- Increasing every coordinate improves the first coordinate and so strictly improves rank. -/
theorem reverseTie_strictAllIncrease : StrictAllIncreasePreference ReverseTiePreference := by
  intro x y hxy
  refine ⟨Or.inl (hxy 0), ?_⟩
  rintro (h | ⟨he, _⟩)
  · exact (not_lt_of_gt (hxy 0)) h
  · have h := hxy 0
    linarith

/-- Increasing only the second coordinate can make a bundle strictly worse. -/
theorem reverseTie_not_monotone : ¬MonotonePreference ReverseTiePreference := by
  intro h
  have hm := h (PairBundle 0 1 (by norm_num) (by norm_num))
    (PairBundle 0 0 (by norm_num) (by norm_num)) (by
      intro j
      fin_cases j <;> norm_num [PairBundle])
  norm_num [ReverseTiePreference, PairBundle] at hm

/-- Despite that failure, there are arbitrarily nearby strict improvements. -/
theorem reverseTie_locallyInsatiable : LocallyInsatiable ReverseTiePreference :=
  strictAllIncrease_locallyInsatiable reverseTie_strictAllIncrease

/-- Continuity is exactly what this counterexample lacks in the equivalence of Problem 2.6. -/
theorem reverseTie_not_continuous : ¬ContinuousPreference ReverseTiePreference :=
  fun hc => reverseTie_not_monotone
    (continuous_strictAllIncrease_monotone reverseTie_rational hc reverseTie_strictAllIncrease)

/-- **Problem 2.6**, the counterexample when continuity is removed. -/
theorem problem_2_6_without_continuity :
    Rational ReverseTiePreference ∧ StrictAllIncreasePreference ReverseTiePreference ∧
    LocallyInsatiable ReverseTiePreference ∧ ¬MonotonePreference ReverseTiePreference ∧
    ¬ContinuousPreference ReverseTiePreference :=
  ⟨reverseTie_rational, reverseTie_strictAllIncrease, reverseTie_locallyInsatiable,
    reverseTie_not_monotone, reverseTie_not_continuous⟩

end Kreps.PreferenceProperties
