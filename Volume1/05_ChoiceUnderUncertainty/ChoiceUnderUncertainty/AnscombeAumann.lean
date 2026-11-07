/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureRepresentation
import ChoiceUnderUncertainty.SubjectiveLotteries

/-!
# The two Anscombe–Aumann representations

Kreps I, Propositions 5.12 and 5.13, pp. 102–108. The mixture axioms give a
state-additive expected utility. Adding comparisons of constant and single-state
acts gives a common prize utility and strictly positive subjective probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S] {r : HorseLottery S X → HorseLottery S X → Prop}

/-- Proposition 5.12. The primitive axioms are equivalent to state-additive expected utility. -/
theorem proposition_5_12 : MixtureAxioms r ↔ ∃ U : S → X → ℝ, Represents (HorseValue U) r := by
  constructor
  · intro h
    obtain ⟨u, hr, ha⟩ := proposition_5_4.mp h
    exact horseRepresentation_of_affine hr ha
  · rintro ⟨U, hr⟩
    exact proposition_5_4.mpr ⟨_, hr, horseValue_affine U⟩

/-- Proposition 5.13. State independence gives full-support subjective expected utility. -/
theorem proposition_5_13 [Nonempty S] : MixtureAxioms r ∧ StateIndependentComparisons r ↔
    ∃ (p : S → ℝ) (U : X → ℝ), (∀ s, 0 < p s) ∧ ∑ s, p s = 1 ∧
      Represents (SubjectiveHorseValue p U) r := by
  constructor
  · rintro ⟨h, hi⟩
    obtain ⟨V, hV⟩ := proposition_5_12.mp h
    exact subjectiveRepresentation_of_stateIndependent hV hi
  · rintro ⟨p, U, hp, hsum, hr⟩
    exact ⟨proposition_5_4.mpr ⟨_, hr, subjectiveHorseValue_affine p U⟩,
      subjectiveActValue_stateIndependent p hp hsum (ExpectedUtility U) hr⟩

end Kreps.ChoiceUnderUncertainty
