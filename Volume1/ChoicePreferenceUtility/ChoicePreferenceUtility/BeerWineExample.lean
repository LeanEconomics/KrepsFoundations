/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.ParetoMajority
import ChoicePreferenceUtility.PartialPreference

/-!
# The beer-and-wine illustration of indecision

Kreps I, Section 1.8, pp. 20-21. The bundles are three beers and ten wines, twenty
beers and six wines, and four beers and eleven wines. The third is strictly better
than the first, while both are incomparable with the second. This ranking pattern
alone contradicts negative transitivity of strict preference.

The book specifies these comparisons, not a relation on all bundles. Coordinatewise
Pareto preference is one explicit model realizing them. Its strict part and equality
also satisfy the partial-preference axioms considered in Problem 1.17.
-/

namespace Kreps.ChoicePreferenceUtility

/-- The first bundle on p. 20: three cans of beer and ten bottles of wine. -/
def BeerWineFirst : NonnegativeOrthant 2 :=
  ⟨fun j => if j = 0 then 3 else 10, by intro j; dsimp; split_ifs <;> norm_num⟩

/-- The second bundle on p. 20: twenty cans of beer and six bottles of wine. -/
def BeerWineSecond : NonnegativeOrthant 2 :=
  ⟨fun j => if j = 0 then 20 else 6, by intro j; dsimp; split_ifs <;> norm_num⟩

/-- The improved bundle on p. 21: four cans of beer and eleven bottles of wine. -/
def BeerWineImproved : NonnegativeOrthant 2 :=
  ⟨fun j => if j = 0 then 4 else 11, by intro j; dsimp; split_ifs <;> norm_num⟩

/-- The literal strict ranking pattern already refutes negative transitivity. -/
theorem beerWine_pattern_not_negativelyTransitive
    {s : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop}
    (hbetter : s BeerWineImproved BeerWineFirst)
    (hleft : ¬s BeerWineSecond BeerWineFirst)
    (hright : ¬s BeerWineImproved BeerWineSecond) : ¬NegativelyTransitive s := by
  intro hn
  exact (hn BeerWineImproved BeerWineFirst BeerWineSecond hbetter).elim hleft hright

/-- In the Pareto witness model, the first two bundles cannot be weakly compared. -/
theorem beerWine_first_second_incomparable :
    ¬ParetoPreference BeerWineFirst BeerWineSecond ∧
      ¬ParetoPreference BeerWineSecond BeerWineFirst := by
  constructor
  · intro h
    have hzero := h 0
    norm_num [BeerWineFirst, BeerWineSecond] at hzero
  · intro h
    have hone := h 1
    norm_num [BeerWineFirst, BeerWineSecond] at hone

/-- In the same model, the improved bundle is still incomparable with the second. -/
theorem beerWine_improved_second_incomparable :
    ¬ParetoPreference BeerWineImproved BeerWineSecond ∧
      ¬ParetoPreference BeerWineSecond BeerWineImproved := by
  constructor
  · intro h
    have hzero := h 0
    norm_num [BeerWineImproved, BeerWineSecond] at hzero
  · intro h
    have hone := h 1
    norm_num [BeerWineImproved, BeerWineSecond] at hone

/-- Four beers and eleven wines strictly Pareto dominate three beers and ten wines. -/
theorem beerWine_strict_improvement :
    Strict ParetoPreference BeerWineImproved BeerWineFirst := by
  constructor
  · intro j
    dsimp [BeerWineFirst, BeerWineImproved]
    split_ifs <;> norm_num
  · intro h
    have hzero := h 0
    norm_num [BeerWineFirst, BeerWineImproved] at hzero

/-- The book's three bundles witness failure of negative transitivity in this model. -/
theorem beerWine_not_negativelyTransitive :
    ¬NegativelyTransitive (Strict (ParetoPreference (k := 2))) :=
  beerWine_pattern_not_negativelyTransitive beerWine_strict_improvement
    (fun h => beerWine_first_second_incomparable.2 h.1)
    (fun h => beerWine_improved_second_incomparable.1 h.1)

/-- Strict Pareto preference and positive equality obey all partial-preference axioms. -/
theorem beerWine_partialPreferenceAxioms :
    PartialPreferenceAxioms (Strict (ParetoPreference (k := 2))) (· = ·) := by
  constructor
  · exact problem_1_6_asymmetric 2
  · exact proposition_1_9h (problem_1_6_transitive 2)
  · exact fun _ => rfl
  · exact fun _ _ h => h.symm
  · exact fun _ _ _ hxy hyz => hxy.trans hyz
  · rintro x y z hxy rfl
    exact hxy
  · rintro x y z rfl hyz
    exact hyz

/-- The witness satisfies the partial theory while failing the standard strict axiom. -/
theorem beerWine_indecision_model :
    PartialPreferenceAxioms (Strict (ParetoPreference (k := 2))) (· = ·) ∧
      ¬NegativelyTransitive (Strict (ParetoPreference (k := 2))) :=
  ⟨beerWine_partialPreferenceAxioms, beerWine_not_negativelyTransitive⟩

end Kreps.ChoicePreferenceUtility
