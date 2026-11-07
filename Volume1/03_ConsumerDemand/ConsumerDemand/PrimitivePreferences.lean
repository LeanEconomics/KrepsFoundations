/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem
import ConsumerDemand.RepresentationGeneralContinuousRepresentation

/-!
# Consumer demand from primitive preferences

Kreps I, Section 3.1, p. 51. Rationality and continuity produce a continuous
utility representation by the independently copied proof of Proposition 2.9.
Thus utility representation is a conclusion, rather than an additional assumption
in the primitive consumer model. The `Representation` namespace isolates attributed
prerequisites from the chapter's public definitions.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- Preference continuity means openness of strict comparisons in the product domain. -/
def ContinuousPreference {X : Type*} [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  IsOpen {q : X × X | Strict r q.1 q.2}

/-- Section 3.1's utility exists from primitive rational and continuous preferences. -/
theorem continuous_utility_of_primitive_preferences {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  (Representation.proposition_2_9 k hr).mp hc

/-- Representation identifies the entire preference-maximizing and demand correspondences. -/
theorem preferenceChoice_eq_demand {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    {u : NonnegativeOrthant k → ℝ} (hu : Represents u r)
    (p : PositivePrices k) (y : ℝ≥0) :
    PrefChoice r (BudgetSet p y) = MarshallianDemand u p y := by
  ext x
  simp only [PrefChoice, MarshallianDemand, UtilityPref, Set.mem_ofPred_eq]
  exact and_congr_right (fun _ => forall_congr' fun z => imp_congr_right (fun _ => hu x z))

/-- Primitive rational continuous preferences have an optimal bundle at every budget. -/
theorem primitive_consumer_choice_nonempty {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) (p : PositivePrices k) (y : ℝ≥0) :
    (PrefChoice r (BudgetSet p y)).Nonempty := by
  obtain ⟨u, hu, huc⟩ := continuous_utility_of_primitive_preferences hr hc
  rw [preferenceChoice_eq_demand hu]
  exact proposition_3_1b huc p y

end Kreps.ConsumerDemand
