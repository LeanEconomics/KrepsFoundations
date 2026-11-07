/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem

/-!
# Strictly decreasing preferences

Kreps I, Problem 3.1, p. 64. Decrease means that reducing some commodities
without increasing any is strictly preferred. The origin is the unique demand,
and the origin directly witnesses failure of local insatiability. Neither result
uses a continuity assumption or assumes exhaustion of the budget.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- Reducing at least one commodity, and increasing none, is strictly preferred. -/
def StrictlyDecreasingPreference {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x y, x.val ≤ y.val → x ≠ y → Strict r x y

/-- **Problem 3.1:** a strictly decreasing rational consumer uniquely chooses the origin. -/
theorem problem_3_1_demand {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hd : StrictlyDecreasingPreference r)
    (p : PositivePrices k) (y : ℝ≥0) :
    PrefChoice r (BudgetSet p y) = {ZeroBundle k} := by
  have hzero : ZeroBundle k ∈ BudgetSet p y := by
    change Expenditure p (ZeroBundle k) ≤ (y : ℝ)
    rw [expenditure_zero]
    exact y.property
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (hd (ZeroBundle k) x x.property (Ne.symm hne)).2 (hx.2 _ hzero)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨hzero, fun z _ => ?_⟩
    by_cases hz : ZeroBundle k = z
    · subst z
      exact (hr.1 _ _).elim id id
    · exact (hd _ z z.property hz).1

/-- **Problem 3.1:** no bundle is strictly better than the origin, even in an arbitrary ball. -/
theorem problem_3_1_not_locallyInsatiable {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hd : StrictlyDecreasingPreference r) : ¬LocallyInsatiable r := by
  intro hlocal
  obtain ⟨z, _, hz⟩ := hlocal (ZeroBundle k) 1 zero_lt_one
  by_cases hzero : ZeroBundle k = z
  · subst z
    exact hz.2 hz.1
  · exact (hd _ z z.property hzero).2 hz.1

end Kreps.ConsumerDemand
