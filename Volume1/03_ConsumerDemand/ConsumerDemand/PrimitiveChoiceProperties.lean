/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.PrimitivePreferences
import ConsumerDemand.IrrelevantGoods

/-!
# Primitive-preference uniqueness with irrelevant goods

Kreps I, Problem 3.2, p. 64. This wrapper combines primitive-preference
existence with the direct preference argument for uniqueness. The representation
required for existence is derived from rationality and continuity, not supplied
as an extra hypothesis. A finite useful-good subset includes the literal first
`j` goods used in the source.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- **Problem 3.2:** complete existence and uniqueness from primitive preference assumptions. -/
theorem problem_3_2_primitive {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hl : LocallyInsatiable r) (A : Finset (Fin k))
    (hi : IrrelevantOutside r A) (hs : StrictlyConvexInGoods r A)
    (p : PositivePrices k) (y : ℝ≥0) : ∃! x, x ∈ PrefChoice r (BudgetSet p y) := by
  obtain ⟨x, hx⟩ := primitive_consumer_choice_nonempty hr hc p y
  exact ⟨x, hx, fun z hz => problem_3_2_subsingleton hr hl A hi hs p y hz hx⟩

/-- The first `j` commodities, using zero-based indices internally. -/
def FirstGoods (k j : ℕ) : Finset (Fin k) := Finset.univ.filter (fun i => i.val < j)

/-- Membership in the first-good block matches the literal strict index cutoff. -/
theorem mem_firstGoods {k j : ℕ} (i : Fin k) : i ∈ FirstGoods k j ↔ i.val < j := by
  simp [FirstGoods]

end Kreps.ConsumerDemand
