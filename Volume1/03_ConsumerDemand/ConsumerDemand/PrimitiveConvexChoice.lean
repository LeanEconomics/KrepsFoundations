/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.PrimitivePreferences

/-!
# Convex consumer choice from primitive preferences

Kreps I, Proposition 3.1(c), pp. 53-54. Convexity and strict convexity of preferences
give convexity and uniqueness of budget choice directly. Existence in the uniqueness
theorem comes from rational continuous preferences via the continuous-representation
theorem, rather than from an assumed utility or an assumed maximizer.

The two general menu lemmas are attributed local adaptations of Chapter 2's
`ConvexPreference.proposition_2_6_convex` and `proposition_2_6_unique`, originating
at commit `7d496c5f546d4301da35c1995af5a77694874155`. They preserve the definitions
and proof arguments. Empty maximizing sets are allowed in these two lemmas.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- Chapter 2's convex-best-set argument for any convex menu in a convex domain. -/
theorem prefChoice_convex {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r)
    (hc : ConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    ConvexMenu hS (PrefChoice r A) := by
  intro x hx y hy a ha
  refine ⟨hA x hx.1 y hy.1 a ha, fun z hz => ?_⟩
  exact hr.2 _ y z (hc x y (hx.2 y hy.1) a ha) (hy.2 z hz)

/-- Chapter 2's strict-convexity argument gives at most one best bundle on any convex menu. -/
theorem prefChoice_subsingleton {hS : Convex ℝ S} {r : S → S → Prop}
    (hs : StrictlyConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    (PrefChoice r A).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := hs x y hne (hx.2 y hy.1) (1 / 2) (by constructor <;> norm_num)
  exact hm.2 (hy.2 _ (hA x hx.1 y hy.1 (1 / 2) (by constructor <;> norm_num)))

/-- **Proposition 3.1(c):** convex preferences give a convex set of consumer choices. -/
theorem primitive_consumer_choice_convex {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) r)
    (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (PrefChoice r (BudgetSet p y)) :=
  prefChoice_convex hr hc (budgetSet_convex p y)

/-- **Proposition 3.1(c):** strict preference convexity gives at most one consumer choice. -/
theorem primitive_consumer_choice_subsingleton {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hs : StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) r)
    (p : PositivePrices k) (y : ℝ≥0) : (PrefChoice r (BudgetSet p y)).Subsingleton :=
  prefChoice_subsingleton hs (budgetSet_convex p y)

/-- **Proposition 3.1(c):** primitive rational continuous strictly convex tastes give uniqueness. -/
theorem primitive_consumer_choice_unique {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r)
    (hs : StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) r)
    (p : PositivePrices k) (y : ℝ≥0) : ∃! x, x ∈ PrefChoice r (BudgetSet p y) := by
  obtain ⟨x, hx⟩ := primitive_consumer_choice_nonempty hr hc p y
  exact ⟨x, hx, fun z hz => primitive_consumer_choice_subsingleton hs p y hz hx⟩

end Kreps.ConsumerDemand
