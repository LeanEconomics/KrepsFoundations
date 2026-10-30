/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem

/-!
# Unused goods and uniqueness with partial strict convexity

Kreps I, Problem 3.2, p. 64. A locally insatiable consumer never buys goods
that do not affect preferences. Strict convexity only among the remaining goods
therefore suffices for uniqueness. The generic finite subset formulation includes
the source's first `j` goods without imposing strict convexity on irrelevant goods.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Agreeing on the useful goods makes bundles indifferent. -/
def IrrelevantOutside {k : ℕ} (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop)
    (A : Finset (Fin k)) : Prop :=
  ∀ x z, (∀ i ∈ A, x.val i = z.val i) → Indifferent r x z

/-- Strict convexity when all goods outside `A` are held fixed. -/
def StrictlyConvexInGoods {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) (A : Finset (Fin k)) : Prop :=
  ∀ x z, x ≠ z → (∀ i ∉ A, x.val i = z.val i) → r x z →
    ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
      Strict r (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ⟨ha.1.le, ha.2.le⟩) z

/-- Removing consumption of one commodity preserves nonnegativity. -/
def RemoveGood {k : ℕ} (x : NonnegativeOrthant k) (j : Fin k) : NonnegativeOrthant k :=
  ⟨Function.update x.val j 0, fun i => by
    by_cases h : i = j
    · subst i
      simp
    · simpa [h] using x.property i⟩

/-- Removing a commodity lowers expenditure by exactly its original cost. -/
theorem expenditure_removeGood {k : ℕ} (p : PositivePrices k)
    (x : NonnegativeOrthant k) (j : Fin k) :
    Expenditure p (RemoveGood x j) + p.val j * x.val j = Expenditure p x := by
  have hterm (i : Fin k) :
      p.val i * (RemoveGood x j).val i + (if i = j then p.val j * x.val j else 0) =
        p.val i * x.val i := by
    by_cases h : i = j
    · subst i
      simp [RemoveGood]
    · simp [RemoveGood, h]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Expenditure] using hsum

/-- Local insatiability forces every irrelevant commodity to have zero demand. -/
theorem irrelevant_good_zero_at_choice {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hl : LocallyInsatiable r) (A : Finset (Fin k)) (hi : IrrelevantOutside r A)
    (p : PositivePrices k) (y : ℝ≥0) {x : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (BudgetSet p y)) {j : Fin k} (hj : j ∉ A) : x.val j = 0 := by
  have heq := expenditure_removeGood p x j
  have hnonneg : 0 ≤ p.val j * x.val j := mul_nonneg (p.property j).le (x.property j)
  have hremove : RemoveGood x j ∈ BudgetSet p y := by
    change Expenditure p (RemoveGood x j) ≤ (y : ℝ)
    have hcost : Expenditure p x ≤ (y : ℝ) := hx.1
    linarith
  have hindiff : Indifferent r (RemoveGood x j) x := hi _ _ (fun i hi => by
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [RemoveGood, hne])
  have hchoice : RemoveGood x j ∈ PrefChoice r (BudgetSet p y) :=
    ⟨hremove, fun z hz => hr.2 _ _ _ hindiff.1 (hx.2 z hz)⟩
  have hcost := preferenceChoice_exhausts_budget hl p y hx
  have hremoved := preferenceChoice_exhausts_budget hl p y hchoice
  have hzero : p.val j * x.val j = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (p.property j))

/-- **Problem 3.2:** partial strict convexity implies at most one optimal bundle. -/
theorem problem_3_2_subsingleton {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hl : LocallyInsatiable r) (A : Finset (Fin k)) (hi : IrrelevantOutside r A)
    (hs : StrictlyConvexInGoods r A) (p : PositivePrices k) (y : ℝ≥0) :
    (PrefChoice r (BudgetSet p y)).Subsingleton := by
  intro x hx z hz
  by_contra hne
  have hagree : ∀ i ∉ A, x.val i = z.val i := by
    intro i hia
    rw [irrelevant_good_zero_at_choice hr hl A hi p y hx hia,
      irrelevant_good_zero_at_choice hr hl A hi p y hz hia]
  have hstrict := hs x z hne hagree (hx.2 z hz.1) (1 / 2)
    (by constructor <;> norm_num)
  have hfeasible := budgetSet_convex p y x hx.1 z hz.1 (1 / 2)
    (by constructor <;> norm_num)
  exact hstrict.2 (hz.2 _ hfeasible)

/-- **Problem 3.2:** continuity supplies existence, completing uniqueness. -/
theorem problem_3_2_unique {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hc : Continuous u) (hl : LocallyInsatiable (UtilityPref u)) (A : Finset (Fin k))
    (hi : IrrelevantOutside (UtilityPref u) A) (hs : StrictlyConvexInGoods (UtilityPref u) A)
    (p : PositivePrices k) (y : ℝ≥0) : ∃! x, x ∈ MarshallianDemand u p y := by
  obtain ⟨x, hx⟩ := proposition_3_1b hc p y
  exact ⟨x, hx, fun z hz => problem_3_2_subsingleton
    (utilityPref_rational u) hl A hi hs p y hz hx⟩

end Kreps.ConsumerDemand
