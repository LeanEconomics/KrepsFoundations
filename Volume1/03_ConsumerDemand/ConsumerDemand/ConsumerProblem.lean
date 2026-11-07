/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BudgetSets

/-!
# The consumer's problem and its basic properties

Kreps I, Proposition 3.1 and Definition 3.2, pp. 52-54. Demand is the full set
of utility-maximizing budget-feasible bundles. Continuous utility guarantees
existence; quasi-concavity gives a convex solution set and strict quasi-concavity
gives uniqueness. Local insatiability implies exhaustion of the budget.
All results permit zero income; none assumes a maximizer as an existence premise.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- **Definition 3.2:** Marshallian demand is the full solution set of the consumer's problem. -/
def MarshallianDemand {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  PrefChoice (UtilityPref u) (BudgetSet p y)

/-- Demand membership consists precisely of budget feasibility and utility optimality. -/
theorem mem_marshallianDemand_iff {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand u p y ↔
      x ∈ BudgetSet p y ∧ ∀ z ∈ BudgetSet p y, u z ≤ u x := Iff.rfl

/-- The alternative Mathlib formulation identifies demand with feasible global maximizers. -/
theorem mem_marshallianDemand_iff_isMaxOn {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand u p y ↔ x ∈ BudgetSet p y ∧ IsMaxOn u (BudgetSet p y) x := Iff.rfl

/-- **Proposition 3.1(a):** positive joint scaling of prices and income preserves all solutions. -/
theorem proposition_3_1a {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = MarshallianDemand u p y := by
  simp only [MarshallianDemand, budgetSet_scale]

/-- **Proposition 3.1(b):** a continuous utility attains its maximum on every budget set. -/
theorem proposition_3_1b {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u)
    (p : PositivePrices k) (y : ℝ≥0) : (MarshallianDemand u p y).Nonempty := by
  obtain ⟨x, hx, hm⟩ := (budgetSet_isCompact p y).exists_isMaxOn
    (budgetSet_nonempty p y) hu.continuousOn
  exact ⟨x, hx, hm⟩

/-- At zero income, every utility has the unique feasible bundle as its unique demand. -/
theorem marshallianDemand_zero {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) : MarshallianDemand u p 0 = {ZeroBundle k} := by
  ext x
  simp only [MarshallianDemand, PrefChoice, UtilityPref, budgetSet_zero, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨And.left, fun h => ⟨h, by rw [h]⟩⟩

/-- **Proposition 3.1(c):** quasi-concavity makes the entire demand set convex. -/
theorem proposition_3_1c_convex {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (MarshallianDemand u p y) := by
  intro x hx z hz a ha
  refine ⟨budgetSet_convex p y x hx.1 z hz.1 a ha, fun w hw => ?_⟩
  exact (le_min (hx.2 w hw) (hz.2 w hw)).trans (hu x z a ha)

/-- Strict quasi-concavity permits at most one budget-feasible maximizer. -/
theorem marshallianDemand_subsingleton {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : StrictlyQuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) : (MarshallianDemand u p y).Subsingleton := by
  intro x hx z hz
  by_contra hne
  have hbetter := hu x z hne (hx.2 z hz.1) (1 / 2) (by constructor <;> norm_num)
  have hfeasible := budgetSet_convex p y x hx.1 z hz.1 (1 / 2)
    (by constructor <;> norm_num)
  exact not_lt_of_ge (hz.2 _ hfeasible) hbetter

/-- **Proposition 3.1(c):** continuous strictly quasi-concave utility has exactly one solution. -/
theorem proposition_3_1c_unique {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hc : Continuous u)
    (hu : StrictlyQuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) : ∃! x, x ∈ MarshallianDemand u p y := by
  obtain ⟨x, hx⟩ := proposition_3_1b hc p y
  exact ⟨x, hx, fun z hz => marshallianDemand_subsingleton hu p y hz hx⟩

/-- Local insatiability excludes a preference-best point with strictly slack expenditure. -/
theorem preferenceChoice_exhausts_budget {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : LocallyInsatiable r)
    (p : PositivePrices k) (y : ℝ≥0) {x : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (BudgetSet p y)) : Expenditure p x = (y : ℝ) := by
  apply le_antisymm hx.1
  by_contra hnot
  have hslack : Expenditure p x < (y : ℝ) := lt_of_not_ge hnot
  have hopen : IsOpen {z : NonnegativeOrthant k | Expenditure p z < (y : ℝ)} :=
    isOpen_lt (expenditure_continuous p) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hslack
  obtain ⟨z, hzx, hbetter⟩ := hr x (ε / 2) (by positivity)
  have hzlt : Expenditure p z < (y : ℝ) :=
    hball (show z ∈ Metric.ball x ε from by change dist z x < ε; linarith)
  have hz : z ∈ BudgetSet p y := hzlt.le
  exact hbetter.2 (hx.2 z hz)

/-- **Proposition 3.1(d):** locally insatiable consumers spend their entire income at a solution. -/
theorem proposition_3_1d {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : LocallyInsatiable (UtilityPref u)) (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ MarshallianDemand u p y) :
    Expenditure p x = (y : ℝ) := preferenceChoice_exhausts_budget hu p y hx

end Kreps.ConsumerDemand
