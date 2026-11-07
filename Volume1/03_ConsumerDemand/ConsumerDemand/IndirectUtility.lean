/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ConsumerProblem
import ConsumerDemand.BudgetContinuity

/-!
# Marshallian demand and indirect utility

Kreps I, Definition 3.2 and Proposition 3.3, pp. 54-56. The budget correspondence
satisfies all hypotheses of the maximum theorem, so demand is nonempty, locally
bounded and upper semicontinuous, and indirect utility is continuous. The domain
includes zero income. On every subset where demand is singleton-valued its
selection is relatively continuous, which includes the book's open subsets.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal Topology

/-- **Definition 3.2:** the value of the consumer's problem, attained for continuous utility. -/
noncomputable def IndirectUtility {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : ℝ := sSup (u '' BudgetSet p y)

/-- Every demanded bundle gives exactly the indirect utility value. -/
theorem indirectUtility_eq_of_mem {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : x ∈ MarshallianDemand u p y) : IndirectUtility u p y = u x :=
  parametricValue_eq_of_maximum (A := fun θ : PriceIncome k => BudgetSet θ.1 θ.2)
    (F := fun _ z => u z) (p := (p, y)) hx

/-- At zero income, indirect utility equals the utility of consuming nothing. -/
theorem indirectUtility_zero {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) : IndirectUtility u p 0 = u (ZeroBundle k) := by
  apply indirectUtility_eq_of_mem
  rw [marshallianDemand_zero]
  exact Set.mem_singleton _

/-- **Proposition 3.3(a):** demand and indirect utility are homogeneous of degree zero. -/
theorem proposition_3_3a {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = MarshallianDemand u p y ∧
      IndirectUtility u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = IndirectUtility u p y := by
  refine ⟨proposition_3_1a u a ha p y, ?_⟩
  simp only [IndirectUtility, budgetSet_scale]

/-- Berge's theorem applies with every budget-continuity and compactness hypothesis discharged. -/
theorem consumer_maximum_theorem {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    (∀ θ : PriceIncome k, (MarshallianDemand u θ.1 θ.2).Nonempty) ∧
      SequentialUpper (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) ∧
      LocalCompactBound (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) ∧
      Continuous (fun θ : PriceIncome k => IndirectUtility u θ.1 θ.2) :=
  maximum_theorem (A := fun θ : PriceIncome k => BudgetSet θ.1 θ.2)
    (F := fun _ x => u x) (hu.comp continuous_snd) budgetSet_sequentialLower
    budgetSet_sequentialUpper budgetSet_localCompactBound (fun θ => budgetSet_nonempty θ.1 θ.2)

/-- **Proposition 3.3(b):** demand is upper semicontinuous in the book's closed-graph convention. -/
theorem proposition_3_3b {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u) :
    SequentialUpper (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.1

/-- The same demand correspondence has a common compact bound around each parameter. -/
theorem marshallianDemand_localCompactBound {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    LocalCompactBound (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.2.1

/-- Each complete set of demanded bundles is compact. -/
theorem marshallianDemand_isCompact {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) (p : PositivePrices k) (y : ℝ≥0) :
    IsCompact (MarshallianDemand u p y) :=
  (proposition_3_3b hu).isCompact (marshallianDemand_localCompactBound hu) (p, y)

/-- Demand also satisfies Mathlib's open-set definition of upper hemicontinuity. -/
theorem marshallianDemand_upperHemicontinuous {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    UpperHemicontinuous (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) := by
  intro θ
  obtain ⟨K, hK, hlocal⟩ := marshallianDemand_localCompactBound hu θ
  exact sequentialUpper_upperHemicontinuousAt (proposition_3_3b hu) hK.isSeqCompact hlocal

/-- **Proposition 3.3(c):** indirect utility is continuous even at zero income. -/
theorem proposition_3_3c {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u) :
    Continuous (fun θ : PriceIncome k => IndirectUtility u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.2.2

/-- **Proposition 3.3(b):** a unique demand selection is continuous on its parameter subset. -/
theorem proposition_3_3b_unique {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) (S : Set (PriceIncome k)) (s : S → NonnegativeOrthant k)
    (hs : ∀ θ : S, MarshallianDemand u θ.val.1 θ.val.2 = {s θ}) : Continuous s := by
  apply continuous_of_singleton_correspondence
  · intro θ x θ₀ x₀ hθ hx hm
    have hmem : x₀ ∈ MarshallianDemand u θ₀.val.1 θ₀.val.2 :=
      proposition_3_3b hu (fun n => (θ n).val) x θ₀.val x₀
        (continuous_subtype_val.continuousAt.tendsto.comp hθ) hx
        (fun n => by
          change x n ∈ MarshallianDemand u (θ n).val.1 (θ n).val.2
          rw [hs (θ n)]
          exact hm n)
    rwa [hs θ₀] at hmem
  · intro θ
    obtain ⟨K, hK, hlocal⟩ := marshallianDemand_localCompactBound hu θ.val
    refine ⟨K, hK, ?_⟩
    have hrestricted := (continuous_subtype_val.continuousAt (x := θ)).eventually hlocal
    filter_upwards [hrestricted] with η hη
    rwa [hs η] at hη

end Kreps.ConsumerDemand
