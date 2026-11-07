/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EventSubjectiveUtility
import ChoiceUnderUncertainty.MeasureMixtures
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The countably additive extension in the invitation on page 122

We take a sigma-algebra of state events. The explicit extra continuity condition
is continuity of the evaluated calibrated acts along increasing event sequences.
It gives a countably additive probability on the given sigma-algebra. Integrating
statewise roulette utility recovers every finite-partition formula. Dominated
convergence extends the values along approximations of richer acts.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Filter
open scoped ENNReal Topology

variable {S X : Type*} [MeasurableSpace S]

/-- The family of events in the specified sigma-algebra. -/
def SigmaEvents (S : Type*) [MeasurableSpace S] : Set (Set S) := {E | MeasurableSet E}

/-- The measurable events satisfy the event-algebra assumptions of Problem 5.6. -/
theorem sigmaEvents_isSetAlgebra : IsSetAlgebra (SigmaEvents S) :=
  ⟨MeasurableSet.empty, fun _ h => MeasurableSet.compl h, fun _ _ h g => MeasurableSet.union h g⟩

/-- Continuity from below for the event probabilities calibrated from preferences. -/
def EventWeightContinuous (p : SigmaEvents S → ℝ) : Prop :=
  ∀ (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n)), Monotone E →
    Tendsto (fun n => p ⟨E n, he n⟩) atTop (𝓝 (p ⟨⋃ n, E n, MeasurableSet.iUnion he⟩))

/-- The union of the first `n` events of a sequence. -/
def InitialEventUnion (E : ℕ → Set S) (n : ℕ) : Set S := ⋃ i : Fin n, E i

/-- A successor initial union adds exactly one event. -/
theorem initialEventUnion_succ {Y : Type*} (E : ℕ → Set Y) (n : ℕ) :
    InitialEventUnion E (n + 1) = InitialEventUnion E n ∪ E n := by
  ext s
  simp only [InitialEventUnion, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i.val < n
    · exact Or.inl ⟨⟨i.val, h⟩, hi⟩
    · have he : i.val = n := by omega
      exact Or.inr (he ▸ hi)
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hi⟩

/-- Finite additivity and continuity from below give countable additivity on disjoint sequences. -/
theorem eventWeight_hasSum (p : SigmaEvents S → ℝ)
    (hp : FinitelyAdditiveProbability sigmaEvents_isSetAlgebra p) (hc : EventWeightContinuous p)
    (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    HasSum (fun n => p ⟨E n, he n⟩) (p ⟨⋃ n, E n, MeasurableSet.iUnion he⟩) := by
  classical
  have hm (n) : MeasurableSet (InitialEventUnion E n) := MeasurableSet.iUnion fun i => he i.val
  have hi : Monotone (InitialEventUnion E) := monotone_nat_of_le_succ fun n => by
    rw [initialEventUnion_succ]
    exact Set.subset_union_left
  have hall : (⋃ n, InitialEventUnion E n) = ⋃ n, E n := by
    ext s
    simp only [InitialEventUnion, Set.mem_iUnion]
    exact ⟨fun ⟨_, i, h⟩ => ⟨i.val, h⟩, fun ⟨n, h⟩ => ⟨n + 1, Fin.last n, h⟩⟩
  have hv (n) : p ⟨InitialEventUnion E n, hm n⟩ =
      ∑ i ∈ Finset.range n, p ⟨E i, he i⟩ := by
    induction n with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      convert hp.2.2.1 using 1
      apply congrArg p
      apply Subtype.ext
      simp [InitialEventUnion]
    | succ n ih =>
      have hdis : Disjoint (InitialEventUnion E n) (E n) := by
        apply Set.disjoint_left.mpr
        intro s hs h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        exact Set.disjoint_left.mp (hd (ne_of_lt i.isLt)) hi h
      have hh := hp.2.2.2 ⟨InitialEventUnion E n, hm n⟩ ⟨E n, he n⟩ hdis
      rw [Finset.sum_range_succ, ← ih, ← hh]
      exact congrArg p (Subtype.ext (initialEventUnion_succ E n))
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => (hp.1 ⟨E n, he n⟩).1)]
  have h := hc (InitialEventUnion E) hm hi
  have hlast : (⟨⋃ n, InitialEventUnion E n, MeasurableSet.iUnion hm⟩ : SigmaEvents S) =
      ⟨⋃ n, E n, MeasurableSet.iUnion he⟩ := Subtype.ext hall
  simpa only [hv, hlast] using h

/-- The calibrated probabilities define an actual countably additive probability measure. -/
theorem probabilityMeasure_of_eventContinuity (p : SigmaEvents S → ℝ)
    (hp : FinitelyAdditiveProbability sigmaEvents_isSetAlgebra p) (hc : EventWeightContinuous p) :
    ∃ μ : ProbabilityMeasure S, ∀ E : SigmaEvents S, (μ : Measure S).real E.val = p E := by
  let m : ∀ E : Set S, MeasurableSet E → ℝ≥0∞ := fun E h => ENNReal.ofReal (p ⟨E, h⟩)
  have hzero : m ∅ MeasurableSet.empty = 0 := by simp [m, hp.2.2.1]
  have hsum {E : ℕ → Set S} (he : ∀ n, MeasurableSet (E n))
      (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
      m (⋃ n, E n) (MeasurableSet.iUnion he) = ∑' n, m (E n) (he n) := by
    have hs := eventWeight_hasSum p hp hc E he hd
    change ENNReal.ofReal _ = ∑' n, ENNReal.ofReal _
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => (hp.1 ⟨E n, he n⟩).1) hs.summable]
  let μ := Measure.ofMeasurable m hzero (fun {_} he hd => hsum he hd)
  have happ (E : SigmaEvents S) : μ E.val = ENNReal.ofReal (p E) :=
    Measure.ofMeasurable_apply E.val E.property
  have hmass : μ Set.univ = 1 := by
    rw [happ ⟨Set.univ, MeasurableSet.univ⟩, hp.2.1, ENNReal.ofReal_one]
  refine ⟨⟨μ, ⟨hmass⟩⟩, fun E => ?_⟩
  change (μ E.val).toReal = p E
  rw [happ, ENNReal.toReal_ofReal (hp.1 E).1]

/-- Continuity of calibrated event bets supplies continuity from below for their probabilities. -/
theorem probabilityMeasure_of_calibratedActs {F : EventAct (SigmaEvents S) X → ℝ}
    {r : EventAct (SigmaEvents S) X → EventAct (SigmaEvents S) X → Prop}
    (hF : Represents F r) (ha : EventAffine sigmaEvents_isSetAlgebra F)
    (b g : SimpleLottery X)
    (hn : F (EventConstant sigmaEvents_isSetAlgebra g) -
      F (EventConstant sigmaEvents_isSetAlgebra b) = 1)
    (hw : ∀ E : SigmaEvents S, EventRanking sigmaEvents_isSetAlgebra r b E.val E.property g b)
    (hc : ∀ (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n)), Monotone E →
      Tendsto (fun n => F (EventCut sigmaEvents_isSetAlgebra b (E n) (he n)
        (EventConstant sigmaEvents_isSetAlgebra g))) atTop
        (𝓝 (F (EventCut sigmaEvents_isSetAlgebra b (⋃ n, E n) (MeasurableSet.iUnion he)
          (EventConstant sigmaEvents_isSetAlgebra g))))) :
    ∃ μ : ProbabilityMeasure S, ∀ E : SigmaEvents S, (μ : Measure S).real E.val =
      EventProbability sigmaEvents_isSetAlgebra F b g E := by
  apply probabilityMeasure_of_eventContinuity _
    (problem_5_6e sigmaEvents_isSetAlgebra hF ha b g hn hw).1
  intro E he hm
  exact (hc E he hm).sub (tendsto_const_nhds (x := F (EventConstant sigmaEvents_isSetAlgebra b)))

/-- The integral of a simple state payoff is its finite partition-weighted sum. -/
theorem integral_partition_value {I : Type*} [Fintype I] (μ : ProbabilityMeasure S)
    (c : S → I) (he : ∀ i, MeasurableSet {s | c s = i}) (v : I → ℝ) :
    (∫ s, v (c s) ∂(μ : Measure S)) = ∑ i, (μ : Measure S).real {s | c s = i} * v i := by
  classical
  have hsum (s : S) : v (c s) = ∑ i, ({t | c t = i} : Set S).indicator (fun _ => v i) s := by
    simp [Set.indicator]
  simp_rw [hsum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (he i), setIntegral_const, smul_eq_mul]
  · intro i _
    exact (integrable_const _).indicator (he i)

/-- On every doubly simple act the integral extension equals the finite subjective EU formula. -/
theorem integral_simpleHorseValue {I : Type*} [Fintype I] (μ : ProbabilityMeasure S)
    (U : X → ℝ) (h : EventAct (SigmaEvents S) X) (c : S → I)
    (hc : ∀ i, MeasurableSet {s | c s = i}) (q : I → SimpleLottery X)
    (hh : ∀ s, h.val s = q (c s)) :
    (∫ s, ExpectedUtility U (h.val s) ∂(μ : Measure S)) =
      ∑ i, (μ : Measure S).real {s | c s = i} * ExpectedUtility U (q i) := by
  simpa only [hh] using integral_partition_value μ c hc (fun i => ExpectedUtility U (q i))

/-- Dominated almost-everywhere approximation extends these integrals to more general acts. -/
theorem simpleHorseValue_tendsto (μ : ProbabilityMeasure S) (U : X → ℝ)
    (h : S → SimpleLottery X) (g : ℕ → EventAct (SigmaEvents S) X) (bound : S → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (fun s => ExpectedUtility U ((g n).val s)) (μ : Measure S))
    (hb : Integrable bound (μ : Measure S))
    (hdom : ∀ n, ∀ᵐ s ∂(μ : Measure S), ‖ExpectedUtility U ((g n).val s)‖ ≤ bound s)
    (hlim : ∀ᵐ s ∂(μ : Measure S), Tendsto (fun n => ExpectedUtility U ((g n).val s)) atTop
      (𝓝 (ExpectedUtility U (h s)))) :
    Tendsto (fun n => ∫ s, ExpectedUtility U ((g n).val s) ∂(μ : Measure S)) atTop
      (𝓝 (∫ s, ExpectedUtility U (h s) ∂(μ : Measure S))) :=
  tendsto_integral_of_dominated_convergence bound hm hb hdom hlim

end Kreps.ChoiceUnderUncertainty
