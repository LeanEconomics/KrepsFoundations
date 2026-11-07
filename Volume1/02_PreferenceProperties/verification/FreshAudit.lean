import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Logic.Function.Basic
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Basic.NNReal.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Piecewise
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Algebra.Order.UpperLower
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice, preference, and utility

Kreps I, §1.1, pp. 1-4: feasible choice, finite nonemptiness, choice coherence,
complete and transitive preferences, and equations (1.1)-(1.3).

Choice is extended to the empty menu by the empty set. Nonemptiness is a separate
hypothesis, imposed only on finite nonempty menus in `FiniteNonempty`.
`FeasibleOn` and `CoherentOn` retain restricted menu domains for Problems 1.15-1.16.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- The complete collection of nonempty menus. -/
def FullMenus (X : Type*) : Set (Set X) := {A | A.Nonempty}

/-- A choice rule returns a set of acceptable alternatives from each menu. -/
abbrev ChoiceRule (X : Type*) := Set X → Set X

/-- Feasibility on an explicitly specified menu domain. -/
def FeasibleOn (menus : Set (Set X)) (c : ChoiceRule X) : Prop :=
  ∀ A ∈ menus, c A ⊆ A

/-- Feasibility for the full-domain extension, including the empty menu. -/
def Feasible (c : ChoiceRule X) : Prop := ∀ A, c A ⊆ A

/-- **Definition 1.1a.** Choice is nonempty on every finite nonempty menu. -/
def FiniteNonempty (c : ChoiceRule X) : Prop :=
  ∀ A, A.Finite → A.Nonempty → (c A).Nonempty

/-- **Definition 1.1b.** Coherence with an explicit admissible-menu domain. -/
def CoherentOn (menus : Set (Set X)) (c : ChoiceRule X) : Prop :=
  ∀ A ∈ menus, ∀ B ∈ menus, ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B,
    x ∈ c A → y ∉ c A → y ∉ c B

/-- **Definition 1.1b.** Full-domain choice coherence. -/
def Coherent (c : ChoiceRule X) : Prop :=
  ∀ A B, ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, x ∈ c A → y ∉ c A → y ∉ c B

/-- **Definition 1.1c.** Every pair of alternatives can be compared. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- **Definition 1.1d.** The preference relation is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- Complete and transitive weak preference; indifference is allowed. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Equation (1.2): all alternatives at least as good as every menu member. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Equation (1.3): preference induced by a real-valued utility function. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- Equation (1.1): the full set of utility-maximizing alternatives. -/
def UtilityChoice (u : X → ℝ) : ChoiceRule X := PrefChoice (UtilityPref u)

/-- A numerical function represents preference, with the book's orientation. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Preference revealed by choice from pairs, including singleton pairs. -/
def Revealed (c : ChoiceRule X) (x y : X) : Prop := x ∈ c {x, y}

/-- Strict preference derived from weak preference. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference derived from weak preference. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- **Definition 1.6**, p. 7: the alternatives no better than `x`. -/
def NoBetterThan (r : X → X → Prop) (x : X) : Set X := {y | r x y}

/-- Complete preferences are reflexive. -/
theorem complete_refl {r : X → X → Prop} (hc : Complete r) (x : X) : r x x :=
  (hc x x).elim id id

/-- Choice generated by a preference relation is feasible. -/
theorem prefChoice_feasible (r : X → X → Prop) : Feasible (PrefChoice r) :=
  fun _ _ h => h.1

/-- A feasible full-domain choice selects nothing from the empty menu. -/
theorem feasible_empty {c : ChoiceRule X} (hc : Feasible c) : c ∅ = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hc ∅ hx

/-- Equal numerical representations give identical maximizing sets. -/
theorem represents_choice {u : X → ℝ} {r : X → X → Prop} (hu : Represents u r) :
    PrefChoice r = UtilityChoice u := by
  ext A x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨hx, fun y hy => (hu x y).mp (hr y hy)⟩
  · rintro ⟨hx, hu'⟩
    exact ⟨hx, fun y hy => (hu x y).mpr (hu' y hy)⟩

/-- The full-domain coherence condition is exactly coherence on nonempty menus. -/
theorem coherent_iff_on_full {c : ChoiceRule X} :
    Coherent c ↔ CoherentOn (FullMenus X) c := by
  constructor
  · intro h A _ B _ x hx y hy
    exact h A B x hx y hy
  · intro h A B x hx y hy
    exact h A ⟨x, hx.1⟩ B ⟨x, hx.2⟩ x hx y hy

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Upper semicontinuity of uniformly controlled series

Analytic support for Kreps I, Problem 2.10. Uniform limits preserve upper
semicontinuity, so a series of upper semicontinuous real functions with a
summable bound on the absolute values is upper semicontinuous.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- A uniform limit of upper semicontinuous real functions is upper semicontinuous. -/
theorem upperSemicontinuous_of_tendstoUniformly {I X : Type*} [TopologicalSpace X]
    {l : Filter I} [l.NeBot] {f : I → X → ℝ} {g : X → ℝ}
    (hlim : TendstoUniformly f g l) (hf : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous g := by
  intro x b hb
  let ε := (b - g x) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have he : 3 * ε = b - g x := by dsimp [ε]; ring
  obtain ⟨i, hi⟩ := ((Metric.tendstoUniformly_iff.mp hlim) ε hε).exists
  have hx := hi x
  rw [Real.dist_eq] at hx
  have hx' : f i x < g x + 2 * ε := by linarith [(abs_lt.mp hx).1]
  filter_upwards [hf i x (g x + 2 * ε) hx'] with y hy
  have hy' := hi y
  rw [Real.dist_eq] at hy'
  linarith [(abs_lt.mp hy').2]

/-- Summably bounded upper semicontinuous summands have an upper semicontinuous sum. -/
theorem upperSemicontinuous_tsum_of_norm_le {I X : Type*} [TopologicalSpace X]
    {f : I → X → ℝ} {w : I → ℝ} (hw : Summable w)
    (hf : ∀ i, UpperSemicontinuous (f i)) (hbound : ∀ i x, ‖f i x‖ ≤ w i) :
    UpperSemicontinuous (fun x => ∑' i, f i x) :=
  upperSemicontinuous_of_tendstoUniformly (tendstoUniformly_tsum hw hbound)
    (fun _ => upperSemicontinuous_sum (fun i _ => hf i))

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Lower-tail mass of a finite real measure

Analytic support for Kreps I, Problem 2.15. The cumulative lower-tail mass of a
finite measure is nondecreasing and upper semicontinuous. No normalization to a
probability measure is imposed. Continuity from above of the measure supplies
the upper-semicontinuity proof.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory
open scoped Topology

/-- The real-valued mass of the closed lower half-line for an arbitrary finite measure. -/
noncomputable def LowerDistribution (μ : Measure ℝ) (a : ℝ) : ℝ := μ.real (Set.Iic a)

/-- Enlarging a lower half-line increases its mass. -/
theorem lowerDistribution_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (LowerDistribution μ) :=
  fun _ _ hab => measureReal_mono (Set.Iic_subset_Iic.mpr hab)

/-- Lower-tail masses converge when cutoffs decrease geometrically to the target cutoff. -/
theorem lowerDistribution_tendsto_above (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => LowerDistribution μ (a + (1 / 2 : ℝ) ^ n))
      Filter.atTop (𝓝 (LowerDistribution μ a)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => a + (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Antitone (fun n : ℕ => a + (1 / 2 : ℝ) ^ n) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hi : (⋂ n : ℕ, Set.Iic (a + (1 / 2 : ℝ) ^ n)) = Set.Iic a := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ n : ℕ, x ≤ a + (1 / 2 : ℝ) ^ n := Set.mem_iInter.mp hx
      exact isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hx')
    · intro hx
      apply Set.mem_iInter.mpr
      intro n
      exact le_trans hx (le_add_of_nonneg_right
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n))
  have hμ := tendsto_measure_iInter_atTop (μ := μ)
    (fun _ : ℕ => isClosed_Iic.measurableSet.nullMeasurableSet)
    (fun i j hij => Set.Iic_subset_Iic.mpr (hm hij)) ⟨0, measure_ne_top μ _⟩
  rw [hi] at hμ
  simpa only [LowerDistribution, measureReal_def, Function.comp_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top μ (Set.Iic a))).tendsto.comp hμ

/-- The lower-tail mass function is upper semicontinuous, even when the measure has atoms. -/
theorem lowerDistribution_upperSemicontinuous (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UpperSemicontinuous (LowerDistribution μ) := by
  intro a b hb
  obtain ⟨n, hn⟩ := ((lowerDistribution_tendsto_above μ a).eventually
    (isOpen_Iio.mem_nhds hb)).exists
  have hnear : ∀ᶠ y in 𝓝 a, y < a + (1 / 2 : ℝ) ^ n :=
    isOpen_Iio.mem_nhds (lt_add_of_pos_right a (pow_pos (by norm_num) n))
  filter_upwards [hnear] with y hy
  exact (lowerDistribution_monotone μ hy.le).trans_lt hn

/-- If the cutoff has zero mass, approaching it from below gives the same lower-tail mass. -/
theorem lowerDistribution_tendsto_below (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) :
    Filter.Tendsto (fun n : ℕ => LowerDistribution μ (a - (1 / 2 : ℝ) ^ n))
      Filter.atTop (𝓝 (LowerDistribution μ a)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 a) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Monotone (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hi : (⋃ n : ℕ, Set.Iic (a - (1 / 2 : ℝ) ^ n)) = Set.Iio a := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact hn.trans_lt (sub_lt_self a (pow_pos (by norm_num) n))
    · intro hx
      obtain ⟨n, hn⟩ := (hlim.eventually (isOpen_Ioi.mem_nhds hx)).exists
      exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hμ := tendsto_measure_iUnion_atTop (μ := μ)
    (fun i j hij => Set.Iic_subset_Iic.mpr (hm hij))
  rw [hi, measure_congr (Iio_ae_eq_Iic' ha)] at hμ
  simpa only [LowerDistribution, measureReal_def, Function.comp_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top μ (Set.Iic a))).tendsto.comp hμ

/-- Absence of an atom supplies lower semicontinuity at the cutoff. -/
theorem lowerDistribution_lowerSemicontinuousAt (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) : LowerSemicontinuousAt (LowerDistribution μ) a := by
  intro b hb
  obtain ⟨n, hn⟩ := ((lowerDistribution_tendsto_below μ a ha).eventually
    (isOpen_Ioi.mem_nhds hb)).exists
  have hnear : ∀ᶠ y in 𝓝 a, a - (1 / 2 : ℝ) ^ n < y :=
    isOpen_Ioi.mem_nhds (sub_lt_self a (pow_pos (by norm_num) n))
  filter_upwards [hnear] with y hy
  exact hn.trans_le (lowerDistribution_monotone μ hy.le)

/-- The lower-tail function is continuous at cutoffs with zero singleton mass. -/
theorem lowerDistribution_continuousAt (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ)
    (ha : μ {a} = 0) : ContinuousAt (LowerDistribution μ) a :=
  continuousAt_iff_lower_upperSemicontinuousAt.mpr
    ⟨lowerDistribution_lowerSemicontinuousAt μ a ha, lowerDistribution_upperSemicontinuous μ a⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: Euclidean distance and elementary topology

Definitions A2.1–A2.5 and Proposition A2.4, pp. 441–443. Euclidean space carries
its genuine sum-of-squares norm. Its explicit homeomorphism to the finite product
explains why the chapter can use the product metric for topological arguments.
-/

namespace Kreps.PreferenceProperties

/-- The appendix's finite-dimensional Euclidean space, with its Euclidean norm. -/
abbrev CommodityEuclidean (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- **Definition A2.1:** Euclidean distance is the square root of the sum of squared differences. -/
theorem definition_A2_1 {k : ℕ} (x y : CommodityEuclidean k) :
    dist x y = Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  simpa only [Real.dist_eq, sq_abs] using EuclideanSpace.dist_eq x y

/-- The four metric properties listed immediately after Definition A2.1. -/
theorem euclidean_distance_properties {k : ℕ} (x y z : CommodityEuclidean k) (a : ℝ) :
    0 ≤ dist x y ∧ (dist x y = 0 ↔ x = y) ∧ dist x y = dist y x ∧
      dist (a • x) (a • y) = |a| * dist x y ∧ dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_nonneg, dist_eq_zero, dist_comm x y,
    by simpa only [Real.norm_eq_abs] using dist_smul₀ a x y, dist_triangle x y z⟩

/-- The translation invariance noted alongside Definition A2.1. -/
theorem euclidean_distance_translation {k : ℕ} (x y z : CommodityEuclidean k) :
    dist (x + z) (y + z) = dist x y := dist_add_right x y z

/-- The Euclidean and coordinate-product presentations have the same topology. -/
noncomputable def euclideanProductHomeomorph (k : ℕ) :
    CommodityEuclidean k ≃ₜ (Fin k → ℝ) := PiLp.homeomorph 2 (fun _ => ℝ)

/-- **Definition A2.2:** the epsilon-neighborhood is an open metric ball. -/
theorem definition_A2_2 {k : ℕ} (x : CommodityEuclidean k) (ε : ℝ) :
    {y | dist y x < ε} = Metric.ball x ε := rfl

/-- The exercise in footnote 2: every open ball is open. -/
theorem appendix2_open_ball {X : Type*} [PseudoMetricSpace X] (x : X) (ε : ℝ) :
    IsOpen (Metric.ball x ε) := Metric.isOpen_ball

/-- **Definition A2.3:** every point of an open set has a ball inside the set. -/
theorem definition_A2_3_open {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∃ ε > 0, Metric.ball x ε ⊆ S := Metric.isOpen_iff

/-- **Definition A2.3:** closed sets are precisely the complements of open sets. -/
theorem definition_A2_3_closed {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsClosed S ↔ IsOpen Sᶜ := isOpen_compl_iff.symm

/-- Empty and full spaces are both open and closed, as observed on p. 442. -/
theorem appendix2_empty_univ_clopen {X : Type*} [TopologicalSpace X] :
    IsOpen (∅ : Set X) ∧ IsClosed (∅ : Set X) ∧
      IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) :=
  ⟨isOpen_empty, isClosed_empty, isOpen_univ, isClosed_univ⟩

/-- **Proposition A2.4:** arbitrary unions of open sets are open. -/
theorem proposition_A2_4_open_union {X I : Type*} [TopologicalSpace X]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) : IsOpen (⋃ i, U i) := isOpen_iUnion hU

/-- **Proposition A2.4:** finite intersections of open sets are open. -/
theorem proposition_A2_4_open_inter {X I : Type*} [TopologicalSpace X] [Finite I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) : IsOpen (⋂ i, U i) :=
  isOpen_iInter_of_finite hU

/-- **Proposition A2.4:** finite unions of closed sets are closed. -/
theorem proposition_A2_4_closed_union {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) : IsClosed (⋃ i, C i) :=
  isClosed_iUnion_of_finite hC

/-- **Proposition A2.4:** arbitrary intersections of closed sets are closed. -/
theorem proposition_A2_4_closed_inter {X I : Type*} [TopologicalSpace X]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) : IsClosed (⋂ i, C i) :=
  isClosed_iInter hC

/-- The relative-open definition on p. 443, expressed through subtype preimages. -/
theorem appendix2_relative_open {X : Type*} [TopologicalSpace X] (S : Set X) (A : Set S) :
    IsOpen A ↔ ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = A := isOpen_induced_iff

/-- The corresponding relative-closed definition. -/
theorem appendix2_relative_closed {X : Type*} [TopologicalSpace X] (S : Set X) (A : Set S) :
    IsClosed A ↔ ∃ C : Set X, IsClosed C ∧ Subtype.val ⁻¹' C = A := isClosed_induced_iff

/-- **Definition A2.5:** closure is the least closed superset. -/
theorem definition_A2_5_closure {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsClosed (closure S) ∧ S ⊆ closure S ∧
      ∀ C, IsClosed C → S ⊆ C → closure S ⊆ C :=
  ⟨isClosed_closure, subset_closure, fun _ hC hSC => closure_minimal hSC hC⟩

/-- **Definition A2.5:** interior is the greatest open subset. -/
theorem definition_A2_5_interior {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsOpen (interior S) ∧ interior S ⊆ S ∧
      ∀ U, IsOpen U → U ⊆ S → U ⊆ interior S :=
  ⟨isOpen_interior, interior_subset, fun _ hU hUS => interior_maximal hUS hU⟩

/-- The intersection construction of closure described after Definition A2.5. -/
theorem appendix2_closure_intersection {X : Type*} [TopologicalSpace X] (S : Set X) :
    closure S = ⋂₀ {C | S ⊆ C ∧ IsClosed C} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sInter.mpr (fun C hC => closure_minimal hC.1 hC.2 hx)
  · intro x hx
    exact Set.mem_sInter.mp hx _ ⟨subset_closure, isClosed_closure⟩

/-- The union construction of interior described on p. 443. -/
theorem appendix2_interior_union {X : Type*} [TopologicalSpace X] (S : Set X) :
    interior S = ⋃₀ {U | U ⊆ S ∧ IsOpen U} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sUnion.mpr ⟨interior S, ⟨interior_subset, isOpen_interior⟩, hx⟩
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
    exact interior_maximal hU.1 hU.2 hxU

/-- Interior points are exactly the centers of balls contained in the set. -/
theorem appendix2_interior_ball {X : Type*} [PseudoMetricSpace X] (S : Set X) (x : X) :
    x ∈ interior S ↔ ∃ ε > 0, Metric.ball x ε ⊆ S := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]

/-- The complement-duality exercise on p. 443. -/
theorem appendix2_closure_interior_complement {X : Type*} [TopologicalSpace X] (S : Set X) :
    closure S = (interior Sᶜ)ᶜ ∧ interior S = (closure Sᶜ)ᶜ :=
  ⟨closure_eq_compl_interior_compl, interior_eq_compl_closure_compl⟩

/-- The relative interior of a domain in itself is the entire domain. -/
theorem appendix2_relative_interior_self {X : Type*} [TopologicalSpace X] (S : Set X) :
    interior (Set.univ : Set S) = Set.univ := interior_univ

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Joint continuity of increasing aggregators

An increasing real-valued function on a finite product of densely ordered
spaces is jointly continuous if it is continuous in each coordinate. The
proof builds a finite product neighborhood inside each strict level set.
Endpoints of the coordinate intervals are allowed.
-/

namespace Kreps.PreferenceProperties

open Filter Set
open scoped Topology

/-- A continuous strict lower level has a nearby lower bound whose upper ray is a neighborhood. -/
theorem continuous_lower_level_bound {A : Type*} [LinearOrder A] [DenselyOrdered A]
    [TopologicalSpace A] [OrderTopology A] {f : A → ℝ} (hf : Continuous f)
    {x : A} {a : ℝ} (ha : a < f x) :
    ∃ y, y ≤ x ∧ a < f y ∧ Ici y ∈ 𝓝 x := by
  by_cases hx : ∃ z, z < x
  · obtain ⟨l, hl, hs⟩ := exists_Ioc_subset_of_mem_nhds
      (hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ha)) hx
    obtain ⟨y, hly, hyx⟩ := exists_between hl
    exact ⟨y, hyx.le, hs ⟨hly, hyx.le⟩, Ici_mem_nhds hyx⟩
  · refine ⟨x, le_rfl, ha, ?_⟩
    have he : Ici x = univ := by
      ext y
      simp only [mem_Ici, mem_univ, iff_true]
      exact le_of_not_gt (fun hy => hx ⟨y, hy⟩)
    rw [he]
    exact univ_mem

variable {I : Type*} [DecidableEq I] {A : I → Type*}
variable [∀ i, LinearOrder (A i)] [∀ i, DenselyOrdered (A i)]
variable [∀ i, TopologicalSpace (A i)] [∀ i, OrderTopology (A i)]

/-- Lower bounds for finitely many coordinates can be chosen inside a strict lower level. -/
theorem finite_coordinate_lower_bound {F : (∀ i, A i) → ℝ}
    (hc : ∀ p i, Continuous (fun t => F (Function.update p i t)))
    (s : Finset I) (p : ∀ i, A i) {a : ℝ} (ha : a < F p) :
    ∃ q, q ≤ p ∧ a < F q ∧ (∀ i ∈ s, Ici (q i) ∈ 𝓝 (p i)) ∧
      ∀ i ∉ s, q i = p i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨p, le_rfl, ha, by simp, by simp⟩
  | @insert i s his ih =>
    obtain ⟨q, hqp, haq, hqn, hqe⟩ := ih
    have hiq : q i = p i := hqe i his
    have haq' : a < F (Function.update q i (q i)) := by
      simpa only [Function.update_eq_self] using haq
    obtain ⟨t, hti, hat, htn⟩ := continuous_lower_level_bound (hc q i) haq'
    refine ⟨Function.update q i t, ?_, hat, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hti.trans (hqp i)
      · simpa only [Function.update_of_ne hji] using hqp j
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        simpa only [Function.update_self, hiq] using htn
      · have hji : j ≠ i := fun h => his (h ▸ hjs)
        simpa only [Function.update_of_ne hji] using hqn j hjs
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i s)
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
      simpa only [Function.update_of_ne hji] using hqe j hjs

/-- A separately continuous increasing finite-product function has open strict lower levels. -/
theorem finiteProductMonotone_isOpen_lt [Finite I] {F : (∀ i, A i) → ℝ}
    (hm : Monotone F) (hc : ∀ p i, Continuous (fun t => F (Function.update p i t)))
    (a : ℝ) : IsOpen {p | a < F p} := by
  classical
  let : Fintype I := Fintype.ofFinite I
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨q, _, haq, hqn, _⟩ := finite_coordinate_lower_bound hc Finset.univ p hp
  have hn (i : I) : ∀ᶠ x in 𝓝 p, q i ≤ x i :=
    (continuous_apply i).continuousAt.preimage_mem_nhds (hqn i (Finset.mem_univ i))
  filter_upwards [Filter.eventually_all.mpr hn] with x hx
  exact haq.trans_le (hm hx)

/-- Coordinate continuity and monotonicity imply joint continuity on a finite interval product. -/
theorem finiteProductMonotone_continuous [Finite I] {F : (∀ i, A i) → ℝ}
    (hm : Monotone F) (hc : ∀ p i, Continuous (fun t => F (Function.update p i t))) :
    Continuous F := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  refine ⟨finiteProductMonotone_isOpen_lt hm hc a, ?_⟩
  have hn : Monotone (fun p : ∀ i, (A i)ᵒᵈ => -F p) := by
    intro p q hpq
    exact neg_le_neg (hm hpq)
  have ho := finiteProductMonotone_isOpen_lt hn (fun p i => (hc p i).neg) (-a)
  have hdual : Continuous (fun p : ∀ i, A i => (fun i => p i : ∀ i, (A i)ᵒᵈ)) :=
    continuous_pi (fun i => continuous_apply i)
  convert ho.preimage hdual using 1
  ext p
  change F p < a ↔ -a < -F p
  exact neg_lt_neg_iff.symm

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Dyadic grids for ordered bisymmetric means

The algebraic stage of the cardinal-scale construction used in Proposition 2.14.
No additive representation is assumed: a reflexive symmetric bisymmetric mean
generates its own nested grid, and bisymmetry supplies the midpoint identity.
-/

namespace Kreps.PreferenceProperties

/-- The algebraic and order properties of a strict symmetric bisymmetric mean. -/
structure OrderedBisymmetricMean (α : Type*) [LinearOrder α] where
  mean : α → α → α
  reflexive : ∀ x, mean x x = x
  symmetric : ∀ x y, mean x y = mean y x
  bisymmetric : ∀ x y z w, mean (mean x y) (mean z w) = mean (mean x z) (mean y w)
  strictMono_left : ∀ y, StrictMono (fun x => mean x y)
  strictMono_right : ∀ x, StrictMono (mean x)

variable {α : Type*} [LinearOrder α]

/-- Repeated midpoint subdivision, with the endpoint values retained at even grid indices. -/
def MeanDyadicGrid (F : α → α → α) (a b : α) : ℕ → ℕ → α
  | 0, k => if k = 0 then a else b
  | n + 1, k => F (MeanDyadicGrid F a b n (k / 2))
      (MeanDyadicGrid F a b n ((k + 1) / 2))

/-- A strict mean lies strictly between unequal ordered arguments. -/
theorem orderedMean_between (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) :
    a < M.mean a b ∧ M.mean a b < b := by
  constructor
  · exact by simpa only [M.reflexive] using M.strictMono_right a hab
  · exact by simpa only [M.reflexive] using M.strictMono_left b hab

/-- Refining the grid preserves an old point at twice its former index. -/
theorem meanDyadicGrid_even (M : OrderedBisymmetricMean α) (a b : α) (n k : ℕ) :
    MeanDyadicGrid M.mean a b (n + 1) (2 * k) = MeanDyadicGrid M.mean a b n k := by
  have h₀ : 2 * k / 2 = k := by omega
  have h₁ : (2 * k + 1) / 2 = k := by omega
  simp only [MeanDyadicGrid, h₀, h₁, M.reflexive]

/-- New odd-index points are means of neighboring old points. -/
theorem meanDyadicGrid_odd (M : OrderedBisymmetricMean α) (a b : α) (n k : ℕ) :
    MeanDyadicGrid M.mean a b (n + 1) (2 * k + 1) =
      M.mean (MeanDyadicGrid M.mean a b n k) (MeanDyadicGrid M.mean a b n (k + 1)) := by
  have h₀ : (2 * k + 1) / 2 = k := by omega
  have h₁ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [MeanDyadicGrid, h₀, h₁]

/-- Every refinement starts at the designated left endpoint. -/
theorem meanDyadicGrid_left (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ) :
    MeanDyadicGrid M.mean a b n 0 = a := by
  induction n with
  | zero => simp [MeanDyadicGrid]
  | succ n ih => simpa only [Nat.mul_zero, ih] using meanDyadicGrid_even M a b n 0

/-- Every refinement ends at the designated right endpoint. -/
theorem meanDyadicGrid_right (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ) :
    MeanDyadicGrid M.mean a b n (2 ^ n) = b := by
  induction n with
  | zero => simp [MeanDyadicGrid]
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm, meanDyadicGrid_even, ih]

/-- A two-step interval has its middle grid point as its mean. -/
theorem meanDyadicGrid_near (M : OrderedBisymmetricMean α) (a b : α) (n : ℕ)
    (hmid : ∀ i j, i ≤ 2 ^ n → j ≤ 2 ^ n →
      M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b n j) =
        MeanDyadicGrid M.mean a b (n + 1) (i + j))
    (k : ℕ) (hk : k + 2 ≤ 2 ^ (n + 1)) :
    M.mean (MeanDyadicGrid M.mean a b (n + 1) k)
      (MeanDyadicGrid M.mean a b (n + 1) (k + 2)) =
        MeanDyadicGrid M.mean a b (n + 1) (k + 1) := by
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  by_cases he : k % 2 = 0
  · have hk' : k = 2 * (k / 2) := by omega
    have hk₂ : k + 2 = 2 * (k / 2 + 1) := by omega
    have hk₁ : k + 1 = 2 * (k / 2) + 1 := by omega
    have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
      (meanDyadicGrid_even M a b n (k / 2))
    have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₂).trans
      (meanDyadicGrid_even M a b n (k / 2 + 1))
    have hm := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
      (meanDyadicGrid_odd M a b n (k / 2))
    rw [hl, hr, hm]
  · have hk' : k = 2 * (k / 2) + 1 := by omega
    have hk₂ : k + 2 = 2 * (k / 2 + 1) + 1 := by omega
    have hk₁ : k + 1 = 2 * (k / 2 + 1) := by omega
    have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
      (meanDyadicGrid_odd M a b n (k / 2))
    have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₂).trans
      (meanDyadicGrid_odd M a b n (k / 2 + 1))
    have hm := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
      (meanDyadicGrid_even M a b n (k / 2 + 1))
    rw [hl, hr, hm]
    rw [M.symmetric (MeanDyadicGrid M.mean a b n (k / 2 + 1))
      (MeanDyadicGrid M.mean a b n (k / 2 + 1 + 1)), M.bisymmetric, M.reflexive]
    have hi : k / 2 ≤ 2 ^ n := by omega
    have hj : k / 2 + 1 + 1 ≤ 2 ^ n := by omega
    rw [hmid _ _ hi hj]
    have hsum : k / 2 + (k / 2 + 1 + 1) = 2 * (k / 2 + 1) := by omega
    rw [hsum, meanDyadicGrid_even, M.reflexive]

/-- Bisymmetry makes arbitrary grid pairs average their dyadic indices. -/
theorem meanDyadicGrid_midpoint (M : OrderedBisymmetricMean α) (a b : α) (n i j : ℕ)
    (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ n) :
    M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b n j) =
      MeanDyadicGrid M.mean a b (n + 1) (i + j) := by
  induction n generalizing i j with
  | zero =>
    norm_num at hi hj
    interval_cases i <;> interval_cases j <;>
      simp [MeanDyadicGrid, M.reflexive, M.symmetric]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have hi₀ : i / 2 ≤ 2 ^ n := by omega
    have hi₁ : (i + 1) / 2 ≤ 2 ^ n := by omega
    have hj₀ : j / 2 ≤ 2 ^ n := by omega
    have hj₁ : (j + 1) / 2 ≤ 2 ^ n := by omega
    change M.mean
      (M.mean (MeanDyadicGrid M.mean a b n (i / 2))
        (MeanDyadicGrid M.mean a b n ((i + 1) / 2)))
      (M.mean (MeanDyadicGrid M.mean a b n (j / 2))
        (MeanDyadicGrid M.mean a b n ((j + 1) / 2))) =
      M.mean (MeanDyadicGrid M.mean a b (n + 1) ((i + j) / 2))
        (MeanDyadicGrid M.mean a b (n + 1) ((i + j + 1) / 2))
    rw [M.bisymmetric, ih _ _ hi₀ hj₀, ih _ _ hi₁ hj₁]
    by_cases hei : i % 2 = 0
    · congr 2 <;> omega
    · by_cases hej : j % 2 = 0
      · congr 2 <;> omega
      · have hright : (i + 1) / 2 + (j + 1) / 2 = i / 2 + j / 2 + 2 := by omega
        have hmiddle : (i + j) / 2 = i / 2 + j / 2 + 1 := by omega
        have hmiddle' : (i + j + 1) / 2 = i / 2 + j / 2 + 1 := by omega
        rw [hright, hmiddle, hmiddle', M.reflexive]
        exact meanDyadicGrid_near M a b n ih (i / 2 + j / 2) (by omega)

/-- Consecutive dyadic grid points are strictly ordered between distinct endpoints. -/
theorem meanDyadicGrid_lt_succ (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (n k : ℕ) (hk : k < 2 ^ n) :
    MeanDyadicGrid M.mean a b n k < MeanDyadicGrid M.mean a b n (k + 1) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by norm_num at hk; omega
    subst k
    simpa [MeanDyadicGrid] using hab
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have hkhalf : k / 2 < 2 ^ n := by omega
    have hbetween := orderedMean_between M (ih (k / 2) hkhalf)
    by_cases he : k % 2 = 0
    · have hk' : k = 2 * (k / 2) := by omega
      have hk₁ : k + 1 = 2 * (k / 2) + 1 := by omega
      have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
        (meanDyadicGrid_even M a b n (k / 2))
      have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
        (meanDyadicGrid_odd M a b n (k / 2))
      rw [hl, hr]
      exact hbetween.1
    · have hk' : k = 2 * (k / 2) + 1 := by omega
      have hk₁ : k + 1 = 2 * (k / 2 + 1) := by omega
      have hl := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk').trans
        (meanDyadicGrid_odd M a b n (k / 2))
      have hr := (congrArg (MeanDyadicGrid M.mean a b (n + 1)) hk₁).trans
        (meanDyadicGrid_even M a b n (k / 2 + 1))
      rw [hl, hr]
      exact hbetween.2

/-- Each finite grid is strictly increasing in its valid index interval. -/
theorem meanDyadicGrid_strictMonoOn (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (n : ℕ) : StrictMonoOn (MeanDyadicGrid M.mean a b n) (Set.Iic (2 ^ n)) :=
  strictMonoOn_Iic_of_lt_succ (fun k hk => meanDyadicGrid_lt_succ M hab n k hk)

/-- Repeated refinement does not change any existing grid point. -/
theorem meanDyadicGrid_refine (M : OrderedBisymmetricMean α) (a b : α) (n m k : ℕ) :
    MeanDyadicGrid M.mean a b (n + m) (k * 2 ^ m) = MeanDyadicGrid M.mean a b n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hindex : k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) := by rw [pow_succ]; ring
    rw [Nat.add_succ, hindex, meanDyadicGrid_even, ih]

/-- The union of all finite dyadic mean grids. -/
def MeanDyadicPoints (M : OrderedBisymmetricMean α) (a b : α) : Set α :=
  {x | ∃ n k, k ≤ 2 ^ n ∧ x = MeanDyadicGrid M.mean a b n k}

/-- The dyadic points are closed under the mean operation. -/
theorem meanDyadicPoints_mean (M : OrderedBisymmetricMean α) (a b : α) {x y : α}
    (hx : x ∈ MeanDyadicPoints M a b) (hy : y ∈ MeanDyadicPoints M a b) :
    M.mean x y ∈ MeanDyadicPoints M a b := by
  obtain ⟨n, i, hi, rfl⟩ := hx
  obtain ⟨m, j, hj, rfl⟩ := hy
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  refine ⟨n + m + 1, i * 2 ^ m + j * 2 ^ n, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · have hleft := meanDyadicGrid_refine M a b n m i
    have hright := meanDyadicGrid_refine M a b m n j
    rw [Nat.add_comm m n] at hright
    rw [← hleft, ← hright]
    exact meanDyadicGrid_midpoint M a b (n + m) _ _ hi' hj'

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 3: convex sets and their hulls

Kreps I, Definition A3.1, Propositions A3.2–A3.5 and A3.7, pp. 452–456.
These interfaces use Mathlib's convexity and hull constructions. Finite combinations
include an explicit nonnegative weight vector with total weight one. Carathéodory's
theorem bounds the number of points by the dimension plus one.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition A3.1:** closure under the book's two-point convex combinations. -/
theorem definition_A3_1 : Convex ℝ S ↔
    ∀ x ∈ S, ∀ y ∈ S, ∀ a ∈ Set.Icc (0 : ℝ) 1, a • x + (1 - a) • y ∈ S := by
  constructor
  · intro h x hx y hy a ha
    exact h hx hy ha.1 (sub_nonneg.mpr ha.2) (by linarith)
  · intro h x hx y hy a b ha hb hab
    have he : b = 1 - a := by linarith
    subst b
    exact h x hx y hy a ⟨ha, by linarith⟩

/-- **Proposition A3.2:** any finite convex combination remains in the set. -/
theorem proposition_A3_2 {ι : Type*} (t : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hS : Convex ℝ S) (hw : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ S) : ∑ i ∈ t, w i • z i ∈ S :=
  hS.sum_mem hw h1 hz

/-- **Proposition A3.3:** arbitrary intersections of convex sets are convex. -/
theorem proposition_A3_3 {C : Set (Set E)} (hC : ∀ s ∈ C, Convex ℝ s) :
    Convex ℝ (⋂₀ C) := convex_sInter hC

/-- **Definition A3.4:** the convex hull is the smallest convex superset. -/
theorem definition_A3_4_convexHull : S ⊆ convexHull ℝ S ∧ Convex ℝ (convexHull ℝ S) ∧
    ∀ T, S ⊆ T → Convex ℝ T → convexHull ℝ S ⊆ T :=
  ⟨subset_convexHull ℝ S, convex_convexHull ℝ S, fun _ h hc => convexHull_min h hc⟩

/-- **Proposition A3.4:** hull membership means being a finite convex combination. -/
theorem proposition_A3_4 {x : E} : x ∈ convexHull ℝ S ↔
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x :=
  mem_convexHull_iff_exists_fintype

/-- **Proposition A3.5 (Carathéodory):** at most dimension plus one points suffice. -/
theorem proposition_A3_5 [FiniteDimensional ℝ E] {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ t : Finset E, (↑t : Set E) ⊆ S ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := AffineIndependent.card_le_finrank_succ
    (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx)
  have hcard : t.card ≤ Module.finrank ℝ
      (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 := by
    simpa only [Fintype.card_coe] using h
  exact hcard.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

variable [TopologicalSpace E]

/-- **Definition A3.4:** the closed convex hull has the closed-and-convex universal property. -/
theorem definition_A3_4_closedConvexHull : S ⊆ closedConvexHull ℝ S ∧
    Convex ℝ (closedConvexHull ℝ S) ∧ IsClosed (closedConvexHull ℝ S) ∧
      ∀ T, S ⊆ T → Convex ℝ T → IsClosed T → closedConvexHull ℝ S ⊆ T :=
  ⟨subset_closedConvexHull, convex_closedConvexHull, isClosed_closedConvexHull,
    fun _ h hc ht => closedConvexHull_min h hc ht⟩

/-- **Proposition A3.7**, first assertion: closure preserves convexity. -/
theorem proposition_A3_7_closure [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : Convex ℝ S) : Convex ℝ (closure S) := hS.closure

/-- **Proposition A3.7**, second assertion: close the convex hull to get the closed convex hull. -/
theorem proposition_A3_7_closedHull [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    closure (convexHull ℝ S) = closedConvexHull ℝ S :=
  closedConvexHull_eq_closure_convexHull.symm

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite transfers preserving coordinate sums

Preparation for Kreps I, Proposition 2.14. On a finite product of real intervals,
any two bundles with the same coordinate sum are joined by finitely many
two-coordinate transfers preserving that sum. An objective invariant under
these elementary transfers is therefore constant on every sum level set.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Taking the numerical values of interval coordinates commutes with coordinate replacement. -/
theorem intervalValues_update [DecidableEq I] (x : ∀ i, S i) (i : I) (a : S i) :
    (fun j => (Function.update x i a j).val) = Function.update (fun j => (x j).val) i a.val := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

/-- Replacing one numerical coordinate changes a finite sum by the difference in its value. -/
theorem sum_interval_update [DecidableEq I] (s : Finset I) (x : ∀ i, S i) {i : I}
    (hi : i ∈ s) (a : S i) :
    (∑ j ∈ s, (Function.update x i a j).val) = (∑ j ∈ s, (x j).val) - (x i).val + a.val := by
  rw [intervalValues_update, Finset.sum_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add s (fun j => (x j).val) hi
  linarith

/-- Unequal finite vectors with the same sum have both a deficit coordinate and a surplus one. -/
theorem finite_sum_opposite_coordinates (s : Finset I) (x y : I → ℝ)
    (hSum : ∑ i ∈ s, x i = ∑ i ∈ s, y i) (hne : ¬∀ i ∈ s, x i = y i) :
    ∃ i ∈ s, ∃ j ∈ s, x i < y i ∧ y j < x j := by
  have hleft : ∃ i ∈ s, x i < y i := by
    by_contra h
    push Not at h
    have he := (Finset.sum_eq_sum_iff_of_le h).mp hSum.symm
    exact hne (fun i hi => (he i hi).symm)
  obtain ⟨i, hi, hix⟩ := hleft
  have hright : ∃ j ∈ s, y j < x j := by
    by_contra h
    push Not at h
    have hlt := Finset.sum_lt_sum h ⟨i, hi, hix⟩
    exact (ne_of_lt hlt) hSum
  obtain ⟨j, hj, hjx⟩ := hright
  exact ⟨i, hi, j, hj, hix, hjx⟩

/-- The elementary two-coordinate transfer invariance needed for the additive construction. -/
def PairSumInvariant [DecidableEq I] (F : (∀ i, S i) → ℝ) : Prop :=
  ∀ (x : ∀ i, S i) (i j : I) (a : S i) (b : S j), i ≠ j →
    a.val + b.val = (x i).val + (x j).val →
      F (Function.update (Function.update x i a) j b) = F x

/-- Equal sums on a finite changing set imply equal utility under pair-transfer invariance. -/
theorem pairSumInvariant_eq_of_sum_eq_on [DecidableEq I] [∀ i, Set.OrdConnected (S i)]
    {F : (∀ i, S i) → ℝ} (hF : PairSumInvariant F) (s : Finset I)
    (x y : ∀ i, S i) (hSum : ∑ i ∈ s, (x i).val = ∑ i ∈ s, (y i).val)
    (hout : ∀ i ∉ s, x i = y i) : F x = F y := by
  induction s using Finset.strongInductionOn generalizing x y with
  | _ s ih =>
    by_cases he : ∀ i ∈ s, (x i).val = (y i).val
    · have hxy : x = y := by
        funext i
        by_cases hi : i ∈ s
        · exact Subtype.ext (he i hi)
        · exact hout i hi
      exact congrArg F hxy
    · obtain ⟨i, hi, j, hj, hix, hjx⟩ :=
        finite_sum_opposite_coordinates s (fun i => (x i).val) (fun i => (y i).val) hSum he
      have hij : i ≠ j := by intro h; subst j; linarith
      let δ := min ((y i).val - (x i).val) ((x j).val - (y j).val)
      have hδ : 0 ≤ δ := le_min (sub_nonneg.mpr hix.le) (sub_nonneg.mpr hjx.le)
      have hδi : δ ≤ (y i).val - (x i).val := min_le_left _ _
      have hδj : δ ≤ (x j).val - (y j).val := min_le_right _ _
      let a : S i := ⟨(x i).val + δ,
        (show Set.OrdConnected (S i) from inferInstance).out (x i).property (y i).property
          ⟨by linarith, by linarith⟩⟩
      let b : S j := ⟨(x j).val - δ,
        (show Set.OrdConnected (S j) from inferInstance).out (y j).property (x j).property
          ⟨by linarith, by linarith⟩⟩
      let z := Function.update (Function.update x i a) j b
      have hzi : z i = a := by simp [z, hij]
      have hzj : z j = b := by simp [z]
      have hzk (k : I) (hki : k ≠ i) (hkj : k ≠ j) : z k = x k := by
        simp only [z, Function.update_of_ne hki, Function.update_of_ne hkj]
      have hsumz : ∑ k ∈ s, (z k).val = ∑ k ∈ s, (y k).val := by
        change (∑ k ∈ s, (Function.update (Function.update x i a) j b k).val) = _
        rw [sum_interval_update s _ hj, sum_interval_update s _ hi,
          Function.update_of_ne hij.symm]
        change (∑ k ∈ s, (x k).val) - (x i).val + ((x i).val + δ) - (x j).val +
          ((x j).val - δ) = _
        linarith
      have hFz : F z = F x := hF x i j a b hij (by dsimp [a, b]; ring)
      have hmatch : ∃ k ∈ s, z k = y k := by
        rcases le_total ((y i).val - (x i).val) ((x j).val - (y j).val) with h | h
        · refine ⟨i, hi, ?_⟩
          rw [hzi]
          apply Subtype.ext
          simp only [a, δ, min_eq_left h]
          ring
        · refine ⟨j, hj, ?_⟩
          rw [hzj]
          apply Subtype.ext
          simp only [b, δ, min_eq_right h]
          ring
      obtain ⟨k, hk, hky⟩ := hmatch
      have hSum' : ∑ m ∈ s.erase k, (z m).val = ∑ m ∈ s.erase k, (y m).val := by
        have hz := Finset.sum_erase_add s (fun m => (z m).val) hk
        have hy := Finset.sum_erase_add s (fun m => (y m).val) hk
        rw [hky] at hz
        linarith
      have hout' (m : I) (hm : m ∉ s.erase k) : z m = y m := by
        by_cases hmk : m = k
        · subst m
          exact hky
        · have hms : m ∉ s := fun h => hm (Finset.mem_erase.mpr ⟨hmk, h⟩)
          have hmi : m ≠ i := fun h => hms (h ▸ hi)
          have hmj : m ≠ j := fun h => hms (h ▸ hj)
          exact (hzk m hmi hmj).trans (hout m hms)
      exact hFz.symm.trans (ih (s.erase k) (Finset.erase_ssubset hk) z y hSum' hout')

/-- On a finite interval product, two bundles with equal total scores have equal utility. -/
theorem pairSumInvariant_eq_of_sum_eq [DecidableEq I] [Fintype I] [∀ i, Set.OrdConnected (S i)]
    {F : (∀ i, S i) → ℝ} (hF : PairSumInvariant F) (x y : ∀ i, S i)
    (hSum : ∑ i, (x i).val = ∑ i, (y i).val) : F x = F y :=
  pairSumInvariant_eq_of_sum_eq_on hF Finset.univ x y hSum (by simp)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local affine coordinates on real intervals

Supporting mathematics for the globalization of additive utility scales in Proposition 2.14.
Affine coefficients that agree locally are constant on a connected interval. Strict increase
provides uniqueness of the coefficients without imposing differentiability on the coordinates.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Near every point of `S`, one coordinate is a positive affine function of another. -/
def LocallyPositiveAffineOn (f g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
    ∃ A B : ℝ, 0 < A ∧ ∀ y ∈ U, f y = A * g y + B

/-- Two affine expressions in an increasing coordinate agree only with equal coefficients. -/
theorem affine_coefficients_unique {S U : Set ℝ} {g : ℝ → ℝ}
    (hg : StrictMonoOn g S) (hU : IsOpen U) (hne : U.Nonempty) (hUS : U ⊆ S)
    {A B C D : ℝ} (he : ∀ x ∈ U, A * g x + B = C * g x + D) :
    A = C ∧ B = D := by
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have hc : c ∈ U := hsub ⟨hac, hcb⟩
  have hd : d ∈ U := hsub ⟨hac.trans hcd, hdb⟩
  have hlt := hg (hUS hc) (hUS hd) hcd
  have hec := he c hc
  have hed := he d hd
  have hAC : A = C := by nlinarith
  exact ⟨hAC, by rw [hAC] at hec; linarith⟩

/-- Positive affine coefficients that exist locally on a nonempty interval exist globally. -/
theorem locallyPositiveAffineOn_global {S : Set ℝ} {f g : ℝ → ℝ}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hg : StrictMonoOn g S)
    (h : LocallyPositiveAffineOn f g S) :
    ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ S, f x = A * g x + B := by
  classical
  choose U hU hxU hUS A B hA he using fun x : S => h x x.property
  let c : S → ℝ × ℝ := fun x => (A x, B x)
  have hlocal : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨Subtype.val ⁻¹' U x, (hU x).preimage continuous_subtype_val, hxU x, ?_⟩
    intro y hy
    have hcoeff := affine_coefficients_unique hg ((hU x).inter (hU y))
      ⟨y, hy, hxU y⟩ (fun _ hz => hUS x hz.1)
      (fun z hz => (he x z hz.1).symm.trans (he y z hz.2))
    exact Prod.ext hcoeff.1.symm hcoeff.2.symm
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  obtain ⟨x, hx⟩ := hne
  refine ⟨A ⟨x, hx⟩, B ⟨x, hx⟩, hA ⟨x, hx⟩, fun y hy => ?_⟩
  have hc := hlocal.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩
  have hAy : A ⟨y, hy⟩ = A ⟨x, hx⟩ := congrArg Prod.fst hc
  have hBy : B ⟨y, hy⟩ = B ⟨x, hx⟩ := congrArg Prod.snd hc
  simpa only [hAy, hBy] using he ⟨y, hy⟩ y (hxU ⟨y, hy⟩)

/-- On an open set, a fixed positive affine relation is in particular a local one. -/
theorem locallyPositiveAffineOn_of_affine {S : Set ℝ} {f g : ℝ → ℝ}
    (hS : IsOpen S) {A B : ℝ} (hA : 0 < A)
    (he : ∀ x ∈ S, f x = A * g x + B) : LocallyPositiveAffineOn f g S :=
  fun _ hx => ⟨S, hS, hx, Subset.rfl, A, B, hA, he⟩

/-- Restricting a local affine relation to an open set preserves it. -/
theorem locallyPositiveAffineOn_mono {S T : Set ℝ} {f g : ℝ → ℝ}
    (h : LocallyPositiveAffineOn f g S) (hT : IsOpen T) (hTS : T ⊆ S) :
    LocallyPositiveAffineOn f g T := by
  intro x hx
  obtain ⟨U, hU, hxU, _, A, B, hA, he⟩ := h x (hTS hx)
  exact ⟨U ∩ T, hU.inter hT, ⟨hxU, hx⟩, inter_subset_right,
    A, B, hA, fun _ hy => he _ hy.1⟩

/-- Increasing functions on two intersecting intervals are increasing on their union. -/
theorem strictMonoOn_union_intervals {S T : Set ℝ} {f : ℝ → ℝ}
    (hS : S.OrdConnected) (hT : T.OrdConnected) (hne : (S ∩ T).Nonempty)
    (hfS : StrictMonoOn f S) (hfT : StrictMonoOn f T) : StrictMonoOn f (S ∪ T) := by
  obtain ⟨c, hcS, hcT⟩ := hne
  have hcross : ∀ x ∈ S, ∀ y ∈ T, x < y → f x < f y := by
    intro x hx y hy hxy
    by_cases hxc : x < c
    · by_cases hcy : c < y
      · exact (hfS hx hcS hxc).trans (hfT hcT hy hcy)
      · have hyS : y ∈ S := hS.out hx hcS ⟨hxy.le, le_of_not_gt hcy⟩
        exact hfS hx hyS hxy
    · have hxT : x ∈ T := hT.out hcT hy ⟨le_of_not_gt hxc, hxy.le⟩
      exact hfT hxT hy hxy
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hfS hx hy hxy
  · exact hcross x hx y hy hxy
  · by_cases hxc : x < c
    · by_cases hcy : c < y
      · exact (hfT hx hcT hxc).trans (hfS hcS hy hcy)
      · exact hfT hx (hT.out hx hcT ⟨hxy.le, le_of_not_gt hcy⟩) hxy
    · exact hfS (hS.out hcS hy ⟨le_of_not_gt hxc, hxy.le⟩) hy hxy
  · exact hfT hx hy hxy

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Global order from local representations along paths

Supporting the global assembly in Proposition 2.14. A finite subdivision of
a path transports local comparisons from one endpoint to the other. This
step does not assume global representability, differentiability, or a
uniform radius for the local charts.
-/

namespace Kreps.PreferenceProperties

open scoped unitInterval

/-- Local comparisons transport along a monotone-score path, including indifference. -/
theorem interval_order_of_local_comparisons {u v : I → ℝ} (hv : Monotone v)
    (hl : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z) :
    u 0 ≤ u 1 ∧ (u 0 = u 1 → v 0 = v 1) := by
  classical
  choose U hU hx hrel using hl
  have hcover : Set.univ ⊆ ⋃ x, U x :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht0, htm, ⟨N, hN⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU hcover
  have hstep (n : ℕ) : u (t n) ≤ u (t (n + 1)) := by
    obtain ⟨i, hi⟩ := htU n
    have hn := htm (Nat.le_succ n)
    exact (hrel i _ (hi ⟨le_rfl, hn⟩) _ (hi ⟨hn, le_rfl⟩)).mpr (hv hn)
  have hum : Monotone (fun n => u (t n)) := monotone_nat_of_le_succ hstep
  have hle : u 0 ≤ u 1 := by
    simpa only [ht0, hN N le_rfl] using hum (Nat.zero_le N)
  refine ⟨hle, fun he => ?_⟩
  have huconst (n : ℕ) : u (t n) = u 0 := by
    apply le_antisymm
    · calc
        u (t n) ≤ u (t (max n N)) := hum (le_max_left _ _)
        _ = u 1 := congrArg u (hN _ (le_max_right _ _))
        _ = u 0 := he.symm
    · simpa only [ht0] using hum (Nat.zero_le n)
  have hvconst (n : ℕ) : v (t n) = v 0 := by
    induction n with
    | zero => rw [ht0]
    | succ n ih =>
      obtain ⟨i, hi⟩ := htU n
      have hn := htm (Nat.le_succ n)
      have hlmem := hi (show t n ∈ Set.Icc (t n) (t (n + 1)) from ⟨le_rfl, hn⟩)
      have hrmem := hi (show t (n + 1) ∈ Set.Icc (t n) (t (n + 1)) from ⟨hn, le_rfl⟩)
      have hvle : v (t (n + 1)) ≤ v (t n) :=
        (hrel i _ hrmem _ hlmem).mp (by rw [huconst, huconst])
      exact (le_antisymm hvle (hv hn)).trans ih
  simpa only [hN N le_rfl] using (hvconst N).symm

/-- A strict endpoint score difference is strict in the locally represented order as well. -/
theorem interval_strict_order_of_local_comparisons {u v : I → ℝ} (hv : Monotone v)
    (hl : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z) (hstrict : v 0 < v 1) :
    u 0 < u 1 := by
  obtain ⟨hle, he⟩ := interval_order_of_local_comparisons hv hl
  exact lt_of_le_of_ne hle (fun h => (ne_of_lt hstrict) (he h))

/-- Continuous paths carry a local comparison cover back to the compact unit interval. -/
theorem path_order_of_local_comparisons {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hl : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z)
    {p : I → X} (hp : Continuous p) (hv : Monotone (v ∘ p)) :
    u (p 0) ≤ u (p 1) ∧ (u (p 0) = u (p 1) → v (p 0) = v (p 1)) := by
  apply interval_order_of_local_comparisons (u := u ∘ p) hv
  intro t
  obtain ⟨U, hU, ht, hrel⟩ := hl (p t)
  exact ⟨p ⁻¹' U, hU.preimage hp, ht, fun _ hs _ hr => hrel _ hs _ hr⟩

/-- Local representation is global when every ordered pair admits a monotone-score path. -/
theorem global_order_of_local_comparisons {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hl : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z)
    (hp : ∀ x y, v x ≤ v y → ∃ p : I → X,
      Continuous p ∧ p 0 = x ∧ p 1 = y ∧ Monotone (v ∘ p)) :
    ∀ x y, u x ≤ u y ↔ v x ≤ v y := by
  have hle (x y : X) (hxy : v x ≤ v y) :
      u x ≤ u y ∧ (u x = u y → v x = v y) := by
    obtain ⟨p, hpc, hp0, hp1, hpm⟩ := hp x y hxy
    simpa only [hp0, hp1] using path_order_of_local_comparisons hl hpc hpm
  intro x y
  constructor
  · intro hxy
    by_contra hvxy
    have hvyx : v y < v x := lt_of_not_ge hvxy
    obtain ⟨huyx, he⟩ := hle y x hvyx.le
    exact (ne_of_lt hvyx) (he (le_antisymm huyx hxy))
  · intro hxy
    exact (hle x y hxy).1

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite additive scales at attained endpoints

Preparation for the boundary cases in Proposition 2.14. Continuity of the
original pair utility and a strict comparison in a companion coordinate
bound the interior additive scale at any attained least or greatest rank.
No boundedness of the constructed cardinal scale is assumed.
-/

namespace Kreps.PreferenceProperties

/-- A least attained rank and one strict companion comparison bound the additive scale below. -/
theorem additive_scale_bddBelow_at_least {X Y : Type*} [Preorder X] [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u : X × Y → ℝ}
    {f : X → ℝ} {g : Y → ℝ} {a : X} (ha : ∀ x, a ≤ x) {b c : Y}
    (hc : Continuous (fun x => u (x, b))) (hm : Monotone (fun x => u (x, c)))
    (hbc : u (a, b) < u (a, c))
    (hr : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f x + g b ≤ f y + g c) :
    BddBelow (f '' D) := by
  have hopen : IsOpen {x | u (x, b) < u (a, c)} := isOpen_lt hc continuous_const
  obtain ⟨x, hx, hux⟩ := hD.exists_mem_open hopen ⟨a, hbc⟩
  refine ⟨f x + g b - g c, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hu : u (x, b) ≤ u (y, c) := hux.le.trans (hm (ha y))
  have := (hr x hx y hy).mp hu
  linarith

/-- A greatest attained rank and one strict companion comparison bound the scale above. -/
theorem additive_scale_bddAbove_at_greatest {X Y : Type*} [Preorder X] [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u : X × Y → ℝ}
    {f : X → ℝ} {g : Y → ℝ} {a : X} (ha : ∀ x, x ≤ a) {b c : Y}
    (hc : Continuous (fun x => u (x, c))) (hm : Monotone (fun x => u (x, b)))
    (hbc : u (a, b) < u (a, c))
    (hr : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f x + g b ≤ f y + g c) :
    BddAbove (f '' D) := by
  have hopen : IsOpen {x | u (a, b) < u (x, c)} := isOpen_lt continuous_const hc
  obtain ⟨x, hx, hux⟩ := hD.exists_mem_open hopen ⟨a, hbc⟩
  refine ⟨f x + g c - g b, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hu : u (y, b) ≤ u (x, c) := (hm (ha y)).trans hux.le
  have := (hr y hy x hx).mp hu
  linarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extending interval scales to attained endpoints

A continuous monotone scale on a dense subset extends continuously when the
only missing points are least or greatest elements and the corresponding
one-sided range is bounded. On a densely ordered domain, strict monotonicity
is preserved. These lemmas supply the endpoint step for Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

open Filter
open scoped Topology

/-- Approaching a missing least element is cofinal in the dense domain's lower end. -/
theorem tendsto_dense_comap_atBot {X : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] {D : Set X} {a : X} (ha : a ∉ D) (hmin : IsBot a) :
    Tendsto (id : D → D) ((𝓝 a).comap ((↑) : D → X)) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have hab : a < (b : X) := lt_of_le_of_ne (hmin b) (fun h => ha (h ▸ b.property))
  have hn : {x : D | (x : X) < (b : X)} ∈ (𝓝 a).comap ((↑) : D → X) :=
    Filter.preimage_mem_comap (Iio_mem_nhds hab)
  exact Filter.mem_of_superset hn (fun _ hx => hx.le)

/-- Approaching a missing greatest element is cofinal in the dense domain's upper end. -/
theorem tendsto_dense_comap_atTop {X : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] {D : Set X} {a : X} (ha : a ∉ D) (hmax : IsTop a) :
    Tendsto (id : D → D) ((𝓝 a).comap ((↑) : D → X)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hab : (b : X) < a := lt_of_le_of_ne (hmax b) (fun h => ha (h ▸ b.property))
  have hn : {x : D | (b : X) < (x : X)} ∈ (𝓝 a).comap ((↑) : D → X) :=
    Filter.preimage_mem_comap (Ioi_mem_nhds hab)
  exact Filter.mem_of_superset hn (fun _ hx => hx.le)

/-- Finite one-sided bounds give a continuous extension across missing extreme points. -/
theorem exists_continuous_endpoint_extension {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    (hedge : ∀ x, x ∉ D → IsBot x ∨ IsTop x) {f : D → ℝ}
    (hf : Continuous f) (hm : Monotone f)
    (hlo : ∀ x, x ∉ D → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x, x ∉ D → IsTop x → BddAbove (Set.range f)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x : D, g x = f x := by
  have hlimit : ∀ x : X, ∃ y : ℝ,
      Tendsto f ((𝓝 x).comap ((↑) : D → X)) (𝓝 y) := by
    intro x
    by_cases hx : x ∈ D
    · refine ⟨f ⟨x, hx⟩, ?_⟩
      rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
      exact hf.continuousAt
    · rcases hedge x hx with hmin | hmax
      · exact ⟨⨅ d, f d, (tendsto_atBot_ciInf hm (hlo x hx hmin)).comp
          (tendsto_dense_comap_atBot hx hmin)⟩
      · exact ⟨⨆ d, f d, (tendsto_atTop_ciSup hm (hhi x hx hmax)).comp
          (tendsto_dense_comap_atTop hx hmax)⟩
  exact ⟨hD.extend f, hD.continuous_extend hlimit, hD.extend_eq hf⟩

/-- A continuous extension of a dense monotone function is below every later dense value. -/
theorem continuous_extension_le_dense {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : Monotone f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) {x : X} {a : D} (hxa : x < (a : X)) :
    g x ≤ f a := by
  by_contra! h
  have hopen : IsOpen {z : X | f a < g z ∧ z < (a : X)} :=
    (isOpen_lt continuous_const hg).inter isOpen_Iio
  obtain ⟨z, hz, hzg, hza⟩ := hD.exists_mem_open hopen ⟨x, h, hxa⟩
  have hmono := hm (show (⟨z, hz⟩ : D) ≤ a from hza.le)
  rw [← heq ⟨z, hz⟩] at hmono
  exact (not_lt_of_ge hmono) hzg

/-- A continuous extension of a dense monotone function is above every earlier dense value. -/
theorem dense_le_continuous_extension {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : Monotone f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) {x : X} {a : D} (hax : (a : X) < x) :
    f a ≤ g x := by
  by_contra! h
  have hopen : IsOpen {z : X | g z < f a ∧ (a : X) < z} :=
    (isOpen_lt hg continuous_const).inter isOpen_Ioi
  obtain ⟨z, hz, hzg, haz⟩ := hD.exists_mem_open hopen ⟨x, h, hax⟩
  have hmono := hm (show a ≤ (⟨z, hz⟩ : D) from haz.le)
  rw [← heq ⟨z, hz⟩] at hmono
  exact (not_lt_of_ge hmono) hzg

/-- A continuous extension of a strictly increasing dense scale stays strictly increasing. -/
theorem continuous_extension_strictMono {X : Type*} [LinearOrder X] [DenselyOrdered X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : StrictMono f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) : StrictMono g := by
  intro x y hxy
  obtain ⟨a, ha, hxa, hay⟩ := hD.exists_between hxy
  obtain ⟨b, hb, hab, hby⟩ := hD.exists_between hay
  have hlo := continuous_extension_le_dense hD hm.monotone hg heq
    (a := ⟨a, ha⟩) hxa
  have hhi := dense_le_continuous_extension hD hm.monotone hg heq
    (a := ⟨b, hb⟩) hby
  exact hlo.trans_lt ((hm (show (⟨a, ha⟩ : D) < ⟨b, hb⟩ from hab)).trans_le hhi)

/-- A dense strict scale extends continuously and strictly across bounded attained endpoints. -/
theorem exists_continuous_strictMono_endpoint_extension {X : Type*} [LinearOrder X]
    [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    (hedge : ∀ x, x ∉ D → IsBot x ∨ IsTop x) {f : D → ℝ}
    (hf : Continuous f) (hm : StrictMono f)
    (hlo : ∀ x, x ∉ D → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x, x ∉ D → IsTop x → BddAbove (Set.range f)) :
    ∃ g : X → ℝ, Continuous g ∧ StrictMono g ∧ ∀ x : D, g x = f x := by
  obtain ⟨g, hg, heq⟩ := exists_continuous_endpoint_extension hD hedge hf hm.monotone hlo hhi
  exact ⟨g, hg, continuous_extension_strictMono hD hm hg heq, heq⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extending utility comparisons from a dense product domain

Continuous strictly increasing utilities on products of densely ordered blocks
represent the same preference if they agree on a dense subset. The perturbation
argument preserves strict comparisons at boundary bundles; continuity alone
would only preserve their weak limits.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Agreement on a dense set transports strict comparisons to weak comparisons everywhere. -/
theorem dense_comparison_strict_implies_le {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y) {x y : X} (hxy : u x < u y) :
    v x ≤ v y := by
  by_contra! h
  have hopen : IsOpen {p : X × X | u p.1 < u p.2 ∧ v p.2 < v p.1} :=
    (isOpen_lt (hu.comp continuous_fst) (hu.comp continuous_snd)).inter
      (isOpen_lt (hv.comp continuous_snd) (hv.comp continuous_fst))
  obtain ⟨⟨a, b⟩, hab, hub, hvb⟩ := (hD.prod hD).exists_mem_open hopen ⟨(x, y), hxy, h⟩
  exact (not_lt_of_ge ((hr a hab.1 b hab.2).mp hub.le)) hvb

/-- There is room for a strict improvement below any higher continuous monotone utility level. -/
theorem exists_product_improvement_below {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {u v : (∀ i, B i) → ℝ} (hu : StrictMono u) (hv : Continuous v) (hvm : Monotone v)
    {x y : ∀ i, B i} (hxy : v x < v y) :
    ∃ z, u x < u z ∧ v z < v y := by
  classical
  have hnot : ¬ y ≤ x := fun h => (not_lt_of_ge (hvm h)) hxy
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hxi : x i < y i := lt_of_not_ge hi
  have hc : Continuous (fun a : B i => v (Function.update x i a)) :=
    hv.comp (continuous_const.update i continuous_id)
  have hn : {a : B i | v (Function.update x i a) < v y} ∈ 𝓝 (x i) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hxy)
  obtain ⟨b, hb, hsub⟩ := exists_Ico_subset_of_mem_nhds hn ⟨y i, hxi⟩
  obtain ⟨a, hxa, hab⟩ := exists_between hb
  have hlt : x < Function.update x i a := by
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simpa using hxa.le
      · simp only [Function.update_of_ne hj, le_refl]
    · intro h
      have hi' := h i
      simp only [Function.update_self] at hi'
      exact (not_le_of_gt hxa) hi'
  exact ⟨Function.update x i a, hu hlt, hsub ⟨hxa.le, hab⟩⟩

/-- Dense agreement preserves strict comparisons on products, including their endpoints. -/
theorem dense_product_strict_comparison {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {D : Set (∀ i, B i)} (hD : Dense D) {u v : (∀ i, B i) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hum : StrictMono u) (hvm : Monotone v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y)
    {x y : ∀ i, B i} (hxy : v x < v y) : u x < u y := by
  have hr' : ∀ x ∈ D, ∀ y ∈ D, v x ≤ v y ↔ u x ≤ u y :=
    fun x hx y hy => (hr x hx y hy).symm
  have hle := dense_comparison_strict_implies_le hD hv hu hr' hxy
  by_contra! hnot
  have heq := le_antisymm hle hnot
  obtain ⟨z, hzu, hzv⟩ := exists_product_improvement_below hum hv hvm hxy
  have hle' := dense_comparison_strict_implies_le hD hv hu hr' hzv
  exact (not_lt_of_ge (hle'.trans_eq heq.symm)) hzu

/-- Continuous strictly increasing product utilities agreeing densely agree everywhere. -/
theorem dense_product_comparison {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {D : Set (∀ i, B i)} (hD : Dense D) {u v : (∀ i, B i) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hum : StrictMono u) (hvm : StrictMono v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y) :
    ∀ x y, u x ≤ u y ↔ v x ≤ v y := by
  intro x y
  constructor
  · intro h
    by_contra! hv'
    exact (not_lt_of_ge h) (dense_product_strict_comparison hD hu hv hum hvm.monotone hr hv')
  · intro h
    by_contra! hu'
    exact (not_lt_of_ge h) (dense_product_strict_comparison hD hv hu hvm hum.monotone
      (fun x hx y hy => (hr x hx y hy).symm) hu')

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Selecting shared essential companions

Three distinct essential coordinates suffice to assign two companions to every target
coordinate, so that every pair of targets shares a companion different from both. This
elementary selection synchronizes the independently continued scales in Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

/-- Three distinct anchors supply two companions per target with a shared companion per pair. -/
theorem exists_shared_companions {I : Type*} {a b c : I}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ first second : I → I,
      (∀ i, first i ≠ i ∧ second i ≠ i ∧ first i ≠ second i) ∧
      ∀ i j, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j ∧
        (k = first i ∨ k = second i) ∧ (k = first j ∨ k = second j) := by
  classical
  let first : I → I := fun i => if i = a then b else a
  let second : I → I := fun i => if i = a ∨ i = b then c else b
  have hc : ∀ i, first i ≠ i ∧ second i ≠ i ∧ first i ≠ second i := by
    intro i
    by_cases hi : i = a
    · subst i
      simp [first, second, hab, hbc, Ne.symm hab, Ne.symm hac]
    · by_cases hib : i = b
      · subst i
        simp [first, second, hab, hac, Ne.symm hab, Ne.symm hbc]
      · simp [first, second, hi, hib, hab, Ne.symm hi, Ne.symm hib]
  refine ⟨first, second, hc, fun i j hij => ?_⟩
  by_cases hi : i = a
  · subst i
    have hja : j ≠ a := Ne.symm hij
    by_cases hjb : j = b
    · subst j
      exact ⟨c, Ne.symm hac, Ne.symm hbc, by simp [second], by simp [second]⟩
    · exact ⟨b, Ne.symm hab, Ne.symm hjb, by simp [first], by simp [second, hja, hjb]⟩
  · by_cases hj : j = a
    · subst j
      by_cases hib : i = b
      · subst i
        exact ⟨c, Ne.symm hbc, Ne.symm hac, by simp [second], by simp [second]⟩
      · exact ⟨b, Ne.symm hib, Ne.symm hab, by simp [second, hi, hib], by simp [first]⟩
    · exact ⟨a, Ne.symm hi, Ne.symm hj, by simp [first, hi], by simp [first, hj]⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Rationalization of choice

Kreps I, §1.2, Propositions 1.3-1.5, pp. 5-7. The alternative space is arbitrary.
Finite nonemptiness does not assert nonemptiness on infinite menus. The final result
therefore preserves the book's disjunction: empty choice or exact rationalization.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- **Proposition 1.3a**, p. 5. Utility induces complete, transitive preference. -/
theorem proposition_1_3a (u : X → ℝ) : Rational (UtilityPref u) := by
  constructor
  · exact fun x y => le_total (u y) (u x)
  · exact fun _ _ _ hxy hyz => le_trans hyz hxy

/-- Finite-set induction supplies a preference maximum without a utility function. -/
theorem prefChoice_finiteNonempty {r : X → X → Prop} (hr : Rational r) :
    FiniteNonempty (PrefChoice r) := by
  intro A hA
  induction A, hA using Set.Finite.induction_on with
  | empty =>
    intro h
    exact (Set.not_nonempty_empty h).elim
  | @insert a s _ _ ih =>
    intro _
    by_cases hn : s.Nonempty
    · obtain ⟨b, hb, hmax⟩ := ih hn
      rcases hr.1 a b with hab | hba
      · refine ⟨a, Set.mem_insert a s, ?_⟩
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hys
        · exact complete_refl hr.1 _
        · exact hr.2 a b y hab (hmax y hys)
      · refine ⟨b, Set.mem_insert_of_mem a hb, ?_⟩
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hys
        · exact hba
        · exact hmax y hys
    · have hs : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      subst s
      refine ⟨a, by simp, ?_⟩
      intro y hy
      have hy' : y = a := by simpa using hy
      subst y
      exact complete_refl hr.1 a

/-- Transitivity alone suffices for coherence of preference maximization. -/
theorem prefChoice_coherent {r : X → X → Prop} (ht : TransitivePref r) :
    Coherent (PrefChoice r) := by
  intro A B x hx y hy hxc hyc hyB
  apply hyc
  exact ⟨hy.1, fun z hz => ht y x z (hyB.2 x hx.2) (hxc.2 z hz)⟩

/-- **Proposition 1.3b**, p. 5. Utility choice is finite-nonempty and coherent. -/
theorem proposition_1_3b (u : X → ℝ) :
    FiniteNonempty (UtilityChoice u) ∧ Coherent (UtilityChoice u) :=
  ⟨prefChoice_finiteNonempty (proposition_1_3a u),
    prefChoice_coherent (proposition_1_3a u).2⟩

/-- **Proposition 1.4**, pp. 5-6. Rational preference generates coherent choice. -/
theorem proposition_1_4 {r : X → X → Prop} (hr : Rational r) :
    FiniteNonempty (PrefChoice r) ∧ Coherent (PrefChoice r) :=
  ⟨prefChoice_finiteNonempty hr, prefChoice_coherent hr.2⟩

/-- The symmetric formulation of coherence in the footnote on p. 4. -/
theorem coherent_exchange {c : ChoiceRule X} (hc : Coherent c)
    {A B : Set X} {x y : X} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B)
    (hxc : x ∈ c A) (hyc : y ∈ c B) : x ∈ c B ∧ y ∈ c A := by
  constructor
  · by_contra h
    exact hc B A y ⟨hy.2, hy.1⟩ x ⟨hx.2, hx.1⟩ hyc h hxc
  · by_contra h
    exact hc A B x hx y hy hxc h hyc

/-- A chosen alternative wins every feasible pairwise comparison. -/
theorem revealed_of_chosen {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X} {x y : X}
    (hx : x ∈ c A) (hy : y ∈ A) : Revealed c x y := by
  obtain ⟨z, hz⟩ := hn {x, y} (by simp) (by simp)
  have hzmem : z ∈ ({x, y} : Set X) := hf _ hz
  have hzA : z ∈ A := by
    rcases Set.mem_insert_iff.mp hzmem with rfl | hz'
    · exact hf A hx
    · simpa only [Set.mem_singleton_iff.mp hz'] using hy
  exact (coherent_exchange hc ⟨hf A hx, by simp⟩ ⟨hzA, hzmem⟩ hx hz).1

/-- A revealed weak improvement on a chosen alternative is also chosen. -/
theorem chosen_of_revealed {c : ChoiceRule X} (hc : Coherent c)
    {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : Revealed c x y) (hyc : y ∈ c A) : x ∈ c A :=
  (coherent_exchange hc ⟨by simp, hx⟩ ⟨by simp, hy⟩ hxy hyc).1

/-- Pairwise nonemptiness makes revealed preference complete. -/
theorem revealed_complete {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) : Complete (Revealed c) := by
  intro x y
  obtain ⟨z, hz⟩ := hn {x, y} (by simp) (by simp)
  rcases Set.mem_insert_iff.mp (hf _ hz) with rfl | hz'
  · exact Or.inl hz
  · have hz' : z = y := Set.mem_singleton_iff.mp hz'
    subst z
    right
    simpa only [Revealed, Set.pair_comm y x] using hz

/-- Coherence and finite nonemptiness make revealed preference transitive. -/
theorem revealed_transitive {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) : TransitivePref (Revealed c) := by
  intro x y z hxy hyz
  obtain ⟨w, hw⟩ := hn {x, y, z} (by simp) (by simp)
  have hx : x ∈ c {x, y, z} := by
    have hwmem := hf {x, y, z} hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with hwx | hwy | hwz
    · subst w
      exact hw
    · subst w
      exact chosen_of_revealed hc (by simp) (by simp) hxy hw
    · subst w
      have hy : y ∈ c {x, y, z} :=
        chosen_of_revealed hc (by simp) (by simp) hyz hw
      exact chosen_of_revealed hc (by simp) (by simp) hxy hy
  exact revealed_of_chosen hf hn hc hx (by simp)

/-- Nonempty choice agrees exactly with maximization of revealed preference. -/
theorem choice_eq_revealed_of_nonempty {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X} (hA : (c A).Nonempty) :
    c A = PrefChoice (Revealed c) A := by
  ext x
  constructor
  · intro hx
    exact ⟨hf A hx, fun y hy => revealed_of_chosen hf hn hc hx hy⟩
  · rintro ⟨hx, hmax⟩
    obtain ⟨y, hy⟩ := hA
    exact chosen_of_revealed hc hx (hf A hy) (hmax y (hf A hy)) hy

/-- **Proposition 1.5**, pp. 6-7, including the infinite-menu exception. -/
theorem proposition_1_5 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    Rational (Revealed c) ∧
      FiniteNonempty (PrefChoice (Revealed c)) ∧ Coherent (PrefChoice (Revealed c)) ∧
      ∀ A, c A = ∅ ∨ c A = PrefChoice (Revealed c) A := by
  have hr : Rational (Revealed c) :=
    ⟨revealed_complete hf hn, revealed_transitive hf hn hc⟩
  refine ⟨hr, (proposition_1_4 hr).1, (proposition_1_4 hr).2, ?_⟩
  intro A
  rcases (c A).eq_empty_or_nonempty with hA | hA
  · exact Or.inl hA
  · exact Or.inr (choice_eq_revealed_of_nonempty hf hn hc hA)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Strict preference and indifference

Kreps I, §1.4, Propositions 1.9-1.10, pp. 9-10, and Problem 1.9, p. 26.
The two presentations of rational preference are equivalent: complete, transitive
weak preference, or asymmetric, negatively transitive strict preference.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- A strict preference cannot run both ways. -/
def AsymmetricPref (s : X → X → Prop) : Prop := ∀ x y, s x y → ¬s y x

/-- The book's disjunctive formulation of negative transitivity. -/
def NegativelyTransitive (s : X → X → Prop) : Prop :=
  ∀ x y z, s x y → s z y ∨ s x z

/-- Recover weak preference by denying the reversed strict preference. -/
def WeakFromStrict (s : X → X → Prop) (x y : X) : Prop := ¬s y x

/-- Recover indifference when neither strict comparison holds. -/
def IndifferenceFromStrict (s : X → X → Prop) (x y : X) : Prop :=
  ¬s x y ∧ ¬s y x

/-- **Proposition 1.9a**, p. 9. -/
theorem proposition_1_9a (hc : Complete r) (x y : X) : Strict r x y ↔ ¬r y x :=
  ⟨And.right, fun h => ⟨(hc x y).resolve_right h, h⟩⟩

/-- **Proposition 1.9b**, p. 9. No completeness assumption is needed. -/
theorem proposition_1_9b (r : X → X → Prop) : AsymmetricPref (Strict r) :=
  fun _ _ hxy hyx => hxy.2 hyx.1

/-- First half of **Proposition 1.9g**, p. 9. -/
theorem strict_weak_trans (ht : TransitivePref r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨ht x y z hxy.1 hyz, fun hzx => hxy.2 (ht y z x hyz hzx)⟩

/-- Second half of **Proposition 1.9g**, p. 9. -/
theorem weak_strict_trans (ht : TransitivePref r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨ht x y z hxy hyz.1, fun hzx => hyz.2 (ht z x y hzx hxy)⟩

/-- **Proposition 1.9c**, p. 9. -/
theorem proposition_1_9c (hr : Rational r) : NegativelyTransitive (Strict r) := by
  intro x y z hxy
  by_cases hzy : Strict r z y
  · exact Or.inl hzy
  · right
    have hyz : r y z := by
      by_contra h
      exact hzy ((proposition_1_9a hr.1 z y).mpr h)
    exact strict_weak_trans hr.2 hxy hyz

/-- **Proposition 1.9d**, p. 9: reflexivity of indifference. -/
theorem proposition_1_9d (hc : Complete r) (x : X) : Indifferent r x x :=
  ⟨complete_refl hc x, complete_refl hc x⟩

/-- **Proposition 1.9e**, p. 9: symmetry of indifference. -/
theorem proposition_1_9e {x y : X} (hxy : Indifferent r x y) : Indifferent r y x :=
  ⟨hxy.2, hxy.1⟩

/-- **Proposition 1.9f**, p. 9: transitivity of indifference. -/
theorem proposition_1_9f (ht : TransitivePref r) {x y z : X}
    (hxy : Indifferent r x y) (hyz : Indifferent r y z) : Indifferent r x z :=
  ⟨ht x y z hxy.1 hyz.1, ht z y x hyz.2 hxy.2⟩

/-- **Proposition 1.9g**, p. 9: both mixed transitivity statements. -/
theorem proposition_1_9g (ht : TransitivePref r) (x y z : X) :
    (Strict r x y → r y z → Strict r x z) ∧
      (r x y → Strict r y z → Strict r x z) :=
  ⟨fun hxy hyz => strict_weak_trans ht hxy hyz,
    fun hxy hyz => weak_strict_trans ht hxy hyz⟩

/-- **Proposition 1.9h**, p. 9: transitivity of strict preference. -/
theorem proposition_1_9h (ht : TransitivePref r) : TransitivePref (Strict r) :=
  fun _ _ _ hxy hyz => strict_weak_trans ht hxy hyz.1

/-- **Proposition 1.10**, p. 10: reconstruction, including both recovered relations. -/
theorem proposition_1_10 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    by_cases h : s y x
    · exact Or.inr (ha y x h)
    · exact Or.inl h
  · intro x y z hxy hyz hzx
    exact (hn z x y hzx).elim hxy hyz
  · funext x y
    apply propext
    change (¬s y x ∧ ¬¬s x y) ↔ s x y
    exact ⟨fun h => not_not.mp h.2, fun h => ⟨ha x y h, not_not.mpr h⟩⟩
  · funext x y
    exact propext and_comm

/-- **Problem 1.9**, p. 26: the reconstructed weak relation is complete and transitive. -/
theorem problem_1_9 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s :=
  proposition_1_10 ha hn

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: semicontinuity and compact maximization

Definition A2.24 and Proposition A2.26, p. 451. The final diagnostic exercise
requires a correction: absolute summability alone does not imply upper
semicontinuity for signed coefficients. Nonnegative coefficients do suffice.
A single negative coefficient on the closed set `{0}` disproves the printed claim.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- **Definition A2.24:** the book's non-strict epsilon formulation of upper semicontinuity. -/
theorem definition_A2_24_upper {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt f x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → f y ≤ f x + ε := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (h (f x + ε) (by linarith))
    exact ⟨δ, hδ, fun y hy => (hnear hy).le⟩
  · intro h b hb
    obtain ⟨δ, hδ, hnear⟩ := h ((b - f x) / 2) (by linarith)
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear y hy
    linarith

/-- **Definition A2.24:** the corresponding lower-semicontinuity formulation. -/
theorem definition_A2_24_lower {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt f x ↔
      ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → f x ≤ f y + ε := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (h (f x - ε) (by linarith))
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear hy
    linarith
  · intro h a ha
    obtain ⟨δ, hδ, hnear⟩ := h ((f x - a) / 2) (by linarith)
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hbound := hnear y hy
    linarith

/-- **Proposition A2.26:** an upper semicontinuous function attains its finite supremum. -/
theorem proposition_A2_26 {X : Type*} [TopologicalSpace X] {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : UpperSemicontinuousOn f K) :
    ∃ x ∈ K, f x = sSup (f '' K) ∧ ∀ y ∈ K, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne hK hf
  have hg : IsGreatest (f '' K) (f x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨x, hx, hg.csSup_eq.symm, hmax⟩

/-- The economic consequence on p. 451: upper semicontinuous utility gives compact-menu choice. -/
theorem upperSemicontinuous_compact_choice {X : Type*} [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} {K : Set X}
    (hu : Represents u r) (hK : IsCompact K) (hne : K.Nonempty)
    (hc : UpperSemicontinuousOn u K) : (PrefChoice r K).Nonempty := by
  obtain ⟨x, hx, _, hmax⟩ := proposition_A2_26 hK hne hc
  exact ⟨x, hx, fun y hy => (hu x y).mpr (hmax y hy)⟩

/-- The weighted closed-set indicator series from the final diagnostic exercise. -/
noncomputable def ClosedIndicatorSeries {X : Type*} (C : ℕ → Set X) (w : ℕ → ℝ)
    (x : X) : ℝ := ∑' n, (C n).indicator (fun _ => w n) x

/-- The diagnostic claim is valid when its absolutely summable coefficients are nonnegative. -/
theorem appendix2_diagnostic_nonnegative {X : Type*} [TopologicalSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable (fun n => |w n|)) :
    UpperSemicontinuous (ClosedIndicatorSeries C w) := by
  apply upperSemicontinuous_tsum_of_norm_le hs
  · intro n
    exact (hC n).upperSemicontinuous_indicator (hw n)
  · intro n x
    simpa only [Real.norm_eq_abs] using
      norm_indicator_le_norm_self (s := C n) (fun _ => w n) x

/-- A single negative coefficient; all later coefficients vanish. -/
def DiagnosticNegativeWeights (n : ℕ) : ℝ := if n = 0 then -1 else 0

/-- The closed sets in the counterexample can all be the same singleton. -/
def DiagnosticClosedSets (_ : ℕ) : Set ℝ := {0}

/-- The counterexample satisfies the printed absolute-summability hypothesis. -/
theorem diagnosticNegativeWeights_summable :
    Summable (fun n => |DiagnosticNegativeWeights n|) := by
  have he : (fun n => |DiagnosticNegativeWeights n|) =
      fun n : ℕ => if n = 0 then 1 else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [DiagnosticNegativeWeights, hn]
  rw [he]
  exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable

/-- Its indicator sum is negative at zero and vanishes elsewhere. -/
theorem diagnosticNegative_formula (x : ℝ) :
    ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights x =
      if x = 0 then -1 else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [ClosedIndicatorSeries, DiagnosticClosedSets, DiagnosticNegativeWeights]
  · simp [ClosedIndicatorSeries, DiagnosticClosedSets, hx]

/-- The printed signed-coefficient diagnostic fails already at the origin of the real line. -/
theorem diagnosticNegative_not_upperSemicontinuousAt :
    ¬ UpperSemicontinuousAt
      (ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights) 0 := by
  intro h
  have hnear := h (-1 / 2) (by
    change ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights 0 < -1 / 2
    rw [diagnosticNegative_formula]
    norm_num)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := (hlim.eventually hnear).exists
  rw [diagnosticNegative_formula, ite_eq_right (ne_of_gt (pow_pos (by norm_num) n))] at hn
  norm_num at hn

/-- A formal counterexample to the final diagnostic as printed, with all its stated hypotheses. -/
theorem appendix2_diagnostic_counterexample :
    (∀ n, IsClosed (DiagnosticClosedSets n)) ∧
      Summable (fun n => |DiagnosticNegativeWeights n|) ∧
      ¬ UpperSemicontinuous
        (ClosedIndicatorSeries DiagnosticClosedSets DiagnosticNegativeWeights) := by
  exact ⟨fun _ => isClosed_singleton, diagnosticNegativeWeights_summable,
    fun h => diagnosticNegative_not_upperSemicontinuousAt (h 0)⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: sequences, accumulation and compactness

Definitions A2.6 and A2.9–A2.13, Propositions A2.7–A2.8 and A2.12, and
Corollary A2.14, pp. 445–447. Sequence indices start at zero. Accumulation uses
arbitrarily late visits to neighborhoods, so repeated values are allowed.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- **Definition A2.6:** convergence is eventual closeness for every positive epsilon. -/
theorem definition_A2_6 {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (x : X) :
    Filter.Tendsto u Filter.atTop (𝓝 x) ↔
      ∀ ε > 0, ∃ N, ∀ n > N, dist (u n) x < ε := Metric.tendsto_atTop'

/-- **Proposition A2.7:** openness means eventual membership for convergent sequences. -/
theorem proposition_A2_7 {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∀ u : ℕ → X, Filter.Tendsto u Filter.atTop (𝓝 x) →
      ∃ N, ∀ n ≥ N, u n ∈ S := by
  constructor
  · intro hS x hx u hu
    exact Filter.eventually_atTop.mp (hu.eventually (hS.mem_nhds hx))
  · intro h
    apply isClosed_compl_iff.mp
    apply IsSeqClosed.isClosed
    intro u x hu hlim hx
    obtain ⟨N, hN⟩ := h x hx u hlim
    exact hu N (hN N le_rfl)

/-- **Proposition A2.8:** a set is closed exactly when it contains all its sequential limits. -/
theorem proposition_A2_8 {X : Type*} [PseudoMetricSpace X] (S : Set X) :
    IsClosed S ↔ ∀ u : ℕ → X, ∀ x, (∀ n, u n ∈ S) →
      Filter.Tendsto u Filter.atTop (𝓝 x) → x ∈ S := by
  constructor
  · intro h u x hu hlim
    exact h.mem_of_tendsto hlim (Filter.Eventually.of_forall hu)
  · intro h
    exact IsSeqClosed.isClosed (fun u x hu hlim => h u x hu hlim)

/-- **Definition A2.9:** accumulation means returning arbitrarily late to every neighborhood. -/
theorem definition_A2_9 {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔
      ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, dist (u n) x < ε := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [Filter.frequently_atTop, Metric.mem_ball]

/-- The printed definition uses a strictly later index, giving the same accumulation criterion. -/
theorem appendix2_accumulation_strict_index {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔
      ∀ ε > 0, ∀ N : ℕ, ∃ n > N, dist (u n) x < ε := by
  rw [definition_A2_9]
  constructor
  · intro h ε hε N
    obtain ⟨n, hn, hx⟩ := h ε hε (N + 1)
    exact ⟨n, by omega, hx⟩
  · intro h ε hε N
    obtain ⟨n, hn, hx⟩ := h ε hε N
    exact ⟨n, hn.le, hx⟩

/-- **Definition A2.10** and its exercise: accumulation means a convergent subsequence exists. -/
theorem appendix2_accumulation_subsequence {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (x : X) :
    MapClusterPt x Filter.atTop u ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  constructor
  · exact MapClusterPt.tendsto_subseq
  · rintro ⟨φ, hφ, hlim⟩
    exact MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt

/-- The sequential description of closure on p. 446, allowing constant sequences. -/
theorem appendix2_closure_sequence {X : Type*} [PseudoMetricSpace X] (S : Set X) (x : X) :
    x ∈ closure S ↔ ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      Filter.Tendsto u Filter.atTop (𝓝 x) := mem_closure_iff_seq_limit

/-- The book's set-accumulation convention includes every point of the set itself. -/
theorem appendix2_set_accumulation_self {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {x : X} (hx : x ∈ S) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ MapClusterPt x Filter.atTop u :=
  ⟨fun _ => x, fun _ => hx, tendsto_const_nhds.mapClusterPt⟩

/-- **Definition A2.11:** boundedness means a strict uniform bound on norms. -/
theorem definition_A2_11 {E : Type*} [NormedAddCommGroup E] (S : Set E) :
    Bornology.IsBounded S ↔ ∃ M > 0, ∀ x ∈ S, ‖x‖ < M := by
  constructor
  · intro h
    obtain ⟨M, hM, hbound⟩ := h.exists_pos_norm_le
    refine ⟨M + 1, by linarith, fun x hx => ?_⟩
    have hb := hbound x hx
    linarith
  · rintro ⟨M, _, hbound⟩
    exact isBounded_iff_forall_norm_le.mpr ⟨M, fun x hx => (hbound x hx).le⟩

/-- **Proposition A2.12:** a bounded Euclidean sequence has an accumulation point. -/
theorem proposition_A2_12 {k : ℕ} (u : ℕ → CommodityEuclidean k)
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ x ∈ closure (Set.range u), MapClusterPt x Filter.atTop u := by
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hu.isCompact_closure.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨x, hx, (appendix2_accumulation_subsequence u x).mpr ⟨φ, hφ, hlim⟩⟩

/-- The Cauchy criterion stated before Definition A2.13. -/
theorem appendix2_cauchy_criterion {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

/-- Euclidean space is complete: every Cauchy sequence has a finite Euclidean limit. -/
theorem appendix2_euclidean_complete {k : ℕ} (u : ℕ → CommodityEuclidean k)
    (hu : CauchySeq u) : ∃ x, Filter.Tendsto u Filter.atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

/-- **Definition A2.13:** Euclidean compactness is equivalent to closedness and boundedness. -/
theorem definition_A2_13 {k : ℕ} (S : Set (CommodityEuclidean k)) :
    IsCompact S ↔ IsClosed S ∧ Bornology.IsBounded S := Metric.isCompact_iff_isClosed_bounded

/-- **Corollary A2.14:** a compact sequence has accumulation points, all inside its compact set. -/
theorem corollary_A2_14 {X : Type*} [MetricSpace X] {S : Set X} (hS : IsCompact S)
    (u : ℕ → X) (hu : ∀ n, u n ∈ S) :
    (∃ x, MapClusterPt x Filter.atTop u) ∧
      ∀ x, MapClusterPt x Filter.atTop u → x ∈ S := by
  obtain ⟨x, _, φ, hφ, hlim⟩ := hS.tendsto_subseq hu
  refine ⟨⟨x, (appendix2_accumulation_subsequence u x).mpr ⟨φ, hφ, hlim⟩⟩, ?_⟩
  intro y hy
  exact hS.isClosed.mem_of_mapClusterPt hy (Filter.Eventually.of_forall hu)

/-- The finite-set compactness remark on p. 447. -/
theorem appendix2_finite_compact {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : S.Finite) : IsCompact S := hS.isCompact

/-- The open-cover characterization discussed after Corollary A2.14. -/
theorem appendix2_compact_open_cover {X : Type} [TopologicalSpace X] (S : Set X) :
    IsCompact S ↔ ∀ {ι : Type} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      S ⊆ ⋃ i, U i → ∃ F : Finset ι, S ⊆ ⋃ i ∈ F, U i :=
  isCompact_iff_finite_subcover

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Density of bisymmetric mean grids

On a compact ordered interval the dyadic mean grid is dense. Its closure is
closed under the continuous mean; any gap in that closure would contain the
mean of its two boundary points, contradicting strict internality.
-/

namespace Kreps.PreferenceProperties

open Set

variable {α : Type*} [LinearOrder α] [TopologicalSpace α]

/-- Continuity preserves closure under the mean. -/
theorem meanDyadicPoints_closure_mean (M : OrderedBisymmetricMean α) (a b : α)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) {x y : α}
    (hx : x ∈ closure (MeanDyadicPoints M a b))
    (hy : y ∈ closure (MeanDyadicPoints M a b)) :
    M.mean x y ∈ closure (MeanDyadicPoints M a b) := by
  have hm : MapsTo (fun p : α × α => M.mean p.1 p.2)
      (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) (MeanDyadicPoints M a b) :=
    fun _ hp => meanDyadicPoints_mean M a b hp.1 hp.2
  exact hm.closure hc (show (x, y) ∈ closure
    (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) from
    by simpa only [closure_prod_eq, mem_prod] using And.intro hx hy)

/-- A continuous strict bisymmetric mean has a dense dyadic grid on a compact interval. -/
theorem meanDyadicPoints_dense [OrderTopology α] [CompactSpace α]
    (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) :
    Dense (MeanDyadicPoints M a b) := by
  intro x
  have hleft : a ∈ closure (MeanDyadicPoints M a b) :=
    subset_closure ⟨0, 0, by norm_num, (meanDyadicGrid_left M a b 0).symm⟩
  have hright : b ∈ closure (MeanDyadicPoints M a b) :=
    subset_closure ⟨0, 1, by norm_num, (meanDyadicGrid_right M a b 0).symm⟩
  have hloClosed : IsClosed (closure (MeanDyadicPoints M a b) ∩ Iic x) :=
    isClosed_closure.inter isClosed_Iic
  have hhiClosed : IsClosed (closure (MeanDyadicPoints M a b) ∩ Ici x) :=
    isClosed_closure.inter isClosed_Ici
  obtain ⟨l, hl⟩ := hloClosed.isCompact.exists_isGreatest ⟨a, hleft, ha x⟩
  obtain ⟨r, hr⟩ := hhiClosed.isCompact.exists_isLeast ⟨b, hright, hb x⟩
  by_contra hx
  have hlx : l < x := lt_of_le_of_ne hl.1.2 (fun h => hx (h ▸ hl.1.1))
  have hxr : x < r := lt_of_le_of_ne hr.1.2 (fun h => hx (h.symm ▸ hr.1.1))
  have hbetween := orderedMean_between M (hlx.trans hxr)
  have hm := meanDyadicPoints_closure_mean M a b hc hl.1.1 hr.1.1
  rcases le_total (M.mean l r) x with h | h
  · exact (not_le_of_gt hbetween.1) (hl.2 ⟨hm, h⟩)
  · exact (not_le_of_gt hbetween.2) (hr.2 ⟨hm, h⟩)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The diagonal-inverse utility mean

Preparation for Kreps I, Proposition 2.14. A continuous utility that increases
strictly in both coordinates defines a unique mean: its diagonal value equals
the utility of the two inputs. The mean is continuous and strictly increasing.
A partial medial identity for the surrounding utility operation makes the
mean bisymmetric, without assuming a cardinal representation.
-/

namespace Kreps.PreferenceProperties

variable {A : Type*} {F : A → A → ℝ}

/-- A utility strictly increasing in both coordinates has a strictly increasing diagonal. -/
theorem utilityDiagonal_strictMono [LinearOrder A] (hl : ∀ y, StrictMono (fun x => F x y))
    (hr : ∀ x, StrictMono (F x)) : StrictMono (fun x => F x x) := by
  intro x y hxy
  exact (hl x hxy).trans (hr y hxy)

/-- Connectedness makes every pair's utility value attainable on the diagonal. -/
theorem utilityDiagonal_attains_pair [LinearOrder A] [TopologicalSpace A] [PreconnectedSpace A]
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hc : Continuous (fun x => F x x)) (x y : A) : ∃ z, F z z = F x y := by
  have hI := (isPreconnected_range hc).ordConnected
  rcases le_total x y with hxy | hyx
  · exact hI.out ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨(hr x).monotone hxy, (hl y).monotone hxy⟩
  · exact hI.out ⟨y, rfl⟩ ⟨x, rfl⟩ ⟨(hl y).monotone hyx, (hr x).monotone hyx⟩

/-- The unique equal-coordinate bundle with the same utility as the input pair. -/
noncomputable def DiagonalUtilityMean (F : A → A → ℝ)
    (he : ∀ x y, ∃ z, F z z = F x y) (x y : A) : A := Classical.choose (he x y)

/-- The defining indifference equation for the diagonal mean. -/
theorem diagonalUtilityMean_spec (he : ∀ x y, ∃ z, F z z = F x y) (x y : A) :
    F (DiagonalUtilityMean F he x y) (DiagonalUtilityMean F he x y) = F x y :=
  Classical.choose_spec (he x y)

/-- Equal inputs are fixed by the diagonal mean. -/
theorem diagonalUtilityMean_reflexive (he : ∀ x y, ∃ z, F z z = F x y)
    (hd : Function.Injective (fun x => F x x)) (x : A) :
    DiagonalUtilityMean F he x x = x := hd (diagonalUtilityMean_spec he x x)

/-- A symmetric pair utility induces a symmetric diagonal mean. -/
theorem diagonalUtilityMean_symmetric (he : ∀ x y, ∃ z, F z z = F x y)
    (hd : Function.Injective (fun x => F x x)) (hs : ∀ x y, F x y = F y x) (x y : A) :
    DiagonalUtilityMean F he x y = DiagonalUtilityMean F he y x := by
  apply hd
  change F (DiagonalUtilityMean F he x y) (DiagonalUtilityMean F he x y) =
    F (DiagonalUtilityMean F he y x) (DiagonalUtilityMean F he y x)
  rw [diagonalUtilityMean_spec he x y, diagonalUtilityMean_spec he y x, hs]

/-- The mean is strictly increasing in its first coordinate. -/
theorem diagonalUtilityMean_strictMono_left [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x)) (y : A) :
    StrictMono (fun x => DiagonalUtilityMean F he x y) := by
  intro x z hxz
  apply (utilityDiagonal_strictMono hl hr).lt_iff_lt.mp
  simpa only [diagonalUtilityMean_spec] using hl y hxz

/-- The mean is strictly increasing in its second coordinate. -/
theorem diagonalUtilityMean_strictMono_right [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x)) (x : A) :
    StrictMono (DiagonalUtilityMean F he x) := by
  intro y z hyz
  apply (utilityDiagonal_strictMono hl hr).lt_iff_lt.mp
  simpa only [diagonalUtilityMean_spec] using hr x hyz

/-- Comparing pair utilities is equivalent to comparing their diagonal means. -/
theorem diagonalUtilityMean_comparison [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (a b c d : A) :
    F a b ≤ F c d ↔ DiagonalUtilityMean F he a b ≤ DiagonalUtilityMean F he c d := by
  rw [← diagonalUtilityMean_spec he a b, ← diagonalUtilityMean_spec he c d]
  exact (utilityDiagonal_strictMono hl hr).le_iff_le

/-- The inverse diagonal is continuous on its attained interval, so the mean is continuous. -/
theorem diagonalUtilityMean_continuous [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
    [PreconnectedSpace A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hc : Continuous (fun p : A × A => F p.1 p.2)) :
    Continuous (fun p : A × A => DiagonalUtilityMean F he p.1 p.2) := by
  have hd := utilityDiagonal_strictMono hl hr
  have hdc : Continuous (fun x => F x x) := hc.comp (continuous_id.prodMk continuous_id)
  let : Set.OrdConnected (Set.range (fun x => F x x)) := (isPreconnected_range hdc).ordConnected
  let e : A ≃o Set.range (fun x => F x x) := hd.orderIso (fun x => F x x)
  have hg : Continuous (fun p : A × A =>
      (⟨F p.1 p.2, he p.1 p.2⟩ : Set.range (fun x => F x x))) := hc.subtype_mk _
  convert e.symm.continuous.comp hg using 1
  funext p
  apply e.injective
  change e (DiagonalUtilityMean F he p.1 p.2) =
    e (e.symm ⟨F p.1 p.2, by exact he p.1 p.2⟩)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact diagonalUtilityMean_spec he p.1 p.2

/-- A numerical operation has the medial identity wherever its four intermediate values exist. -/
def PartialUtilityMedial {B : Type*} (G : B → B → ℝ) (f : B → ℝ) : Prop :=
  ∀ a b c d p q s t, G a b = f p → G c d = f q → G a c = f s → G b d = f t →
    G p q = G s t

/-- The partial medial identity of the surrounding operation gives a bisymmetric diagonal mean. -/
theorem diagonalUtilityMean_bisymmetric {B : Type*} (G : B → B → ℝ) (f : B → ℝ)
    (k : A → B) (he : ∀ x y, ∃ z, F z z = F x y)
    (hF : ∀ x y, F x y = G (k x) (k y))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p))
    (hdF : Function.Injective (fun x => F x x)) (a b c d : A) :
    DiagonalUtilityMean F he (DiagonalUtilityMean F he a b) (DiagonalUtilityMean F he c d) =
      DiagonalUtilityMean F he (DiagonalUtilityMean F he a c) (DiagonalUtilityMean F he b d) := by
  let M := DiagonalUtilityMean F he
  obtain ⟨p, hp⟩ := hsmall a b
  obtain ⟨q, hq⟩ := hsmall c d
  obtain ⟨s, hs⟩ := hsmall a c
  obtain ⟨t, ht⟩ := hsmall b d
  obtain ⟨v, hv⟩ := hsmall (M a b) (M c d)
  obtain ⟨w, hw⟩ := hsmall (M a c) (M b d)
  have hdiag (x y : A) : G (k (M x y)) (k (M x y)) = G (k x) (k y) := by
    rw [← hF, ← hF]
    exact diagonalUtilityMean_spec he x y
  have hvw : v = w := by
    apply hd
    calc
      G v v = G p q := hmed (k (M a b)) (k (M c d)) (k (M a b)) (k (M c d))
        v v p q hv hv ((hdiag a b).trans hp) ((hdiag c d).trans hq)
      _ = G s t := hmed (k a) (k b) (k c) (k d) p q s t hp hq hs ht
      _ = G w w := (hmed (k (M a c)) (k (M b d)) (k (M a c)) (k (M b d))
        w w s t hw hw ((hdiag a c).trans hs) ((hdiag b d).trans ht)).symm
  apply hdF
  change F (M (M a b) (M c d)) (M (M a b) (M c d)) =
    F (M (M a c) (M b d)) (M (M a c) (M b d))
  rw [diagonalUtilityMean_spec he (M a b) (M c d),
    diagonalUtilityMean_spec he (M a c) (M b d), hF, hF, hv, hw, hvw]

/-- Package the derived diagonal mean for the dyadic cardinal-scale construction. -/
noncomputable def OrderedUtilityMean [LinearOrder A] {B : Type*} (G : B → B → ℝ) (f : B → ℝ)
    (k : A → B) (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hs : ∀ x y, F x y = F y x) (hF : ∀ x y, F x y = G (k x) (k y))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p)) :
    OrderedBisymmetricMean A where
  mean := DiagonalUtilityMean F he
  reflexive := diagonalUtilityMean_reflexive he (utilityDiagonal_strictMono hl hr).injective
  symmetric := diagonalUtilityMean_symmetric he (utilityDiagonal_strictMono hl hr).injective hs
  bisymmetric := diagonalUtilityMean_bisymmetric G f k he hF hsmall hmed hd
    (utilityDiagonal_strictMono hl hr).injective
  strictMono_left := diagonalUtilityMean_strictMono_left he hl hr
  strictMono_right := diagonalUtilityMean_strictMono_right he hl hr

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 3: compactness of convex hulls

Kreps I, Proposition A3.6, p. 455. Carathéodory reduces the convex hull to a
finite union of sets of mixtures with a bounded number of terms. Each such set is
the continuous image of a compact set of weights and a finite product of the
original compact set. The proof includes the empty-set case.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Convex combinations of exactly `n` listed points; zero weights are allowed. -/
def FiniteMixtureSet (S : Set E) (n : ℕ) : Set E :=
  {x | ∃ (w : Fin n → ℝ) (z : Fin n → E), (∀ i, 0 ≤ w i) ∧
    ∑ i, w i = 1 ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x}

/-- Every finite mixture belongs to the convex hull. -/
theorem finiteMixtureSet_subset_convexHull (S : Set E) (n : ℕ) :
    FiniteMixtureSet S n ⊆ convexHull ℝ S := by
  rintro x ⟨w, z, hw, h1, hz, hx⟩
  exact mem_convexHull_of_exists_fintype w z hw h1 hz hx

/-- Reindex a mixture on a finset by a finite interval of natural numbers. -/
theorem mem_finiteMixtureSet_of_mem_finset_hull {S : Set E} (t : Finset E)
    (ht : (↑t : Set E) ⊆ S) {x : E} (hx : x ∈ convexHull ℝ (↑t : Set E)) :
    x ∈ FiniteMixtureSet S t.card := by
  classical
  obtain ⟨w, hw, h1, hx⟩ := Finset.mem_convexHull'.mp hx
  let e : t ≃ Fin t.card := Fintype.equivFinOfCardEq (Fintype.card_coe t)
  refine ⟨fun i => w (e.symm i), fun i => (e.symm i).val,
    fun i => hw _ (e.symm i).property, ?_, fun i => ht (e.symm i).property, ?_⟩
  · calc
      ∑ i : Fin t.card, w (e.symm i) = ∑ i : t, w i :=
        Equiv.sum_comp e.symm (fun i : t => w i)
      _ = ∑ i ∈ t, w i := Finset.sum_attach t w
      _ = 1 := h1
  · calc
      ∑ i : Fin t.card, w (e.symm i) • (e.symm i).val =
          ∑ i : t, w i • i.val := Equiv.sum_comp e.symm (fun i : t => w i • i.val)
      _ = ∑ i ∈ t, w i • i := Finset.sum_attach t (fun i => w i • i)
      _ = x := hx

/-- Carathéodory expresses the hull as finitely many fixed-length mixture sets. -/
theorem convexHull_eq_finite_mixture_union [FiniteDimensional ℝ E] (S : Set E) :
    convexHull ℝ S = ⋃ n : Fin (Module.finrank ℝ E + 2), FiniteMixtureSet S n.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hcard, hxt⟩ := proposition_A3_5 hx
    exact Set.mem_iUnion.mpr ⟨⟨t.card, Nat.lt_add_one_iff.mpr hcard⟩,
      mem_finiteMixtureSet_of_mem_finset_hull t ht hxt⟩
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact finiteMixtureSet_subset_convexHull S n.val hn

/-- Mixtures with a fixed finite number of terms form a compact set. -/
theorem finiteMixtureSet_isCompact {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} (hS : IsCompact S) (n : ℕ) : IsCompact (FiniteMixtureSet S n) := by
  let W : Set (Fin n → ℝ) := Set.Icc 0 1 ∩ {w | ∑ i, w i = 1}
  let Z : Set (Fin n → G) := {z | ∀ i, z i ∈ S}
  let mix : (Fin n → ℝ) × (Fin n → G) → G := fun p => ∑ i, p.1 i • p.2 i
  have hW : IsCompact W := isCompact_Icc.inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hZ : IsCompact Z := isCompact_pi_infinite fun _ => hS
  have hm : Continuous mix := by fun_prop
  have he : FiniteMixtureSet S n = mix '' (W ×ˢ Z) := by
    ext x
    constructor
    · rintro ⟨w, z, hw, h1, hz, hx⟩
      refine ⟨(w, z), ⟨⟨⟨hw, ?_⟩, h1⟩, hz⟩, hx⟩
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hw j)
        (Finset.mem_univ i)
      change w i ≤ (1 : ℝ)
      simpa only [h1] using hi
    · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, hx⟩
      exact ⟨w, z, hw.1.1, hw.2, hz, hx⟩
  rw [he]
  exact (hW.prod hZ).image hm

/-- **Proposition A3.6:** in finite-dimensional Euclidean space, compact hulls stay compact. -/
theorem proposition_A3_6 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {S : Set G} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_finite_mixture_union]
  exact isCompact_iUnion fun n => finiteMixtureSet_isCompact hS n.val

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Positive affine atlases on real intervals

A local increasing coordinate system with positive affine transition maps can be continued
uniquely from any seed chart. This supplies the one-dimensional gluing step for additive utility
scales in Proposition 2.14. Compatibility is a hypothesis on every chart overlap; synchronizing
the scales of distinct economic coordinates is a separate obligation.
-/

namespace Kreps.PreferenceProperties

open Set

/-- An interval cover with increasing coordinates and positive affine changes of coordinate. -/
structure PositiveAffineIntervalAtlas (ι : Type*) (S : Set ℝ) where
  /-- The open domain of each chart. -/
  domain : ι → Set ℝ
  /-- Chart values, with values outside the chart domain immaterial. -/
  coord : ι → ℝ → ℝ
  /-- Chart domains are open in the real line. -/
  isOpen : ∀ i, IsOpen (domain i)
  /-- Chart domains are intervals. -/
  interval : ∀ i, (domain i).OrdConnected
  /-- Every chart stays in the underlying interval. -/
  subset : ∀ i, domain i ⊆ S
  /-- The charts cover the underlying interval. -/
  cover : ∀ x ∈ S, ∃ i, x ∈ domain i
  /-- Each coordinate is continuous on its domain. -/
  continuous : ∀ i, ContinuousOn (coord i) (domain i)
  /-- Each coordinate preserves orientation. -/
  increasing : ∀ i, StrictMonoOn (coord i) (domain i)
  /-- Changes of coordinate are positive affine on every overlap. -/
  transition : ∀ i j, ∃ A B : ℝ, 0 < A ∧
    ∀ x ∈ domain i ∩ domain j, coord i x = A * coord j x + B

/-- A coordinate is locally compatible with all the charts that meet its domain. -/
def PositiveAffineIntervalAtlas.Compatible {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ i, LocallyPositiveAffineOn f (a.coord i) (D ∩ a.domain i)

variable {ι : Type*} {S : Set ℝ}

/-- A continuation of a seed chart to a larger open interval. -/
structure AffineIntervalSection (a : PositiveAffineIntervalAtlas ι S) (seed : ι) where
  /-- The interval on which this continuation is defined. -/
  domain : Set ℝ
  /-- The continuation domain is open. -/
  isOpen : IsOpen domain
  /-- The continuation domain is an interval. -/
  interval : domain.OrdConnected
  /-- The continuation stays in the underlying interval. -/
  subset : domain ⊆ S
  /-- The continued coordinate. -/
  value : ℝ → ℝ
  /-- Continuation preserves continuity. -/
  continuous : ContinuousOn value domain
  /-- Continuation preserves strict increase. -/
  increasing : StrictMonoOn value domain
  /-- The continuation respects the given local coordinate system. -/
  compatible : a.Compatible value domain
  /-- The seed chart remains inside the continuation domain. -/
  seed_subset : a.domain seed ⊆ domain
  /-- The scale agrees with the prescribed normalization on the seed chart. -/
  seed_eq : ∀ x ∈ a.domain seed, value x = a.coord seed x

/-- Every chart is compatible with the atlas. -/
theorem PositiveAffineIntervalAtlas.compatible_chart {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (i : ι) : a.Compatible (a.coord i) (a.domain i) := by
  intro j
  obtain ⟨A, B, hA, he⟩ := a.transition i j
  exact locallyPositiveAffineOn_of_affine ((a.isOpen i).inter (a.isOpen j)) hA he

/-- The seed chart itself is a continuation with the prescribed normalization. -/
def PositiveAffineIntervalAtlas.seedSection {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (seed : ι) : AffineIntervalSection a seed where
  domain := a.domain seed
  isOpen := a.isOpen seed
  interval := a.interval seed
  subset := a.subset seed
  value := a.coord seed
  continuous := a.continuous seed
  increasing := a.increasing seed
  compatible := a.compatible_chart seed
  seed_subset := Subset.rfl
  seed_eq := fun _ _ => rfl

/-- Compatibility gives a single affine relation on each nonempty connected chart overlap. -/
theorem PositiveAffineIntervalAtlas.Compatible.affine {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ} (h : a.Compatible f D)
    (hD : D.OrdConnected) (i : ι) :
    ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ D ∩ a.domain i, f x = A * a.coord i x + B := by
  by_cases hne : (D ∩ a.domain i).Nonempty
  · exact locallyPositiveAffineOn_global (hD.inter (a.interval i)).isPreconnected hne
      ((a.increasing i).mono inter_subset_right) (h i)
  · exact ⟨1, 0, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Two compatible coordinates are locally positive affine functions of one another. -/
theorem PositiveAffineIntervalAtlas.Compatible.local_relation {ι : Type*} {S D E : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f g : ℝ → ℝ}
    (hf : a.Compatible f D) (hg : a.Compatible g E) (hDS : D ⊆ S) :
    LocallyPositiveAffineOn f g (D ∩ E) := by
  intro x hx
  obtain ⟨i, hxi⟩ := a.cover x (hDS hx.1)
  obtain ⟨U, hU, hxU, hUD, A, B, hA, heF⟩ := hf i x ⟨hx.1, hxi⟩
  obtain ⟨V, hV, hxV, hVE, C, F, hC, heG⟩ := hg i x ⟨hx.2, hxi⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    fun _ hz => ⟨(hUD hz.1).1, (hVE hz.2).1⟩,
    A / C, B - A / C * F, div_pos hA hC, ?_⟩
  intro y hy
  rw [heF y hy.1, heG y hy.2]
  field_simp
  nlinarith [ne_of_gt hC]

/-- Seed-normalized continuations agree on their entire overlap. -/
theorem AffineIntervalSection.unique {ι : Type*} {S : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {seed : ι}
    (hne : (a.domain seed).Nonempty) (p q : AffineIntervalSection a seed) :
    EqOn p.value q.value (p.domain ∩ q.domain) := by
  obtain ⟨x, hx⟩ := hne
  have hdom : (p.domain ∩ q.domain).Nonempty := ⟨x, p.seed_subset hx, q.seed_subset hx⟩
  obtain ⟨A, B, _, he⟩ := locallyPositiveAffineOn_global
    (p.interval.inter q.interval).isPreconnected hdom
    (q.increasing.mono inter_subset_right)
    (p.compatible.local_relation q.compatible p.subset)
  have hcoeff := affine_coefficients_unique (q.increasing.mono q.seed_subset)
    (a.isOpen seed) ⟨x, hx⟩ Subset.rfl
    (A := A) (B := B) (C := 1) (D := 0) (fun y hy => by
      have hey := he y ⟨p.seed_subset hy, q.seed_subset hy⟩
      rw [p.seed_eq y hy, ← q.seed_eq y hy] at hey
      simpa only [one_mul, add_zero] using hey.symm)
  intro y hy
  simpa only [hcoeff.1, hcoeff.2, one_mul, add_zero] using he y hy

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Endpoint extensions on real score intervals

A nonempty interior is dense in a real interval. Points of the interval outside
that interior can only be attained least or greatest elements. Consequently,
continuous strict interior scales with finite attained endpoint limits extend
to the full score interval.
-/

namespace Kreps.PreferenceProperties

/-- The real interior is dense relative to a nondegenerate interval. -/
theorem interval_interior_dense {S : Set ℝ} (hS : S.OrdConnected)
    (hn : (interior S).Nonempty) : Dense {x : S | x.val ∈ interior S} := by
  rw [Subtype.dense_iff]
  have he : ((↑) : S → ℝ) '' {x : S | x.val ∈ interior S} = interior S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  rw [he, (convex_iff_ordConnected.mpr hS).closure_interior_eq_closure_of_nonempty_interior hn]
  exact subset_closure

/-- A point of a real interval outside its interior is a least or greatest element. -/
theorem interval_outside_interior_extreme {S : Set ℝ} (hS : S.OrdConnected)
    (x : S) (hx : x.val ∉ interior S) : IsBot x ∨ IsTop x := by
  by_contra! h
  obtain ⟨a, ha⟩ := not_forall.mp h.1
  obtain ⟨b, hb⟩ := not_forall.mp h.2
  have hax : a.val < x.val := lt_of_not_ge ha
  have hxb : x.val < b.val := lt_of_not_ge hb
  apply hx
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Ioo_mem_nhds hax hxb) (fun _ hy =>
      hS.out a.property b.property ⟨hy.1.le, hy.2.le⟩))

/-- A continuous strict scale extends from an interval interior to its bounded attained ends. -/
theorem interval_exists_continuous_strictMono_extension {S : Set ℝ} (hS : S.OrdConnected)
    (hn : (interior S).Nonempty) {f : interior S → ℝ}
    (hf : Continuous f) (hm : StrictMono f)
    (hlo : ∀ x : S, x.val ∉ interior S → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x : S, x.val ∉ interior S → IsTop x → BddAbove (Set.range f)) :
    ∃ g : S → ℝ, Continuous g ∧ StrictMono g ∧
      ∀ x : interior S, g (Set.inclusion interior_subset x) = f x := by
  let : Fact S.OrdConnected := ⟨hS⟩
  let D : Set S := {x | x.val ∈ interior S}
  let inc : D → interior S := fun x => ⟨x.val.val, x.property⟩
  let f' : D → ℝ := f ∘ inc
  have hc : Continuous inc :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hm' : StrictMono f' := fun _ _ h => hm h
  have hr : Set.range f' = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inc x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨⟨x.val, interior_subset x.property⟩, x.property⟩, rfl⟩
  obtain ⟨g, hg, hgm, heq⟩ := exists_continuous_strictMono_endpoint_extension
    (interval_interior_dense hS hn) (interval_outside_interior_extreme hS)
    (hf.comp hc) hm' (fun x hx he => hr ▸ hlo x hx he)
    (fun x hx he => hr ▸ hhi x hx he)
  exact ⟨g, hg, hgm, fun x => heq ⟨Set.inclusion interior_subset x, x.property⟩⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Globalizing aligned local pair comparisons

Continuous increasing coordinate scales identify real intervals with their interval images.
Straight interpolation in those score images gives paths whose total score is monotone.
The local comparison cover therefore globalizes, including indifference, without assuming
smoothness or a common size for chart neighborhoods.
-/

namespace Kreps.PreferenceProperties

open Set
open scoped unitInterval

/-- A continuous increasing interval coordinate admits a path affine in its score. -/
theorem exists_affine_score_path {S : Set ℝ} (hS : S.OrdConnected) {f : S → ℝ}
    (hf : Continuous f) (hm : StrictMono f) (x y : S) :
    ∃ p : I → S, Continuous p ∧ p 0 = x ∧ p 1 = y ∧
      ∀ t, f (p t) = (1 - t.val) * f x + t.val * f y := by
  let : Fact S.OrdConnected := ⟨hS⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  have hR : (range f).OrdConnected := (isPreconnected_range hf).ordConnected
  let : Fact (range f).OrdConnected := ⟨hR⟩
  let e : S ≃o range f := StrictMono.orderIso f hm
  let r : I → range f := fun t =>
    ⟨(1 - t.val) * f x + t.val * f y, by
      simpa only [smul_eq_mul] using hR.convex ⟨x, rfl⟩ ⟨y, rfl⟩
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩
  have hrc : Continuous r :=
    (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)).subtype_mk _
  have hr0 : r 0 = e x := Subtype.ext (by simp [r, e])
  have hr1 : r 1 = e y := Subtype.ext (by simp [r, e])
  refine ⟨fun t => e.symm (r t), e.symm.continuous.comp hrc, ?_, ?_, ?_⟩
  · change e.symm (r 0) = x
    rw [hr0]
    exact e.symm_apply_apply x
  · change e.symm (r 1) = y
    rw [hr1]
    exact e.symm_apply_apply y
  · intro t
    exact congrArg Subtype.val (e.apply_symm_apply (r t))

/-- Locally represented pair preferences have the same additive representation globally. -/
theorem pair_global_order_of_local_comparisons {S T : Set ℝ}
    (hS : S.OrdConnected) (hT : T.OrdConnected) {f : S → ℝ} {g : T → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfm : StrictMono f) (hgm : StrictMono g)
    {U : S × T → ℝ}
    (hl : ∀ p : S × T, ∃ N : Set (S × T), IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ N, ∀ r ∈ N, U q ≤ U r ↔ f q.1 + g q.2 ≤ f r.1 + g r.2) :
    ∀ p q : S × T, U p ≤ U q ↔ f p.1 + g p.2 ≤ f q.1 + g q.2 := by
  apply global_order_of_local_comparisons hl
  intro x y hxy
  obtain ⟨p, hpc, hp0, hp1, hpf⟩ := exists_affine_score_path hS hf hfm x.1 y.1
  obtain ⟨q, hqc, hq0, hq1, hqg⟩ := exists_affine_score_path hT hg hgm x.2 y.2
  refine ⟨fun t => (p t, q t), hpc.prodMk hqc, ?_, ?_, ?_⟩
  · simp only [hp0, hq0]
  · simp only [hp1, hq1]
  · intro a b hab
    change a.val ≤ b.val at hab
    change f (p a) + g (q a) ≤ f (p b) + g (q b)
    rw [hpf, hqg, hpf, hqg]
    have hnonneg := mul_nonneg (sub_nonneg.mpr hab)
      (sub_nonneg.mpr hxy)
    change 0 ≤ (b.val - a.val) * ((f y.1 + g y.2) - (f x.1 + g x.2)) at hnonneg
    nlinarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Finite utility representation

Kreps I, §1.3, pp. 7-8: no-better-than sets and their cardinalities provide the
utility representation in Proposition 1.8 and complete Proposition 1.2.
The inclusion results do not require a finite alternative space.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- Every alternative belongs to its own no-better-than set. -/
theorem mem_noBetterThan_self (hc : Complete r) (x : X) : x ∈ NoBetterThan r x :=
  complete_refl hc x

/-- **Proposition 1.7**, p. 8: preference is inclusion of lower contour sets. -/
theorem pref_iff_noBetterThan_subset (hr : Rational r) (x y : X) :
    r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x := by
  constructor
  · exact fun h z hz => hr.2 x y z h hz
  · exact fun h => h (mem_noBetterThan_self hr.1 y)

/-- Strict preference is strict inclusion of no-better-than sets. -/
theorem strict_iff_noBetterThan_ssubset (hr : Rational r) (x y : X) :
    Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x := by
  change (r x y ∧ ¬r y x) ↔ _
  rw [Set.ssubset_def, ← pref_iff_noBetterThan_subset hr x y,
    ← pref_iff_noBetterThan_subset hr y x]

/-- **Proposition 1.7**, p. 8: nonemptiness and the three nesting possibilities. -/
theorem proposition_1_7 (hr : Rational r) (x y : X) :
    (NoBetterThan r x).Nonempty ∧
      (r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x) ∧
      (Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x) ∧
      (NoBetterThan r x ⊂ NoBetterThan r y ∨
        NoBetterThan r y ⊂ NoBetterThan r x ∨ NoBetterThan r x = NoBetterThan r y) := by
  refine ⟨⟨x, mem_noBetterThan_self hr.1 x⟩, pref_iff_noBetterThan_subset hr x y,
    strict_iff_noBetterThan_ssubset hr x y, ?_⟩
  by_cases hxy : r x y
  · by_cases hyx : r y x
    · exact Or.inr (Or.inr (Set.Subset.antisymm
        ((pref_iff_noBetterThan_subset hr y x).mp hyx)
        ((pref_iff_noBetterThan_subset hr x y).mp hxy)))
    · exact Or.inr (Or.inl ((strict_iff_noBetterThan_ssubset hr x y).mp ⟨hxy, hyx⟩))
  · exact Or.inl ((strict_iff_noBetterThan_ssubset hr y x).mp
      ⟨(hr.1 x y).resolve_left hxy, hxy⟩)

/-- The book's cardinality utility; representation is asserted only for finite `X`. -/
noncomputable def FiniteUtility (r : X → X → Prop) (x : X) : ℝ :=
  (NoBetterThan r x).ncard

/-- **Proposition 1.8**, p. 8: cardinality of lower contours represents preference. -/
theorem proposition_1_8 [Finite X] (hr : Rational r) : Represents (FiniteUtility r) r := by
  intro x y
  constructor
  · intro hxy
    have h := Set.ncard_le_ncard ((pref_iff_noBetterThan_subset hr x y).mp hxy)
    unfold FiniteUtility
    exact_mod_cast h
  · intro h
    by_contra hxy
    have hyx := (hr.1 x y).resolve_left hxy
    have hlt := Set.ncard_lt_ncard
      ((strict_iff_noBetterThan_ssubset hr y x).mp ⟨hyx, hxy⟩)
    have hlt' : FiniteUtility r x < FiniteUtility r y := by
      unfold FiniteUtility
      exact_mod_cast hlt
    exact (not_lt_of_ge h) hlt'

/-- **Proposition 1.2b**, p. 4: rational finite preference has a utility representation. -/
theorem proposition_1_2b [Finite X] (hr : Rational r) :
    FiniteNonempty (PrefChoice r) ∧ Coherent (PrefChoice r) ∧
      ∃ u : X → ℝ, Represents u r :=
  ⟨(proposition_1_4 hr).1, (proposition_1_4 hr).2, FiniteUtility r, proposition_1_8 hr⟩

/-- On a finite alternative space every coherent feasible choice is rationalized exactly. -/
theorem finite_choice_eq_revealed [Finite X] {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) : c = PrefChoice (Revealed c) := by
  funext A
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [feasible_empty hf]
    simp [PrefChoice]
  · exact choice_eq_revealed_of_nonempty hf hn hc (hn A (Set.toFinite A) hA)

/-- **Proposition 1.2a**, p. 4: the same preferences and utility rationalize finite choice. -/
theorem proposition_1_2a [Finite X] {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    ∃ (u : X → ℝ) (r : X → X → Prop),
      Rational r ∧ Represents u r ∧ c = PrefChoice r ∧ c = UtilityChoice u := by
  have hr := (proposition_1_5 hf hn hc).1
  have hu := proposition_1_8 hr
  have hchoice := finite_choice_eq_revealed hf hn hc
  exact ⟨FiniteUtility (Revealed c), Revealed c, hr, hu, hchoice,
    hchoice.trans (represents_choice hu)⟩

/-- **Proposition 1.2c**, p. 4. This direction holds even for infinite `X`. -/
theorem proposition_1_2c (u : X → ℝ) :
    FiniteNonempty (UtilityChoice u) ∧ Coherent (UtilityChoice u) ∧
      Rational (UtilityPref u) ∧ PrefChoice (UtilityPref u) = UtilityChoice u :=
  ⟨(proposition_1_3b u).1, (proposition_1_3b u).2, proposition_1_3a u, rfl⟩

/-- **Problem 1.8**, p. 26, asks for the proof of Proposition 1.7. -/
theorem problem_1_8 (hr : Rational r) (x y : X) :
    (NoBetterThan r x).Nonempty ∧
      (r x y ↔ NoBetterThan r y ⊆ NoBetterThan r x) ∧
      (Strict r x y ↔ NoBetterThan r y ⊂ NoBetterThan r x) :=
  ⟨(proposition_1_7 hr x y).1, (proposition_1_7 hr x y).2.1,
    (proposition_1_7 hr x y).2.2.1⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Countable utility representation

Kreps I, §1.5, Propositions 1.11-1.12, pp. 10-12. Positive summable weights on a
countable separating subset give a utility representation. Conversely, rational
interval witnesses, together with attained minima above rational cutoffs, provide a
countable separating subset of any represented preference. This is the book's
countability argument with the gap case expressed without infimum notation.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- The separating-subset condition in **Proposition 1.12**, p. 11. -/
def OrderSeparating (r : X → X → Prop) (D : Set X) : Prop :=
  ∀ x y, Strict r x y → ∃ z ∈ D, r x z ∧ Strict r z y

/-- Every countable type has strictly positive summable real weights. -/
theorem exists_positive_summable (Y : Type*) [Countable Y] :
    ∃ w : Y → ℝ, (∀ y, 0 < w y) ∧ Summable w := by
  let := Encodable.ofCountable Y
  exact ⟨fun y => (1 / 2 : ℝ) ^ Encodable.encode y,
    fun _ => pow_pos (by norm_num) _, summable_geometric_two_encode⟩

/-- Sum the weights of separating alternatives no better than `x`. -/
noncomputable def WeightedUtility (r : X → X → Prop) (D : Set X)
    (w : D → ℝ) (x : X) : ℝ := ∑' z : D, {z : D | r x z}.indicator w z

/-- Termwise comparison of weighted no-better-than sets. -/
theorem weightedTerm_le {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (ht : TransitivePref r) {x y : X} (hxy : r x y) (z : D) :
    {z : D | r y z}.indicator w z ≤ {z : D | r x z}.indicator w z := by
  classical
  change (if r y z then w z else 0) ≤ if r x z then w z else 0
  by_cases hy : r y z
  · have hx := ht x y z hxy hy
    simp [hy, hx]
  · simp only [hy, ite_false]
    split_ifs
    · exact (hw z).le
    · exact le_rfl

/-- Weak preference increases the weighted sum. -/
theorem weightedUtility_mono {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (ht : TransitivePref r) {x y : X} (hxy : r x y) :
    WeightedUtility r D w y ≤ WeightedUtility r D w x :=
  Summable.tsum_le_tsum (weightedTerm_le hw ht hxy)
    (hs.indicator _) (hs.indicator _)

/-- A separating witness makes the increase in utility strict. -/
theorem weightedUtility_strict {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (ht : TransitivePref r) (hD : OrderSeparating r D)
    {x y : X} (hxy : Strict r x y) :
    WeightedUtility r D w y < WeightedUtility r D w x := by
  classical
  obtain ⟨z, hzD, hxz, hzy⟩ := hD x y hxy
  let zi : D := ⟨z, hzD⟩
  have hzi : {z : D | r y z}.indicator w zi < {z : D | r x z}.indicator w zi := by
    change (if r y z then w zi else 0) < if r x z then w zi else 0
    simp only [hzy.2, ite_false, hxz, ite_true]
    exact hw zi
  exact Summable.tsum_lt_tsum (weightedTerm_le hw ht hxy.1) hzi
    (hs.indicator _) (hs.indicator _)

/-- A positive weighted sum on a separating set represents rational preferences. -/
theorem weightedUtility_represents {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (hr : Rational r) (hD : OrderSeparating r D) :
    Represents (WeightedUtility r D w) r := by
  intro x y
  constructor
  · exact weightedUtility_mono hw hs hr.2
  · intro h
    by_contra hxy
    have hstrict : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact (not_lt_of_ge h) (weightedUtility_strict hw hs hr.2 hD hstrict)

/-- The sufficient direction of **Proposition 1.12**, p. 11. -/
theorem represents_of_countable_separating (hr : Rational r) {D : Set X}
    (hc : D.Countable) (hD : OrderSeparating r D) : ∃ u : X → ℝ, Represents u r := by
  let : Countable D := hc.to_subtype
  obtain ⟨w, hw, hs⟩ := exists_positive_summable D
  exact ⟨WeightedUtility r D w, weightedUtility_represents hw hs hr hD⟩

/-- **Proposition 1.11**, pp. 10-11: every rational countable preference is representable. -/
theorem proposition_1_11 [Countable X] (hr : Rational r) :
    ∃ u : X → ℝ, Represents u r := by
  apply represents_of_countable_separating hr (Set.to_countable Set.univ)
  exact fun x y hxy => ⟨x, Set.mem_univ x, complete_refl hr.1 x, hxy⟩

/-- A representing utility also represents the strict comparison by strict inequality. -/
theorem strict_iff_utility_lt {u : X → ℝ} (hu : Represents u r) (x y : X) :
    Strict r x y ↔ u y < u x := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hle => h.2 ((hu y x).mpr hle))
  · intro h
    exact ⟨(hu x y).mpr h.le, fun hyx => (not_le_of_gt h) ((hu y x).mp hyx)⟩

/-- The necessary direction of **Proposition 1.12**, p. 12, including gaps in the range. -/
theorem countable_separating_of_represents {u : X → ℝ} (hu : Represents u r) :
    ∃ D : Set X, D.Countable ∧ OrderSeparating r D := by
  classical
  let I := {p : ℚ × ℚ // ∃ z : X, (p.1 : ℝ) < u z ∧ u z < (p.2 : ℝ)}
  let f : I → X := fun i => Classical.choose i.property
  have hf (i : I) : (i.val.1 : ℝ) < u (f i) ∧ u (f i) < (i.val.2 : ℝ) :=
    Classical.choose_spec i.property
  let J := {q : ℚ // ∃ z : X, (q : ℝ) < u z ∧ ∀ y, (q : ℝ) < u y → u z ≤ u y}
  let g : J → X := fun j => Classical.choose j.property
  have hg (j : J) : (j.val : ℝ) < u (g j) ∧
      ∀ y, (j.val : ℝ) < u y → u (g j) ≤ u y :=
    Classical.choose_spec j.property
  refine ⟨Set.range f ∪ Set.range g,
    (Set.countable_range f).union (Set.countable_range g), ?_⟩
  intro x y hxy
  have hlt := (strict_iff_utility_lt hu x y).mp hxy
  obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt
  by_cases hgap : ∃ z : X, (q : ℝ) < u z ∧ u z < u x
  · obtain ⟨z, hqz, hzx⟩ := hgap
    obtain ⟨t, hzt, htx⟩ := exists_rat_btwn hzx
    let i : I := ⟨(q, t), z, hqz, hzt⟩
    refine ⟨f i, Or.inl ⟨i, rfl⟩, (hu x (f i)).mpr ?_,
      (strict_iff_utility_lt hu (f i) y).mpr ?_⟩
    · exact ((hf i).2.trans htx).le
    · exact hyq.trans (hf i).1
  · have hmin : ∀ z : X, (q : ℝ) < u z → u x ≤ u z := by
      intro z hqz
      exact le_of_not_gt (fun hzx => hgap ⟨z, hqz, hzx⟩)
    let j : J := ⟨q, x, hqx, hmin⟩
    refine ⟨g j, Or.inr ⟨j, rfl⟩, (hu x (g j)).mpr ((hg j).2 x hqx),
      (strict_iff_utility_lt hu (g j) y).mpr ?_⟩
    exact hyq.trans (hg j).1

/-- **Proposition 1.12**, pp. 11-12: the full countable-subset criterion. -/
theorem proposition_1_12 (hr : Rational r) :
    (∃ u : X → ℝ, Represents u r) ↔ ∃ D : Set X, D.Countable ∧ OrderSeparating r D := by
  constructor
  · rintro ⟨u, hu⟩
    exact countable_separating_of_represents hu
  · rintro ⟨D, hc, hD⟩
    exact represents_of_countable_separating hr hc hD

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice from infinite menus

Kreps I, §1.6, pp. 15-17. Assumption 1.16 is exactly what is needed to eliminate
the empty-choice exception in Proposition 1.5. Emptying any family of infinite
menus preserves the original two choice conditions, as the book explains on p. 16.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- **Assumption 1.16**, p. 16: choose whenever a revealed greatest element exists. -/
def Assumption116 (c : ChoiceRule X) : Prop :=
  ∀ A x, x ∈ A → A ⊆ NoBetterThan (Revealed c) x → (c A).Nonempty

/-- **Proposition 1.17**, p. 17, in both directions. -/
theorem proposition_1_17 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) :
    c = PrefChoice (Revealed c) ↔ Assumption116 c := by
  constructor
  · intro h A x hx hmax
    rw [h]
    exact ⟨x, hx, fun y hy => hmax hy⟩
  · intro h
    funext A
    ext x
    constructor
    · intro hx
      exact ⟨hf A hx, fun y hy => revealed_of_chosen hf hn hc hx hy⟩
    · rintro ⟨hx, hmax⟩
      have hne := h A x hx (fun y hy => hmax y hy)
      rw [choice_eq_revealed_of_nonempty hf hn hc hne]
      exact ⟨hx, hmax⟩

/-- **Proposition 1.18**, p. 17: no revealed greatest element implies empty choice. -/
theorem proposition_1_18 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {A : Set X}
    (hA : ∀ x ∈ A, ¬A ⊆ NoBetterThan (Revealed c) x) : c A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hA x (hf A hx) (fun _ hy => revealed_of_chosen hf hn hc hx hy)

/-- Replace choice by the empty set on a specified family of menus. -/
noncomputable def EmptyMenus (c : ChoiceRule X) (E : Set (Set X)) : ChoiceRule X := by
  classical
  exact fun A => if A ∈ E then ∅ else c A

/-- Emptying menus preserves feasibility. -/
theorem emptyMenus_feasible {c : ChoiceRule X} (hf : Feasible c) (E : Set (Set X)) :
    Feasible (EmptyMenus c E) := by
  classical
  intro A x hx
  by_cases hA : A ∈ E
  · simp [EmptyMenus, hA] at hx
  · exact hf A (by simpa [EmptyMenus, hA] using hx)

/-- Emptying only infinite menus preserves finite nonemptiness. -/
theorem emptyMenus_finiteNonempty {c : ChoiceRule X} (hn : FiniteNonempty c)
    {E : Set (Set X)} (hE : ∀ A ∈ E, ¬A.Finite) : FiniteNonempty (EmptyMenus c E) := by
  classical
  intro A hfin hne
  have hA : A ∉ E := fun he => hE A he hfin
  simpa [EmptyMenus, hA] using hn A hfin hne

/-- The argument on p. 16: emptying any collection of menus preserves coherence. -/
theorem emptyMenus_coherent {c : ChoiceRule X} (hc : Coherent c) (E : Set (Set X)) :
    Coherent (EmptyMenus c E) := by
  classical
  intro A B x hx y hy hxc hyc hyB
  by_cases hA : A ∈ E
  · simp [EmptyMenus, hA] at hxc
  · by_cases hB : B ∈ E
    · simp [EmptyMenus, hB] at hyB
    · exact hc A B x hx y hy (by simpa [EmptyMenus, hA] using hxc)
        (by simpa [EmptyMenus, hA] using hyc) (by simpa [EmptyMenus, hB] using hyB)

/-- Full formalization of the arbitrary infinite-menu modification on p. 16. -/
theorem empty_infinite_menus_preserves_choice {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hc : Coherent c) {E : Set (Set X)}
    (hE : ∀ A ∈ E, ¬A.Finite) :
    Feasible (EmptyMenus c E) ∧ FiniteNonempty (EmptyMenus c E) ∧
      Coherent (EmptyMenus c E) :=
  ⟨emptyMenus_feasible hf E, emptyMenus_finiteNonempty hn hE, emptyMenus_coherent hc E⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quasi-linear utility and compensating money

Kreps I, Definition 2.15 and Proposition 2.16, pp. 43-44, and Problem 2.11,
p. 48. The non-money bundle has any nonempty type X; taking X to be the
nonnegative orthant gives the book's domain. Money is nonnegative throughout.
The construction follows the hint: calibrate each bundle against a fixed x₀,
then assign the difference between the two compensating money amounts.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*}

/-- **Definition 2.15:** subutility plus the amount of money left over. -/
def QuasiLinearUtility (u : X → ℝ) (p : X × ℝ≥0) : ℝ := u p.1 + p.2

/-- A preference admits a utility representation with money coefficient one. -/
def QuasiLinear (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∃ u : X → ℝ, Represents (QuasiLinearUtility u) r

/-- **Proposition 2.16a:** for fixed non-money goods, money orders the bundles. -/
def OwnMoneyOrder (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x m n, r (x, m) (x, n) ↔ n ≤ m

/-- **Proposition 2.16b:** each common nonnegative money addition preserves comparisons. -/
def MoneyTranslation (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x y m n t, r (x, m) (y, n) ↔ r (x, m + t) (y, n + t)

/-- **Proposition 2.16c:** money can make any two non-money bundles indifferent. -/
def MoneyCompensable (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x y, ∃ m n, Indifferent r (x, m) (y, n)

/-- Indifferent substitutions leave every weak comparison unchanged. -/
theorem indifferent_compare_iff {Y : Type*} {r : Y → Y → Prop}
    (ht : TransitivePref r) {x x' y y' : Y}
    (hx : Indifferent r x x') (hy : Indifferent r y y') : r x y ↔ r x' y' := by
  constructor
  · intro h
    exact ht x' y y' (ht x' x y hx.2 h) hy.1
  · intro h
    exact ht x y' y (ht x x' y' hx.1 h) hy.2

/-- Translation invariance also preserves indifference in both directions. -/
theorem moneyTranslation_indifferent {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (ht : MoneyTranslation r) (x y : X) (m n t : ℝ≥0) :
    Indifferent r (x, m) (y, n) ↔ Indifferent r (x, m + t) (y, n + t) := by
  exact and_congr (ht x y m n t) (ht y x n m t)

/-- A quasi-linear representation has the fixed-goods money order. -/
theorem quasiLinear_ownMoneyOrder {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : OwnMoneyOrder r := by
  intro x m n
  rw [hu]
  change (u x + (n : ℝ) ≤ u x + (m : ℝ)) ↔ n ≤ m
  rw [add_le_add_iff_left, NNReal.coe_le_coe]

/-- Common additions cancel from comparisons of quasi-linear utilities. -/
theorem quasiLinear_moneyTranslation {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : MoneyTranslation r := by
  intro x y m n t
  rw [hu, hu]
  simp only [QuasiLinearUtility, NNReal.coe_add]
  constructor <;> intro h <;> linarith

/-- Positive and negative parts of the utility difference give feasible compensations. -/
theorem quasiLinear_moneyCompensable {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : MoneyCompensable r := by
  intro x y
  let m : ℝ≥0 := .mk (max 0 (u y - u x)) (le_max_left _ _)
  let n : ℝ≥0 := .mk (max 0 (u x - u y)) (le_max_left _ _)
  have he : QuasiLinearUtility u (x, m) = QuasiLinearUtility u (y, n) := by
    change u x + max 0 (u y - u x) = u y + max 0 (u x - u y)
    rcases le_total (u x) (u y) with h | h
    · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
      ring
  exact ⟨m, n, (hu _ _).mpr he.ge, (hu _ _).mpr he.le⟩

/-- The compensating-money construction in the hint to **Problem 2.11**. -/
theorem quasiLinear_of_money_properties {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) (hm : OwnMoneyOrder r) (ht : MoneyTranslation r)
    (hc : MoneyCompensable r) (x₀ : X) : QuasiLinear r := by
  classical
  choose m n h using fun x => hc x x₀
  let u : X → ℝ := fun x => (n x : ℝ) - (m x : ℝ)
  refine ⟨u, ?_⟩
  rintro ⟨x, a⟩ ⟨y, b⟩
  change r (x, a) (y, b) ↔ u y + (b : ℝ) ≤ u x + (a : ℝ)
  let T := m x + m y
  have hx : Indifferent r (x, a + T) (x₀, n x + a + m y) := by
    simpa [T, add_assoc, add_left_comm, add_comm] using
      (moneyTranslation_indifferent ht x x₀ (m x) (n x) (a + m y)).mp (h x)
  have hy : Indifferent r (y, b + T) (x₀, n y + b + m x) := by
    simpa [T, add_assoc, add_left_comm, add_comm] using
      (moneyTranslation_indifferent ht y x₀ (m y) (n y) (b + m x)).mp (h y)
  calc
    r (x, a) (y, b) ↔ r (x, a + T) (y, b + T) := ht x y a b T
    _ ↔ r (x₀, n x + a + m y) (x₀, n y + b + m x) :=
      indifferent_compare_iff hr.2 hx hy
    _ ↔ n y + b + m x ≤ n x + a + m y := hm x₀ _ _
    _ ↔ u y + (b : ℝ) ≤ u x + (a : ℝ) := by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      dsimp [u]
      constructor <;> intro hle <;> linarith

/-- **Proposition 2.16:** all three money properties characterize quasi-linearity. -/
theorem proposition_2_16 [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    QuasiLinear r ↔ OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨quasiLinear_ownMoneyOrder hu, quasiLinear_moneyTranslation hu,
      quasiLinear_moneyCompensable hu⟩
  · rintro ⟨hm, ht, hc⟩
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact quasiLinear_of_money_properties hr hm ht hc x₀

/-- **Problem 2.11:** the characterization, with a nonnegative money domain. -/
theorem problem_2_11 [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    QuasiLinear r ↔ OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r :=
  proposition_2_16 hr

/-- The money-unit utility difference in the compensation discussion on p. 44. -/
def QuasiLinearDifference (u : X → ℝ) (p q : X × ℝ≥0) : ℝ :=
  QuasiLinearUtility u p - QuasiLinearUtility u q

/-- The corrected bundle keeps q's goods and adds the utility difference to q's money. -/
theorem quasiLinear_compensation {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) (p q : X × ℝ≥0)
    (hf : 0 ≤ (q.2 : ℝ) + QuasiLinearDifference u p q) :
    Indifferent r p (q.1, .mk ((q.2 : ℝ) + QuasiLinearDifference u p q) hf) := by
  have he : QuasiLinearUtility u
      (q.1, .mk ((q.2 : ℝ) + QuasiLinearDifference u p q) hf) =
      QuasiLinearUtility u p := by
    change u q.1 + ((q.2 : ℝ) + (u p.1 + p.2 - (u q.1 + q.2))) = u p.1 + p.2
    ring
  exact ⟨(hu _ _).mpr he.le, (hu _ _).mpr he.ge⟩

/-- A weakly preferred starting bundle guarantees that the compensation stays feasible. -/
theorem quasiLinear_compensation_of_preferred {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) {p q : X × ℝ≥0}
    (hpq : r p q) : ∃ n : ℝ≥0, (n : ℝ) = q.2 + QuasiLinearDifference u p q ∧
      Indifferent r p (q.1, n) := by
  have hd : 0 ≤ QuasiLinearDifference u p q := sub_nonneg.mpr ((hu p q).mp hpq)
  have hf := add_nonneg q.2.property hd
  exact ⟨.mk _ hf, rfl, quasiLinear_compensation hu p q hf⟩

/-- Reusing the original goods, as in the printed final formula, fails even for linear utility. -/
theorem printed_compensation_bundle_counterexample :
    ¬Indifferent (UtilityPref (QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ))))
      (1, 0) (1, 1) := by
  norm_num [Indifferent, UtilityPref, QuasiLinearUtility]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: continuous functions and the intermediate-value theorem

Definition A2.15, Propositions A2.15–A2.16, Definition A2.17 and Proposition
A2.18, pp. 447–448. Using a subtype as the domain gives precisely relative
continuity. The book's term "simply connected" here means path connected;
its definition also permits the empty set. No assertion about homotopies is made.
-/

namespace Kreps.PreferenceProperties

open scoped Topology NNReal

/-- **Definition A2.15:** the epsilon–delta definition on a relative domain. -/
theorem definition_A2_15 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (S : Set X) (x : X) :
    ContinuousWithinAt f S x ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃y⦄,
      y ∈ S → dist y x < δ → dist (f y) (f x) < ε := Metric.continuousWithinAt_iff

/-- The footnote's uniform continuity condition uses one delta for all base points. -/
theorem appendix2_uniform_continuity {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x y⦄,
      dist x y < δ → dist (f x) (f y) < ε := Metric.uniformContinuous_iff

/-- A uniform Lipschitz bound supplies the footnote's uniform continuity. -/
theorem appendix2_lipschitz_uniform {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    UniformContinuous f := hf.uniformContinuous

/-- **Proposition A2.15(a):** continuity at a point is equivalent to sequential continuity. -/
theorem proposition_A2_15a {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ u : ℕ → X, Filter.Tendsto u Filter.atTop (𝓝 x) →
      Filter.Tendsto (f ∘ u) Filter.atTop (𝓝 (f x)) := tendsto_nhds_iff_seq_tendsto

/-- **Proposition A2.15(b):** open-preimage characterization; subtypes encode relative openness. -/
theorem proposition_A2_15b_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ O, IsOpen O → IsOpen (f ⁻¹' O) := continuous_def

/-- **Proposition A2.15(b):** the equivalent closed-preimage characterization. -/
theorem proposition_A2_15b_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ C, IsClosed C → IsClosed (f ⁻¹' C) :=
  continuous_iff_isClosed

/-- **Proposition A2.16(a):** sums of continuous vector-valued functions are continuous. -/
theorem proposition_A2_16a {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f g : X → CommodityEuclidean k} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := hf.add hg

/-- **Proposition A2.16(b):** products of continuous real functions are continuous. -/
theorem proposition_A2_16b {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := hf.mul hg

/-- **Proposition A2.16(c):** a quotient is continuous where its denominator is nonzero. -/
theorem proposition_A2_16c {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) {x : X} (hx : g x ≠ 0) :
    ContinuousAt (fun y => f y / g y) x := hf.continuousAt.div hg.continuousAt hx

/-- **Proposition A2.16(d):** continuous functions compose. -/
theorem proposition_A2_16d {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := hg.comp hf

/-- **Definition A2.17:** the book's convention is path connectedness, allowing the empty set. -/
theorem definition_A2_17 {X : Type*} [TopologicalSpace X] (S : Set X) :
    (∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y) ↔ S = ∅ ∨ IsPathConnected S := by
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty S with hS | hS
    · exact Or.inl hS
    · exact Or.inr (isPathConnected_iff.mpr ⟨hS, h⟩)
  · rintro (rfl | h)
    · simp
    · exact h.joinedIn

/-- **Proposition A2.18:** every intermediate value is attained along a path-connected domain. -/
theorem proposition_A2_18 {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : ∀ x ∈ S, ∀ y ∈ S, JoinedIn S x y) {f : X → ℝ}
    (hf : ContinuousOn f S) {x y : X} (hx : x ∈ S) (hy : y ∈ S)
    {r : ℝ} (hxr : f x < r) (hry : r < f y) : ∃ z ∈ S, f z = r := by
  have hp : IsPathConnected S := isPathConnected_iff.mpr ⟨⟨x, hx⟩, hS⟩
  exact hp.isConnected.isPreconnected.intermediate_value hx hy hf ⟨hxr.le, hry.le⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: coordinate spaces and equivalent norms

The orthants on p. 441, the three distances on p. 444, and the coordinate-bound
characterization of Definition A2.11. Strict positivity means positivity in
every coordinate, rather than strict inequality in the product partial order.
-/

namespace Kreps.PreferenceProperties

/-- The strictly positive orthant described on p. 441. -/
def StrictlyPositiveOrthant (k : ℕ) := {x : Fin k → ℝ // ∀ j, 0 < x j}

/-- Membership of the nonnegative orthant is exactly coordinatewise nonnegativity. -/
theorem appendix2_nonnegative_coordinates {k : ℕ} (x : Fin k → ℝ) :
    x ∈ Set.Ici 0 ↔ ∀ j, 0 ≤ x j := Iff.rfl

/-- The nonnegative orthant is a closed domain, including its boundary. -/
theorem appendix2_nonnegative_orthant_closed (k : ℕ) :
    IsClosed (Set.Ici (0 : Fin k → ℝ)) := isClosed_Ici

/-- Strict coordinatewise positivity defines an open domain. -/
theorem appendix2_positive_orthant_open (k : ℕ) :
    IsOpen {x : Fin k → ℝ | ∀ j, 0 < x j} := by
  have he : {x : Fin k → ℝ | ∀ j, 0 < x j} = ⋂ j, {x | 0 < x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)

/-- The sum norm dominates the Euclidean norm by the coordinate-vector triangle inequality. -/
theorem euclidean_norm_le_sum_abs {k : ℕ} (x : CommodityEuclidean k) :
    ‖x‖ ≤ ∑ j, |x j| := by
  have he : (∑ j : Fin k, PiLp.single 2 j (x j) : CommodityEuclidean k) = x := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ j : Fin k, (PiLp.single 2 j (x j) : CommodityEuclidean k)‖ :=
      congrArg norm he.symm
    _ ≤ ∑ j : Fin k, ‖(PiLp.single 2 j (x j) : CommodityEuclidean k)‖ := norm_sum_le _ _
    _ = ∑ j, |x j| := by simp only [PiLp.norm_single, Real.norm_eq_abs]

/-- The three norms have explicit dimension-dependent comparison constants. -/
theorem appendix2_norm_comparison {k : ℕ} (x : CommodityEuclidean k) :
    ‖(fun j => x j : Fin k → ℝ)‖ ≤ ‖x‖ ∧ ‖x‖ ≤ ∑ j, |x j| ∧
      (∑ j, |x j|) ≤ k * ‖(fun j => x j : Fin k → ℝ)‖ := by
  refine ⟨(pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (PiLp.norm_apply_le x),
    euclidean_norm_le_sum_abs x, ?_⟩
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    Pi.sum_norm_apply_le_norm (fun j => x j)

/-- The sum norm and Euclidean norm give the same topology. -/
noncomputable def sumEuclideanHomeomorph (k : ℕ) :
    PiLp 1 (fun _ : Fin k => ℝ) ≃ₜ CommodityEuclidean k :=
  (PiLp.homeomorph 1 (fun _ : Fin k => ℝ)).trans
    (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm

/-- This homeomorphism preserves every coordinate. -/
theorem sumEuclideanHomeomorph_apply {k : ℕ} (x : PiLp 1 (fun _ : Fin k => ℝ))
    (j : Fin k) : sumEuclideanHomeomorph k x j = x j := rfl

/-- **Definition A2.11:** Euclidean boundedness is equivalent to uniform coordinate bounds. -/
theorem appendix2_bounded_coordinates {k : ℕ} (S : Set (CommodityEuclidean k)) :
    Bornology.IsBounded S ↔ ∃ M > 0, ∀ x ∈ S, ∀ j, |x j| < M := by
  constructor
  · intro h
    obtain ⟨M, hM, hb⟩ := h.exists_pos_norm_le
    refine ⟨M + 1, by linarith, fun x hx j => ?_⟩
    have hj : |x j| ≤ M := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x j).trans (hb x hx)
    linarith
  · rintro ⟨M, _, hb⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨k * M, fun x hx => ?_⟩
    calc
      ‖x‖ ≤ ∑ j, |x j| := euclidean_norm_le_sum_abs x
      _ ≤ ∑ _j : Fin k, M := Finset.sum_le_sum fun j _ => (hb x hx j).le
      _ = k * M := by simp

/-- The first point in the book's three-distance example. -/
def AppendixDistancePointA : Fin 2 → ℝ := ![1, 3]

/-- The second point in the example. -/
def AppendixDistancePointB : Fin 2 → ℝ := ![5, 0]

/-- The ordinary Euclidean distance in the displayed example is five. -/
theorem appendix2_example_euclidean_distance :
    dist (WithLp.toLp 2 AppendixDistancePointA) (WithLp.toLp 2 AppendixDistancePointB) = 5 := by
  norm_num [definition_A2_1, AppendixDistancePointA, AppendixDistancePointB,
    Fin.sum_univ_two, PiLp.toLp_apply, Real.sqrt_eq_iff_eq_sq]

/-- The supremum distance in the same example is four. -/
theorem appendix2_example_supremum_distance :
    dist AppendixDistancePointA AppendixDistancePointB = 4 := by
  norm_num [dist_pi_def, Finset.univ_fin2, AppendixDistancePointA, AppendixDistancePointB,
    Real.nndist_eq, Real.dist_eq]

/-- The sum (Manhattan) distance in the same example is seven. -/
theorem appendix2_example_sum_distance :
    dist (WithLp.toLp 1 AppendixDistancePointA) (WithLp.toLp 1 AppendixDistancePointB) = 7 := by
  norm_num [PiLp.dist_eq_of_L1, AppendixDistancePointA, AppendixDistancePointB,
    Fin.sum_univ_two, PiLp.toLp_apply, Real.dist_eq]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cardinal ranks on the dyadic mean grid

An index `k` at subdivision level `n` receives rank `k / 2 ^ n`. The strict
ordering of every common refinement makes this assignment independent of the
chosen subdivision level. Suprema of lower ranks then extend it to all points.
-/

namespace Kreps.PreferenceProperties

variable {α : Type*} [LinearOrder α]

/-- The numerical rank of an index in a dyadic grid. -/
noncomputable def MeanDyadicRank (n k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ n

/-- Valid grid indices have ranks between zero and one. -/
theorem meanDyadicRank_mem (n k : ℕ) (hk : k ≤ 2 ^ n) :
    MeanDyadicRank n k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg k) (by positivity)
  · apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).2
    exact_mod_cast hk

/-- Cross-level grid comparisons coincide exactly with comparisons of their dyadic ranks. -/
theorem meanDyadicGrid_le_iff_rank (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (n m i j : ℕ) (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ m) :
    MeanDyadicGrid M.mean a b n i ≤ MeanDyadicGrid M.mean a b m j ↔
      MeanDyadicRank n i ≤ MeanDyadicRank m j := by
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hleft := meanDyadicGrid_refine M a b n m i
  have hright := meanDyadicGrid_refine M a b m n j
  rw [Nat.add_comm m n] at hright
  rw [← hleft, ← hright,
    (meanDyadicGrid_strictMonoOn M hab (n + m)).le_iff_le hi' hj']
  unfold MeanDyadicRank
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast

/-- The lower numerical ranks at an arbitrary point. -/
def MeanRankCut (M : OrderedBisymmetricMean α) (a b x : α) : Set ℝ :=
  {q | ∃ n k, k ≤ 2 ^ n ∧ q = MeanDyadicRank n k ∧ MeanDyadicGrid M.mean a b n k ≤ x}

/-- The left endpoint's rank ensures each cut is nonempty. -/
theorem meanRankCut_nonempty (M : OrderedBisymmetricMean α) (a b x : α) (hax : a ≤ x) :
    (MeanRankCut M a b x).Nonempty := by
  refine ⟨0, 0, 0, by norm_num, by simp [MeanDyadicRank], ?_⟩
  simpa only [meanDyadicGrid_left] using hax

/-- One bounds every lower dyadic cut. -/
theorem meanRankCut_bddAbove (M : OrderedBisymmetricMean α) (a b x : α) :
    BddAbove (MeanRankCut M a b x) := by
  refine ⟨1, ?_⟩
  rintro q ⟨n, k, hk, rfl, _⟩
  exact (meanDyadicRank_mem n k hk).2

/-- Extending the prescribed dyadic ranks by their lower-cut suprema. -/
noncomputable def MeanCardinalScale (M : OrderedBisymmetricMean α) (a b x : α) : ℝ :=
  sSup (MeanRankCut M a b x)

/-- The completed scale stays in the unit interval. -/
theorem meanCardinalScale_mem (M : OrderedBisymmetricMean α) (a b x : α) (hax : a ≤ x) :
    MeanCardinalScale M a b x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply le_csSup (meanRankCut_bddAbove M a b x)
    refine ⟨0, 0, by norm_num, by simp [MeanDyadicRank], ?_⟩
    simpa only [meanDyadicGrid_left] using hax
  · apply csSup_le (meanRankCut_nonempty M a b x hax)
    rintro q ⟨n, k, hk, rfl, _⟩
    exact (meanDyadicRank_mem n k hk).2

/-- Inclusion of lower cuts makes the scale monotone. -/
theorem meanCardinalScale_mono (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) : Monotone (MeanCardinalScale M a b) := by
  intro x y hxy
  apply csSup_le (meanRankCut_nonempty M a b x (ha x))
  rintro q ⟨n, k, hk, rfl, hx⟩
  exact le_csSup (meanRankCut_bddAbove M a b y) ⟨n, k, hk, rfl, hx.trans hxy⟩

/-- The supremum extension agrees with every original grid rank. -/
theorem meanCardinalScale_grid (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    MeanCardinalScale M a b (MeanDyadicGrid M.mean a b n k) = MeanDyadicRank n k := by
  apply le_antisymm
  · apply csSup_le (meanRankCut_nonempty M a b _ (ha _))
    rintro q ⟨m, i, hi, rfl, hle⟩
    exact (meanDyadicGrid_le_iff_rank M hab m n i k hi hk).1 hle
  · exact le_csSup (meanRankCut_bddAbove M a b _) ⟨n, k, hk, rfl, le_rfl⟩

/-- Density of the grid makes the completed scale strictly increasing. -/
theorem meanCardinalScale_strictMono [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b)
    (ha : ∀ x, a ≤ x) (hd : Dense (MeanDyadicPoints M a b)) :
    StrictMono (MeanCardinalScale M a b) := by
  intro x y hxy
  obtain ⟨u, hu, hxu, huy⟩ := hd.exists_between hxy
  obtain ⟨v, hv, huv, hvy⟩ := hd.exists_between huy
  obtain ⟨n, i, hi, rfl⟩ := hu
  obtain ⟨m, j, hj, rfl⟩ := hv
  have hlt : MeanDyadicRank n i < MeanDyadicRank m j := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt huv) ((meanDyadicGrid_le_iff_rank M hab m n j i hj hi).2 h)
  calc
    MeanCardinalScale M a b x ≤ MeanDyadicRank n i := by
      rw [← meanCardinalScale_grid M hab ha n i hi]
      exact meanCardinalScale_mono M a b ha hxu.le
    _ < MeanDyadicRank m j := hlt
    _ ≤ MeanCardinalScale M a b y := by
      rw [← meanCardinalScale_grid M hab ha m j hj]
      exact meanCardinalScale_mono M a b ha hvy.le

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuation of affine interval coordinates

Compatible coordinates can be glued across overlapping intervals. Taking all continuations of
a seed chart gives a maximal domain; local charts extend it through any boundary point inside
the underlying interval. The construction uses agreement on overlaps rather than a maximality
principle.
-/

namespace Kreps.PreferenceProperties

open Set
open scoped Topology

/-- Compatibility is unchanged when a coordinate is replaced by an equal one on its domain. -/
theorem PositiveAffineIntervalAtlas.Compatible.congr {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f g : ℝ → ℝ}
    (h : a.Compatible f D) (he : EqOn g f D) : a.Compatible g D := by
  intro i x hx
  obtain ⟨U, hU, hxU, hsub, A, B, hA, hEq⟩ := h i x hx
  exact ⟨U, hU, hxU, hsub, A, B, hA, fun y hy => (he (hsub hy).1).trans (hEq y hy)⟩

/-- Locally compatible coordinates remain compatible on the union of their domains. -/
theorem PositiveAffineIntervalAtlas.Compatible.union {ι : Type*} {S D E : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ}
    (hD : a.Compatible f D) (hE : a.Compatible f E) : a.Compatible f (D ∪ E) := by
  intro i x hx
  rcases hx.1 with hxD | hxE
  · obtain ⟨U, hU, hxU, hsub, A, B, hA, he⟩ := hD i x ⟨hxD, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨Or.inl (hsub hy).1, (hsub hy).2⟩, A, B, hA, he⟩
  · obtain ⟨U, hU, hxU, hsub, A, B, hA, he⟩ := hE i x ⟨hxE, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨Or.inr (hsub hy).1, (hsub hy).2⟩, A, B, hA, he⟩

/-- A positive affine rescaling preserves compatibility with the atlas. -/
theorem PositiveAffineIntervalAtlas.Compatible.positive_affine {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ}
    (h : a.Compatible f D) {A B : ℝ} (hA : 0 < A) :
    a.Compatible (fun x => A * f x + B) D := by
  intro i x hx
  obtain ⟨U, hU, hxU, hsub, C, F, hC, he⟩ := h i x hx
  refine ⟨U, hU, hxU, hsub, A * C, A * F + B, mul_pos hA hC, ?_⟩
  intro y hy
  change A * f y + B = _
  rw [he y hy]
  ring

/-- A continuation extends over every chart whose domain meets it. -/
theorem AffineIntervalSection.extend {ι : Type*} {S : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {seed : ι}
    (p : AffineIntervalSection a seed) (i : ι)
    (hne : (p.domain ∩ a.domain i).Nonempty) :
    ∃ q : AffineIntervalSection a seed, q.domain = p.domain ∪ a.domain i ∧
      EqOn q.value p.value p.domain := by
  classical
  obtain ⟨A, B, hA, he⟩ := p.compatible.affine p.interval i
  let g : ℝ → ℝ := fun x => A * a.coord i x + B
  let f : ℝ → ℝ := p.domain.piecewise p.value g
  have hfD : EqOn f p.value p.domain := fun x hx => by simp [f, hx]
  have hfU : EqOn f g (a.domain i) := by
    intro x hx
    by_cases hxD : x ∈ p.domain
    · simpa [f, hxD, g] using he x ⟨hxD, hx⟩
    · simp [f, hxD]
  have hg : ContinuousOn g (a.domain i) :=
    (continuousOn_const.mul (a.continuous i)).add continuousOn_const
  have hgm : StrictMonoOn g (a.domain i) := by
    intro x hx y hy hxy
    dsimp [g]
    nlinarith [a.increasing i hx hy hxy]
  have hfDc := p.continuous.congr hfD
  have hfUc := hg.congr hfU
  have hfDm : StrictMonoOn f p.domain := by
    intro x hx y hy hxy
    rw [hfD hx, hfD hy]
    exact p.increasing hx hy hxy
  have hfUm : StrictMonoOn f (a.domain i) := by
    intro x hx y hy hxy
    rw [hfU hx, hfU hy]
    exact hgm hx hy hxy
  obtain ⟨x, hxD, hxU⟩ := hne
  let q : AffineIntervalSection a seed := {
    domain := p.domain ∪ a.domain i
    isOpen := p.isOpen.union (a.isOpen i)
    interval := (p.interval.isPreconnected.union x hxD hxU
      (a.interval i).isPreconnected).ordConnected
    subset := union_subset p.subset (a.subset i)
    value := f
    continuous := hfDc.union_of_isOpen hfUc p.isOpen (a.isOpen i)
    increasing := strictMonoOn_union_intervals p.interval (a.interval i)
      ⟨x, hxD, hxU⟩ hfDm hfUm
    compatible := (p.compatible.congr hfD).union
      (((a.compatible_chart i).positive_affine hA).congr hfU)
    seed_subset := fun _ hx => Or.inl (p.seed_subset hx)
    seed_eq := fun y hy => (hfD (p.seed_subset hy)).trans (p.seed_eq y hy) }
  exact ⟨q, rfl, hfD⟩

/-- Seed-normalized continuations reach every point of the underlying interval. -/
theorem PositiveAffineIntervalAtlas.sections_cover {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∀ x ∈ S, ∃ p : AffineIntervalSection a seed, x ∈ p.domain := by
  let U : Set ℝ := ⋃ p : AffineIntervalSection a seed, p.domain
  have hU : IsOpen U := isOpen_iUnion fun p => p.isOpen
  have hSU : (S ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, a.subset seed hx, mem_iUnion.mpr ⟨a.seedSection seed, hx⟩⟩
  have hclosed : closure U ∩ S ⊆ U := by
    intro x hx
    obtain ⟨i, hxi⟩ := a.cover x hx.2
    obtain ⟨y, hyi, hyU⟩ := mem_closure_iff.mp hx.1 (a.domain i) (a.isOpen i) hxi
    obtain ⟨p, hyp⟩ := mem_iUnion.mp hyU
    obtain ⟨q, hq, _⟩ := p.extend i ⟨y, hyp, hyi⟩
    exact mem_iUnion.mpr ⟨q, hq ▸ Or.inr hxi⟩
  have hfull := hS.isPreconnected.subset_of_closure_inter_subset hU hSU hclosed
  exact fun x hx => mem_iUnion.mp (hfull hx)

/-- An oriented affine atlas on an open real interval has a global seed-normalized coordinate. -/
theorem PositiveAffineIntervalAtlas.exists_global_section {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∃ p : AffineIntervalSection a seed, p.domain = S := by
  classical
  choose p hp using fun x : S => a.sections_cover hS seed hne x x.property
  let f : ℝ → ℝ := fun x => if hx : x ∈ S then (p ⟨x, hx⟩).value x else 0
  have he (q : AffineIntervalSection a seed) : EqOn f q.value q.domain := by
    intro x hx
    have hxS := q.subset hx
    simp only [f, dite_eq_left hxS]
    exact AffineIntervalSection.unique hne (p ⟨x, hxS⟩) q ⟨hp ⟨x, hxS⟩, hx⟩
  have hm (q : AffineIntervalSection a seed) : StrictMonoOn f q.domain := by
    intro x hx y hy hxy
    rw [he q hx, he q hy]
    exact q.increasing hx hy hxy
  have hSo : IsOpen S := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨i, hxi⟩ := a.cover x hx
    exact ⟨a.domain i, a.subset i, a.isOpen i, hxi⟩
  have hc : ContinuousOn f S := by
    apply continuousOn_of_locally_continuousOn
    intro x hx
    exact ⟨(p ⟨x, hx⟩).domain, (p ⟨x, hx⟩).isOpen, hp ⟨x, hx⟩,
      ((p ⟨x, hx⟩).continuous.congr (he (p ⟨x, hx⟩))).mono inter_subset_right⟩
  have hmono : StrictMonoOn f S := by
    obtain ⟨z, hz⟩ := hne
    intro x hx y hy hxy
    let q := p ⟨x, hx⟩
    let r := p ⟨y, hy⟩
    exact strictMonoOn_union_intervals q.interval r.interval
      ⟨z, q.seed_subset hz, r.seed_subset hz⟩ (hm q) (hm r)
      (Or.inl (hp ⟨x, hx⟩)) (Or.inr (hp ⟨y, hy⟩)) hxy
  have hcomp : a.Compatible f S := by
    intro i x hx
    let q := p ⟨x, hx.1⟩
    obtain ⟨U, hU, hxU, hsub, A, B, hA, hEq⟩ := q.compatible i x ⟨hp ⟨x, hx.1⟩, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨q.subset (hsub hy).1, (hsub hy).2⟩,
      A, B, hA, fun y hy => (he q (hsub hy).1).trans (hEq y hy)⟩
  refine ⟨{
    domain := S
    isOpen := hSo
    interval := hS
    subset := Subset.rfl
    value := f
    continuous := hc
    increasing := hmono
    compatible := hcomp
    seed_subset := a.subset seed
    seed_eq := fun x hx => he (a.seedSection seed) hx }, rfl⟩

/-- A global scale is continuous and increasing, with explicit positive affine chart changes. -/
theorem PositiveAffineIntervalAtlas.globalize {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ a.domain seed, f x = a.coord seed x) ∧
      ∀ i, ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ a.domain i, f x = A * a.coord i x + B := by
  obtain ⟨p, hp⟩ := a.exists_global_section hS seed hne
  refine ⟨p.value, ?_, ?_, p.seed_eq, fun i => ?_⟩
  · simpa only [hp] using p.continuous
  · simpa only [hp] using p.increasing
  · obtain ⟨A, B, hA, he⟩ := p.compatible.affine p.interval i
    refine ⟨A, B, hA, fun x hx => he x ⟨?_, hx⟩⟩
    simpa only [hp] using a.subset i hx

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bounds on interior additive coordinates at attained endpoints

Preparation for Proposition 2.14. A continuous strictly increasing preference utility on a
finite product prevents an interior additive coordinate from diverging at an attained endpoint.
An interior change in a companion coordinate gives the strict comparison needed for the bound.
No boundedness or endpoint limit of the additive coordinate is assumed.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Replacing one coordinate changes an additive score by its coordinate-score difference. -/
theorem sum_coordinate_scores_update {I : Type*} [Fintype I] [DecidableEq I]
    {B : I → Type*} (f : ∀ i, B i → ℝ) (z : ∀ i, B i) (i : I) (x : B i) :
    (∑ k, f k (Function.update z i x k)) = (∑ k, f k (z k)) - f i (z i) + f i x := by
  simp_rw [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add Finset.univ (fun k => f k (z k)) (Finset.mem_univ i)
  linarith

/-- Interior inclusion commutes with coordinate replacement. -/
theorem interior_product_inclusion_update {I : Type*} [DecidableEq I] {S : I → Set ℝ}
    (z : ∀ i, interior (S i)) (i : I) (x : interior (S i)) :
    (fun k => inclusion interior_subset (Function.update z i x k)) =
      Function.update (fun k => inclusion interior_subset (z k)) i
        (inclusion interior_subset x) :=
  funext (Function.apply_update (fun k => inclusion (s := interior (S k)) interior_subset) z i x)

/-- Fixing all other coordinates cancels their contribution to interior additive comparisons. -/
theorem interior_additive_pair_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} {f : ∀ i, interior (S i) → ℝ}
    (hr : ∀ x y : ∀ i, interior (S i),
      V (fun i => inclusion interior_subset (x i)) ≤
          V (fun i => inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i))
    (z : ∀ i, interior (S i)) {i j : I} (hij : i ≠ j)
    (x y : interior (S i)) (b c : interior (S j)) :
    V (Function.update (Function.update (fun k => inclusion interior_subset (z k))
        j (inclusion interior_subset b)) i (inclusion interior_subset x)) ≤
      V (Function.update (Function.update (fun k => inclusion interior_subset (z k))
        j (inclusion interior_subset c)) i (inclusion interior_subset y)) ↔
      f i x + f j b ≤ f i y + f j c := by
  have h := hr (Function.update (Function.update z j b) i x)
    (Function.update (Function.update z j c) i y)
  simp_rw [interior_product_inclusion_update] at h
  rw [sum_coordinate_scores_update, sum_coordinate_scores_update,
    sum_coordinate_scores_update, sum_coordinate_scores_update] at h
  simp only [Function.update_of_ne hij] at h
  exact h.trans (by constructor <;> intro hle <;> linarith)

/-- Every attained least or greatest rank gives a finite bound on its interior additive scale. -/
theorem interior_additive_scale_bounds {I : Type*} [Fintype I] [Nontrivial I]
    {S : I → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hne : ∀ i, (interior (S i)).Nonempty) {V : (∀ i, S i) → ℝ}
    (hc : Continuous V) (hm : StrictMono V) {f : ∀ i, interior (S i) → ℝ}
    (hr : ∀ x y : ∀ i, interior (S i),
      V (fun i => inclusion interior_subset (x i)) ≤
          V (fun i => inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i)) (i : I) :
    (∀ a : S i, IsBot a → BddBelow (range (f i))) ∧
      ∀ a : S i, IsTop a → BddAbove (range (f i)) := by
  classical
  choose z hz using fun k => hne k
  let q : ∀ k, interior (S k) := fun k => ⟨z k, hz k⟩
  let qFull : ∀ k, S k := fun k => inclusion interior_subset (q k)
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := Ne.symm hji
  obtain ⟨L, R, hLR, hsub⟩ := isOpen_interior.exists_Ioo_subset (hne j)
  obtain ⟨b', hLb, hbR⟩ := exists_between hLR
  obtain ⟨c', hbc, hcR⟩ := exists_between hbR
  let b : interior (S j) := ⟨b', hsub ⟨hLb, hbR⟩⟩
  let c : interior (S j) := ⟨c', hsub ⟨hLb.trans hbc, hcR⟩⟩
  let D : Set (S i) := {x | x.val ∈ interior (S i)}
  let f' : S i → ℝ := fun x => if hx : x.val ∈ interior (S i) then f i ⟨x.val, hx⟩ else 0
  have hf' (x : S i) (hx : x ∈ D) : f' x = f i ⟨x.val, hx⟩ := by
    have hx' : x.val ∈ interior (S i) := hx
    simp [f', hx']
  have himage : f' '' D = range (f i) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, hx⟩, (hf' x hx).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨inclusion interior_subset x, x.property, hf' _ x.property⟩
  let u : S i × interior (S j) → ℝ := fun p =>
    V (Function.update (Function.update qFull j (inclusion interior_subset p.2)) i p.1)
  have huc (d : interior (S j)) : Continuous (fun x : S i => u (x, d)) := by
    change Continuous (fun x : S i => V
      (Function.update (Function.update qFull j (inclusion interior_subset d)) i x))
    exact hc.comp (continuous_const.update i continuous_id)
  have hum (d : interior (S j)) : Monotone (fun x : S i => u (x, d)) := by
    change Monotone (fun x : S i => V
      (Function.update (Function.update qFull j (inclusion interior_subset d)) i x))
    exact hm.monotone.comp Function.update_mono
  have hubc (a : S i) : u (a, b) < u (a, c) := by
    dsimp [u]
    rw [Function.update_comm hji, Function.update_comm hji]
    exact hm (Function.update_strictMono hbc)
  have hur : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f' x + f j b ≤ f' y + f j c := by
    intro x hx y hy
    rw [hf' x hx, hf' y hy]
    exact interior_additive_pair_comparison hr q hij ⟨x.val, hx⟩ ⟨y.val, hy⟩ b c
  constructor
  · intro a ha
    have h := additive_scale_bddBelow_at_least (interval_interior_dense (hS i) (hne i))
      ha (huc b) (hum c) (hubc a) hur
    rwa [himage] at h
  · intro a ha
    have h := additive_scale_bddAbove_at_greatest (interval_interior_dense (hS i) (hne i))
      ha (huc c) (hum b) (hubc a) hur
    rwa [himage] at h

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Equivalent utility representations

Kreps I, §1.7, Propositions 1.20-1.21, pp. 17-18, and Problem 1.14, p. 27.
The transformation need only be strictly increasing on the attained utility range.
A globally nondecreasing extension exists with values in the extended reals.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop} {u v : X → ℝ}

/-- **Proposition 1.20**, p. 17: strictly increasing transforms preserve representation. -/
theorem proposition_1_20 (hu : Represents u r) {f : ℝ → ℝ} (hf : StrictMono f) :
    Represents (f ∘ u) r := by
  intro x y
  exact (hu x y).trans hf.le_iff_le.symm

/-- Two utilities representing the same preference have identical equality fibers. -/
theorem same_utility_fibers (hu : Represents u r) (hv : Represents v r)
    {x y : X} (h : u x = u y) : v x = v y := by
  apply le_antisymm
  · exact (hv y x).mp ((hu y x).mpr h.le)
  · exact (hv x y).mp ((hu x y).mpr h.ge)

/-- Choose a value on the attained range and extend arbitrarily elsewhere. -/
noncomputable def UtilityTransform (u v : X → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, u x = t then v (Classical.choose h) else 0

/-- The transformation recovers the second utility exactly. -/
theorem utilityTransform_apply (hu : Represents u r) (hv : Represents v r) (x : X) :
    UtilityTransform u v (u x) = v x := by
  classical
  unfold UtilityTransform
  rw [dite_eq_left (show ∃ y, u y = u x from ⟨x, rfl⟩)]
  exact same_utility_fibers hu hv (Classical.choose_spec (show ∃ y, u y = u x from ⟨x, rfl⟩))

/-- The transformation is strictly increasing on the original utility range. -/
theorem utilityTransform_strictMonoOn (hu : Represents u r) (hv : Represents v r) :
    StrictMonoOn (UtilityTransform u v) (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [utilityTransform_apply hu hv x, utilityTransform_apply hu hv y]
  exact (strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy)

/-- A transformation strictly increasing only on attained values still preserves preference. -/
theorem represents_of_transform_on_range (hu : Represents u r) {f : ℝ → ℝ}
    (hf : StrictMonoOn f (Set.range u)) (hv : ∀ x, v x = f (u x)) : Represents v r := by
  intro x y
  rw [hv x, hv y]
  exact (hu x y).trans (hf.le_iff_le ⟨y, rfl⟩ ⟨x, rfl⟩).symm

/-- **Proposition 1.21**, p. 18: exact characterization, with `u` a representation. -/
theorem proposition_1_21 (hu : Represents u r) :
    Represents v r ↔ ∃ f : ℝ → ℝ, StrictMonoOn f (Set.range u) ∧ ∀ x, v x = f (u x) := by
  constructor
  · intro hv
    exact ⟨UtilityTransform u v, utilityTransform_strictMonoOn hu hv,
      fun x => (utilityTransform_apply hu hv x).symm⟩
  · rintro ⟨f, hf, hv⟩
    exact represents_of_transform_on_range hu hf hv

/-- Problem 1.14d's supremum extension, allowing empty and unbounded lower sections. -/
noncomputable def ExtendedUtilityTransform (u v : X → ℝ) (t : ℝ) : EReal :=
  sSup {a : EReal | ∃ x, u x ≤ t ∧ a = (v x : EReal)}

/-- The supremum extension is nondecreasing on all real arguments. -/
theorem extendedUtilityTransform_monotone (u v : X → ℝ) :
    Monotone (ExtendedUtilityTransform u v) := by
  intro a b hab
  apply sSup_le_sSup
  rintro t ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans hab, rfl⟩

/-- At an attained value the supremum is exactly the corresponding second utility. -/
theorem extendedUtilityTransform_apply (hu : Represents u r) (hv : Represents v r) (x : X) :
    ExtendedUtilityTransform u v (u x) = (v x : EReal) := by
  apply le_antisymm
  · apply sSup_le
    rintro t ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe ((hv x y).mp ((hu x y).mpr hy))
  · apply le_sSup
    exact ⟨x, le_rfl, rfl⟩

/-- The extended-real transformation is strictly increasing on the attained range. -/
theorem extendedUtilityTransform_strictMonoOn (hu : Represents u r) (hv : Represents v r) :
    StrictMonoOn (ExtendedUtilityTransform u v) (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [extendedUtilityTransform_apply hu hv x, extendedUtilityTransform_apply hu hv y]
  exact EReal.coe_lt_coe
    ((strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy))

/-- The extended-real conclusion of **Proposition 1.21**, p. 18. -/
theorem proposition_1_21_extension (hu : Represents u r) (hv : Represents v r) :
    ∃ f : ℝ → EReal, Monotone f ∧ StrictMonoOn f (Set.range u) ∧
      ∀ x, f (u x) = (v x : EReal) :=
  ⟨ExtendedUtilityTransform u v, extendedUtilityTransform_monotone u v,
    extendedUtilityTransform_strictMonoOn hu hv, extendedUtilityTransform_apply hu hv⟩

/-- **Problem 1.14a**, p. 27: the represented relations coincide. -/
theorem problem_1_14a {s : X → X → Prop} (hu : Represents u r) (hv : Represents v s)
    {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.range u)) (hvu : ∀ x, v x = f (u x)) : r = s := by
  funext x y
  exact propext ((represents_of_transform_on_range hu hf hvu x y).trans (hv x y).symm)

/-- **Problem 1.14b**, p. 27: any given transformation is strict on attained values. -/
theorem problem_1_14b (hu : Represents u r) (hv : Represents v r)
    {f : ℝ → ℝ} (hvu : ∀ x, v x = f (u x)) : StrictMonoOn f (Set.range u) := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy
  rw [← hvu x, ← hvu y]
  exact (strict_iff_utility_lt hv y x).mp ((strict_iff_utility_lt hu y x).mpr hxy)

/-- **Problem 1.14d**, p. 27: the actual supremum construction and both order properties. -/
theorem problem_1_14d (hu : Represents u r) (hv : Represents v r) :
    Monotone (ExtendedUtilityTransform u v) ∧
      StrictMonoOn (ExtendedUtilityTransform u v) (Set.range u) ∧
      ∀ x, ExtendedUtilityTransform u v (u x) = (v x : EReal) :=
  ⟨extendedUtilityTransform_monotone u v, extendedUtilityTransform_strictMonoOn hu hv,
    extendedUtilityTransform_apply hu hv⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Continuous preferences

Kreps I, Definition 1.13 and Proposition 1.14, pp. 13-14; Problem 1.11.
Continuity is expressed by openness of the strict graph. The metric characterization
uses exactly the common-radius condition in the definition. The contour results hold
on any topological space; the sequence equivalences require a sequential space.
-/

open Filter Topology

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- The upper weak contour, denoted NWT in the book. -/
def NoWorseThan (r : X → X → Prop) (x : X) : Set X := {y | r y x}

/-- The strict upper contour, denoted SBT in the book. -/
def StrictlyBetterThan (r : X → X → Prop) (x : X) : Set X := {y | Strict r y x}

/-- The strict lower contour, denoted SWT in the book. -/
def StrictlyWorseThan (r : X → X → Prop) (x : X) : Set X := {y | Strict r x y}

/-- Topological form of **Definition 1.13**, without bundling rationality. -/
def ContinuousPreference [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  IsOpen {p : X × X | Strict r p.1 p.2}

/-- The common-radius condition in **Definition 1.13**, p. 13. -/
def MetricContinuousPreference [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x y, Strict r x y → ∃ ε > 0, ∀ x' y',
    dist x' x < ε → dist y' y < ε → Strict r x' y'

/-- The graph definition agrees with the book's metric definition. -/
theorem continuousPreference_iff_metric [PseudoMetricSpace X] :
    ContinuousPreference r ↔ MetricContinuousPreference r := by
  constructor
  · intro h x y hxy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h (x, y) hxy
    refine ⟨ε, hε, fun x' y' hx hy => hball (show (x', y') ∈ Metric.ball (x, y) ε from ?_)⟩
    change max (dist x' x) (dist y' y) < ε
    exact max_lt hx hy
  · intro h
    apply Metric.isOpen_iff.mpr
    rintro ⟨x, y⟩ hxy
    obtain ⟨ε, hε, hball⟩ := h x y hxy
    refine ⟨ε, hε, ?_⟩
    rintro ⟨x', y'⟩ hdist
    change max (dist x' x) (dist y' y) < ε at hdist
    exact hball x' y' (max_lt_iff.mp hdist).1 (max_lt_iff.mp hdist).2

/-- A continuous real utility induces a continuous preference. -/
theorem continuousPreference_of_continuous_utility [TopologicalSpace X]
    {u : X → ℝ} (hu : Continuous u) : ContinuousPreference (UtilityPref u) := by
  have heq : {p : X × X | Strict (UtilityPref u) p.1 p.2} =
      {p : X × X | u p.2 < u p.1} := by
    ext p
    exact lt_iff_le_not_ge.symm
  change IsOpen {p : X × X | Strict (UtilityPref u) p.1 p.2}
  rw [heq]
  exact isOpen_lt (hu.comp continuous_snd) (hu.comp continuous_fst)

/-- **Proposition 1.14c**, stated as a property of all weak contours. -/
def ClosedContours [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, IsClosed (NoBetterThan r x) ∧ IsClosed (NoWorseThan r x)

/-- **Proposition 1.14d**, stated as a property of all strict contours. -/
def OpenStrictContours [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, IsOpen (StrictlyBetterThan r x) ∧ IsOpen (StrictlyWorseThan r x)

/-- Strict graph continuity implies openness of each strict contour. -/
theorem continuousPreference_openStrictContours [TopologicalSpace X]
    (h : ContinuousPreference r) : OpenStrictContours r := by
  intro x
  exact ⟨h.preimage (continuous_id.prodMk continuous_const),
    h.preimage (continuous_const.prodMk continuous_id)⟩

/-- Closed weak contours and open strict contours are complementary descriptions. -/
theorem closedContours_iff_openStrictContours [TopologicalSpace X] (hc : Complete r) :
    ClosedContours r ↔ OpenStrictContours r := by
  have hu (x : X) : StrictlyBetterThan r x = (NoBetterThan r x)ᶜ := by
    ext y
    exact proposition_1_9a hc y x
  have hl (x : X) : StrictlyWorseThan r x = (NoWorseThan r x)ᶜ := by
    ext y
    exact proposition_1_9a hc x y
  constructor
  · intro h x
    exact ⟨hu x ▸ (h x).1.isOpen_compl, hl x ▸ (h x).2.isOpen_compl⟩
  · intro h x
    constructor
    · have hh := (h x).1.isClosed_compl
      simpa only [hu x, compl_compl] using hh
    · have hh := (h x).2.isClosed_compl
      simpa only [hl x, compl_compl] using hh

/-- Open strict contours imply joint continuity for a complete, transitive preference. -/
theorem openStrictContours_continuousPreference [TopologicalSpace X] (hr : Rational r)
    (h : OpenStrictContours r) : ContinuousPreference r := by
  apply isOpen_prod_iff.mpr
  intro x y hxy
  by_cases hm : ∃ z, Strict r x z ∧ Strict r z y
  · obtain ⟨z, hxz, hzy⟩ := hm
    refine ⟨StrictlyBetterThan r z, StrictlyWorseThan r z,
      (h z).1, (h z).2, hxz, hzy, ?_⟩
    intro p hp
    exact strict_weak_trans hr.2 hp.1 hp.2.1
  · refine ⟨StrictlyBetterThan r y, StrictlyWorseThan r x,
      (h y).1, (h x).2, hxy, hxy, ?_⟩
    intro p hp
    apply (proposition_1_9a hr.1 p.1 p.2).mpr
    intro hrev
    exact hm ⟨p.1, strict_weak_trans hr.2 hp.2 hrev, hp.1⟩

/-- **Proposition 1.14c**, both directions. -/
theorem proposition_1_14c [TopologicalSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ ClosedContours r :=
  ⟨fun h => (closedContours_iff_openStrictContours hr.1).mpr
    (continuousPreference_openStrictContours h),
    fun h => openStrictContours_continuousPreference hr
      ((closedContours_iff_openStrictContours hr.1).mp h)⟩

/-- **Proposition 1.14d**, both directions. -/
theorem proposition_1_14d [TopologicalSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ OpenStrictContours r :=
  ⟨continuousPreference_openStrictContours, openStrictContours_continuousPreference hr⟩

/-- **Proposition 1.14a**: both weak comparisons are preserved in a sequence limit. -/
def SequenceWeakContinuity [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ (u : ℕ → X) x y, Tendsto u atTop (𝓝 x) →
    ((∀ n, r (u n) y) → r x y) ∧ ((∀ n, r y (u n)) → r y x)

/-- **Proposition 1.14b**: both strict comparisons eventually hold along a convergent sequence. -/
def SequenceStrictContinuity [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  ∀ (u : ℕ → X) x y, Tendsto u atTop (𝓝 x) →
    (Strict r x y → ∀ᶠ n in atTop, Strict r (u n) y) ∧
      (Strict r y x → ∀ᶠ n in atTop, Strict r y (u n))

/-- **Proposition 1.14a**, both directions, on every sequential space. -/
theorem proposition_1_14a [TopologicalSpace X] [SequentialSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ SequenceWeakContinuity r := by
  rw [proposition_1_14c hr]
  constructor
  · intro h u x y ht
    exact ⟨fun hn => (h y).2.mem_of_tendsto ht (Eventually.of_forall hn),
      fun hn => (h y).1.mem_of_tendsto ht (Eventually.of_forall hn)⟩
  · intro h y
    constructor
    · apply isSeqClosed_iff_isClosed.mp
      intro u x hn ht
      exact (h u x y ht).2 hn
    · apply isSeqClosed_iff_isClosed.mp
      intro u x hn ht
      exact (h u x y ht).1 hn

/-- **Proposition 1.14b**, both directions, on every sequential space. -/
theorem proposition_1_14b [TopologicalSpace X] [SequentialSpace X] (hr : Rational r) :
    ContinuousPreference r ↔ SequenceStrictContinuity r := by
  constructor
  · intro h u x y ht
    have ho := continuousPreference_openStrictContours h
    exact ⟨fun hxy => ht ((ho y).1.mem_nhds hxy),
      fun hyx => ht ((ho y).2.mem_nhds hyx)⟩
  · intro h
    apply (proposition_1_14a hr).mpr
    intro u x y ht
    constructor
    · intro hn
      by_contra hxy
      obtain ⟨n, hny⟩ := ((h u x y ht).2 ((proposition_1_9a hr.1 y x).mpr hxy)).exists
      exact hny.2 (hn n)
    · intro hn
      by_contra hyx
      obtain ⟨n, hny⟩ := ((h u x y ht).1 ((proposition_1_9a hr.1 x y).mpr hyx)).exists
      exact hny.2 (hn n)

/-- **Problem 1.11**: all four characterizations, including the definition's metric form. -/
theorem problem_1_11 [PseudoMetricSpace X] (hr : Rational r) :
    (MetricContinuousPreference r ↔ SequenceWeakContinuity r) ∧
      (MetricContinuousPreference r ↔ SequenceStrictContinuity r) ∧
      (MetricContinuousPreference r ↔ ClosedContours r) ∧
      (MetricContinuousPreference r ↔ OpenStrictContours r) :=
  ⟨continuousPreference_iff_metric.symm.trans (proposition_1_14a hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14b hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14c hr),
    continuousPreference_iff_metric.symm.trans (proposition_1_14d hr)⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Lexicographic preferences have no real utility representation

Kreps I, Problem 1.10, p. 26. On the unit square these preferences are complete
and transitive. A putative representation would put disjoint nonempty utility
intervals above each first coordinate; selecting a rational inside each interval
would inject the uncountable unit interval into the rationals.
-/

namespace Kreps.PreferenceProperties

/-- The closed real unit interval, including both endpoints. -/
abbrev UnitSegment := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

/-- Lexicographic weak preference on the unit square. -/
def LexicographicPreference (x y : UnitSegment × UnitSegment) : Prop :=
  y.1.val < x.1.val ∨ y.1.val = x.1.val ∧ y.2.val ≤ x.2.val

/-- **Problem 1.10**, completeness and transitivity. -/
theorem lexicographic_rational : Rational LexicographicPreference := by
  constructor
  · intro x y
    rcases lt_trichotomy x.1.val y.1.val with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total y.2.val x.2.val with hyx | hxy
      · exact Or.inl (Or.inr ⟨h.symm, hyx⟩)
      · exact Or.inr (Or.inr ⟨h, hxy⟩)
    · exact Or.inl (Or.inl h)
  · rintro x y z (hxy | ⟨hexy, hxy⟩) (hyz | ⟨heyz, hyz⟩)
    · exact Or.inl (hyz.trans hxy)
    · left
      linarith
    · left
      linarith
    · exact Or.inr ⟨heyz.trans hexy, hyz.trans hxy⟩

/-- **Problem 1.10**, impossibility of any real-valued utility representation. -/
theorem lexicographic_not_representable :
    ¬∃ u : UnitSegment × UnitSegment → ℝ, Represents u LexicographicPreference := by
  classical
  rintro ⟨u, hu⟩
  let zero : UnitSegment := ⟨0, by constructor <;> norm_num⟩
  let one : UnitSegment := ⟨1, by constructor <;> norm_num⟩
  have hv (x : UnitSegment) : u (x, zero) < u (x, one) := by
    apply (strict_iff_utility_lt hu (x, one) (x, zero)).mp
    constructor
    · right
      exact ⟨rfl, by norm_num [zero, one]⟩
    · rintro (h | ⟨_, h⟩)
      · exact (lt_irrefl _) h
      · norm_num [zero, one] at h
  choose q hqlo hqhi using fun x => exists_rat_btwn (hv x)
  have hqmono : StrictMono q := by
    intro x y hxy
    have hxy' : x.val < y.val := hxy
    have hs : Strict LexicographicPreference (y, zero) (x, one) := by
      constructor
      · exact Or.inl hxy'
      · rintro (h | ⟨h, _⟩) <;> dsimp at h <;> linarith
    have hsep := (strict_iff_utility_lt hu (y, zero) (x, one)).mp hs
    have hq : (q x : ℝ) < (q y : ℝ) := (hqhi x).trans (hsep.trans (hqlo y))
    exact_mod_cast hq
  have hcount : Countable UnitSegment := hqmono.injective.countable
  have hset : (Set.Icc (0 : ℝ) 1).Countable := hcount
  have hbad := Cardinal.Real.Icc_countable_iff.mp hset
  norm_num at hbad

/-- **Problem 1.10**, its two requested conclusions together. -/
theorem problem_1_10 : Rational LexicographicPreference ∧
    ¬∃ u : UnitSegment × UnitSegment → ℝ, Represents u LexicographicPreference :=
  ⟨lexicographic_rational, lexicographic_not_representable⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One step of the recursive utility assignment

Kreps I, Problem 2.14(d), p. 49. A previously available numerical representation
supplies only comparisons. The new assigned value copies an indifferent point,
exceeds the previous maximum by one, falls below the previous minimum by one,
or is the midpoint between the adjacent assigned values. This file verifies that
one insertion preserves all comparisons with the previously assigned points.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*}

/-- The old numerical values preserve the order of the original ranks. -/
def RankPreserving (v u : I → ℝ) : Prop := ∀ i j, v i ≤ v j ↔ u i ≤ u j

/-- An order-preserving reassignment preserves strict comparisons too. -/
theorem rankPreserving_lt {v u : I → ℝ} (h : RankPreserving v u) (i j : I) :
    v i < v j ↔ u i < u j := by
  simp only [lt_iff_le_not_ge, ← h i j, ← h j i]

/-- The finite set of already assigned values strictly below a new rank. -/
def PreviousLowerRanks (v u : I → ℝ) (a : ℝ) : Set ℝ := u '' {i | v i < a}

/-- The finite set of already assigned values strictly above a new rank. -/
def PreviousUpperRanks (v u : I → ℝ) (a : ℝ) : Set ℝ := u '' {i | a < v i}

/-- The book's four-case rule for inserting one new rank. -/
noncomputable def InsertedRank (v u : I → ℝ) (a : ℝ) : ℝ := by
  classical
  exact if ht : ∃ i, v i = a then u ht.choose
    else if ∀ i, v i < a then sSup (Set.range u) + 1
    else if ∀ i, a < v i then sInf (Set.range u) - 1
    else (sSup (PreviousLowerRanks v u a) + sInf (PreviousUpperRanks v u a)) / 2

/-- Ties may be copied from any prior representative of that rank. -/
theorem insertedRank_tie {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} (i : I) (hi : v i = a) : InsertedRank v u a = u i := by
  classical
  have ht : ∃ j, v j = a := ⟨i, hi⟩
  rw [InsertedRank, dite_eq_left ht]
  apply le_antisymm
  · exact (h _ i).mp (le_of_eq (ht.choose_spec.trans hi.symm))
  · exact (h i _).mp (le_of_eq (hi.trans ht.choose_spec.symm))

/-- A strictly new highest rank receives the preceding maximum plus one. -/
theorem insertedRank_above {v u : I → ℝ} {a : ℝ} (ha : ∀ i, v i < a) :
    InsertedRank v u a = sSup (Set.range u) + 1 := by
  classical
  have ht : ¬ ∃ i, v i = a := by rintro ⟨i, hi⟩; exact (ha i).ne hi
  simp only [InsertedRank, dite_eq_right ht, ite_eq_left ha]

/-- A strictly new lowest rank receives the preceding minimum minus one. -/
theorem insertedRank_below [Nonempty I] {v u : I → ℝ} {a : ℝ}
    (ha : ∀ i, a < v i) : InsertedRank v u a = sInf (Set.range u) - 1 := by
  classical
  have ht : ¬ ∃ i, v i = a := by rintro ⟨i, hi⟩; exact (ha i).ne hi.symm
  have hn : ¬ ∀ i, v i < a := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (ha i).not_gt (h i)
  simp only [InsertedRank, dite_eq_right ht, ite_eq_right hn, ite_eq_left ha]

/-- With ranks on both sides and no tie, the insertion is the midpoint of its neighbors. -/
theorem insertedRank_between {v u : I → ℝ} {a : ℝ}
    (ht : ¬ ∃ i, v i = a) (hl : ∃ i, v i < a) (hh : ∃ i, a < v i) :
    InsertedRank v u a =
      (sSup (PreviousLowerRanks v u a) + sInf (PreviousUpperRanks v u a)) / 2 := by
  classical
  have hnlo : ¬ ∀ i, a < v i := by obtain ⟨i, hi⟩ := hl; exact fun h => hi.not_gt (h i)
  have hnhi : ¬ ∀ i, v i < a := by obtain ⟨i, hi⟩ := hh; exact fun h => hi.not_gt (h i)
  simp only [InsertedRank, dite_eq_right ht, ite_eq_right hnhi, ite_eq_right hnlo]

/-- The maximum lower assigned rank is strictly below the minimum upper assigned rank. -/
theorem previousRanks_gap [Finite I] {v u : I → ℝ} (h : RankPreserving v u) {a : ℝ}
    (hl : ∃ i, v i < a) (hh : ∃ i, a < v i) :
    sSup (PreviousLowerRanks v u a) < sInf (PreviousUpperRanks v u a) := by
  have hln : (PreviousLowerRanks v u a).Nonempty := by
    obtain ⟨i, hi⟩ := hl
    exact ⟨u i, i, hi, rfl⟩
  have hhn : (PreviousUpperRanks v u a).Nonempty := by
    obtain ⟨i, hi⟩ := hh
    exact ⟨u i, i, hi, rfl⟩
  have hlf : (PreviousLowerRanks v u a).Finite := (Set.toFinite _).image u
  have hhf : (PreviousUpperRanks v u a).Finite := (Set.toFinite _).image u
  obtain ⟨i, hi, he⟩ := hln.csSup_mem hlf
  obtain ⟨j, hj, hf⟩ := hhn.csInf_mem hhf
  rw [← he, ← hf]
  exact (rankPreserving_lt h i j).mp (hi.trans hj)

/-- Every lower old rank remains strictly below the newly assigned value. -/
theorem insertedRank_gt [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} {i : I} (hi : v i < a) : u i < InsertedRank v u a := by
  classical
  by_cases ht : ∃ j, v j = a
  · obtain ⟨j, hj⟩ := ht
    rw [insertedRank_tie h j hj]
    exact (rankPreserving_lt h i j).mp (hi.trans_eq hj.symm)
  by_cases hhi : ∀ j, v j < a
  · rw [insertedRank_above hhi]
    have hb := le_csSup (Set.finite_range u).bddAbove (Set.mem_range_self i)
    linarith
  have hh : ∃ j, a < v j := by
    push Not at hhi
    obtain ⟨j, hj⟩ := hhi
    exact ⟨j, lt_of_le_of_ne hj (fun he => ht ⟨j, he.symm⟩)⟩
  rw [insertedRank_between ht ⟨i, hi⟩ hh]
  have hgap := previousRanks_gap h ⟨i, hi⟩ hh
  have hb : u i ≤ sSup (PreviousLowerRanks v u a) :=
    le_csSup ((Set.toFinite _).image u).bddAbove ⟨i, hi, rfl⟩
  linarith

/-- Every higher old rank remains strictly above the newly assigned value. -/
theorem insertedRank_lt [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    {a : ℝ} {i : I} (hi : a < v i) : InsertedRank v u a < u i := by
  classical
  by_cases ht : ∃ j, v j = a
  · obtain ⟨j, hj⟩ := ht
    rw [insertedRank_tie h j hj]
    exact (rankPreserving_lt h j i).mp (hj.trans_lt hi)
  by_cases hlo : ∀ j, a < v j
  · rw [insertedRank_below hlo]
    have hb := csInf_le (Set.finite_range u).bddBelow (Set.mem_range_self i)
    linarith
  have hl : ∃ j, v j < a := by
    push Not at hlo
    obtain ⟨j, hj⟩ := hlo
    exact ⟨j, lt_of_le_of_ne hj (fun he => ht ⟨j, he⟩)⟩
  rw [insertedRank_between ht hl ⟨i, hi⟩]
  have hgap := previousRanks_gap h hl ⟨i, hi⟩
  have hb : sInf (PreviousUpperRanks v u a) ≤ u i :=
    csInf_le ((Set.toFinite _).image u).bddBelow ⟨i, hi, rfl⟩
  linarith

/-- The insertion preserves both weak comparisons with every previously assigned point. -/
theorem insertedRank_compare [Finite I] [Nonempty I] {v u : I → ℝ} (h : RankPreserving v u)
    (a : ℝ) (i : I) :
    (v i ≤ a ↔ u i ≤ InsertedRank v u a) ∧
      (a ≤ v i ↔ InsertedRank v u a ≤ u i) := by
  rcases lt_trichotomy (v i) a with hi | hi | hi
  · have hu := insertedRank_gt h hi
    exact ⟨iff_of_true hi.le hu.le, iff_of_false (not_le_of_gt hi) (not_le_of_gt hu)⟩
  · rw [insertedRank_tie h i hi, hi]
    simp
  · have hu := insertedRank_lt h hi
    exact ⟨iff_of_false (not_le_of_gt hi) (not_le_of_gt hu), iff_of_true hi.le hu.le⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: bounds and extrema

Definition A2.19 and Propositions A2.20–A2.21, pp. 448–450. Real suprema and
infima have explicit nonemptiness and boundedness hypotheses. Extended-real
suprema and infima implement the book's infinite and empty-set conventions.
-/

namespace Kreps.PreferenceProperties

/-- **Definition A2.19(a):** upper and lower bounds on a real set. -/
theorem definition_A2_19a (S : Set ℝ) :
    (BddAbove S ↔ ∃ M, ∀ x ∈ S, x ≤ M) ∧
      (BddBelow S ↔ ∃ m, ∀ x ∈ S, m ≤ x) := ⟨Iff.rfl, Iff.rfl⟩

/-- **Definition A2.19(b):** the real supremum is the least upper bound. -/
theorem definition_A2_19b {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    IsLUB S (sSup S) := isLUB_csSup hne hb

/-- **Definition A2.19(c):** the real infimum is the greatest lower bound. -/
theorem definition_A2_19c {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) :
    IsGLB S (sInf S) := isGLB_csInf hne hb

/-- **Definition A2.19(d):** a supremum belonging to the set is its maximum. -/
theorem definition_A2_19d_max {S : Set ℝ} (hb : BddAbove S) (hmem : sSup S ∈ S) :
    IsGreatest S (sSup S) := ⟨hmem, fun _ hx => le_csSup hb hx⟩

/-- **Definition A2.19(d):** an infimum belonging to the set is its minimum. -/
theorem definition_A2_19d_min {S : Set ℝ} (hb : BddBelow S) (hmem : sInf S ∈ S) :
    IsLeast S (sInf S) := ⟨hmem, fun _ hx => csInf_le hb hx⟩

/-- A nonempty bounded-above real set has the same supremum after embedding into extended reals. -/
theorem appendix2_extended_sup_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun x : ℝ => (x : EReal)) '' S) = ((sSup S : ℝ) : EReal) := by
  apply (isLUB_sSup _).unique
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe (le_csSup hb hx)
  · intro z hz
    induction z using EReal.rec with
    | bot =>
      obtain ⟨x, hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe x)) (hz ⟨x, hx, rfl⟩))
    | coe r =>
      exact EReal.coe_le_coe (csSup_le hne fun x hx =>
        EReal.coe_le_coe_iff.mp (hz ⟨x, hx, rfl⟩))
    | top => exact le_top

/-- The corresponding finite infimum agrees with the extended-real infimum. -/
theorem appendix2_extended_inf_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) = ((sInf S : ℝ) : EReal) := by
  apply (isGLB_sInf _).unique
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe (csInf_le hb hx)
  · intro z hz
    induction z using EReal.rec with
    | bot => exact bot_le
    | coe r =>
      exact EReal.coe_le_coe (le_csInf hne fun x hx =>
        EReal.coe_le_coe_iff.mp (hz ⟨x, hx, rfl⟩))
    | top =>
      obtain ⟨x, hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.coe_lt_top x)) (hz ⟨x, hx, rfl⟩))

/-- **Definition A2.19(b):** unboundedness above gives positive infinity. -/
theorem appendix2_extended_sup_unbounded {S : Set ℝ} (hS : ¬BddAbove S) :
    sSup ((fun x : ℝ => (x : EReal)) '' S) = ⊤ := by
  by_contra h
  apply hS
  refine ⟨(sSup ((fun x : ℝ => (x : EReal)) '' S)).toReal, fun x hx => ?_⟩
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.mp ((le_sSup hx').trans (EReal.le_coe_toReal h))

/-- **Definition A2.19(c):** unboundedness below gives negative infinity. -/
theorem appendix2_extended_inf_unbounded {S : Set ℝ} (hS : ¬BddBelow S) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) = ⊥ := by
  by_contra h
  apply hS
  refine ⟨(sInf ((fun x : ℝ => (x : EReal)) '' S)).toReal, fun x hx => ?_⟩
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.mp ((EReal.coe_toReal_le h).trans (sInf_le hx'))

/-- **Proposition A2.20(a):** the extended infimum is at most the supremum for a nonempty set. -/
theorem proposition_A2_20a {S : Set ℝ} (hne : S.Nonempty) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) ≤
      sSup ((fun x : ℝ => (x : EReal)) '' S) := by
  obtain ⟨x, hx⟩ := hne
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact (sInf_le hx').trans (le_sSup hx')

/-- **Proposition A2.20(b):** boundedness gives finite extended extrema on a nonempty real set. -/
theorem proposition_A2_20b {S : Set ℝ} (hne : S.Nonempty) :
    (BddAbove S → ∃ r : ℝ, sSup ((fun x : ℝ => (x : EReal)) '' S) = r) ∧
      (BddBelow S → ∃ r : ℝ, sInf ((fun x : ℝ => (x : EReal)) '' S) = r) :=
  ⟨fun h => ⟨sSup S, appendix2_extended_sup_finite hne h⟩,
    fun h => ⟨sInf S, appendix2_extended_inf_finite hne h⟩⟩

/-- **Proposition A2.20(c):** a nonempty compact real set has a maximum and a minimum. -/
theorem proposition_A2_20c {S : Set ℝ} (hne : S.Nonempty) (hS : IsCompact S) :
    IsGreatest S (sSup S) ∧ IsLeast S (sInf S) :=
  ⟨hS.isGreatest_sSup hne, hS.isLeast_sInf hne⟩

/-- The explicit empty-set conventions immediately following Proposition A2.20. -/
theorem appendix2_empty_extrema :
    sSup (∅ : Set EReal) = ⊥ ∧ sInf (∅ : Set EReal) = ⊤ := ⟨sSup_empty, sInf_empty⟩

/-- **Proposition A2.21:** a continuous function attains its finite supremum on a compact set. -/
theorem proposition_A2_21 {X : Type*} [TopologicalSpace X] {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hne : S.Nonempty) (hf : ContinuousOn f S) :
    BddAbove (f '' S) ∧ ∃ x ∈ S, f x = sSup (f '' S) ∧ ∀ y ∈ S, f y ≤ f x := by
  obtain ⟨x, hx, heq, hmax⟩ := hS.exists_sSup_image_eq_and_ge hne hf
  exact ⟨hS.bddAbove_image hf, x, hx, heq.symm, hmax⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: relative topology and examples

The half-open interval and infinite-intersection examples on p. 442, the
relative-topology exercises on p. 443, and the Lipschitz footnote on pp. 447–448.
-/

namespace Kreps.PreferenceProperties

/-- The interval `(0,1]` is neither open nor closed. -/
theorem appendix2_half_open_interval :
    ¬IsOpen (Set.Ioc (0 : ℝ) 1) ∧ ¬IsClosed (Set.Ioc (0 : ℝ) 1) := by
  constructor
  · intro h
    have he := h.interior_eq
    rw [interior_Ioc] at he
    have hmem : (1 : ℝ) ∈ Set.Ioo 0 1 := he.symm ▸ (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 1)
    exact (lt_irrefl (1 : ℝ)) hmem.2
  · intro h
    have he := h.closure_eq
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at he
    have hmem : (0 : ℝ) ∈ Set.Ioc 0 1 := he ▸ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    exact (lt_irrefl (0 : ℝ)) hmem.1

/-- An arbitrary intersection of open neighborhoods may fail to be open. -/
theorem appendix2_infinite_open_intersection :
    (∀ ε > 0, IsOpen (Metric.ball (0 : ℝ) ε)) ∧
      ¬IsOpen (⋂ ε > 0, Metric.ball (0 : ℝ) ε) := by
  refine ⟨fun _ _ => Metric.isOpen_ball, ?_⟩
  rw [Metric.biInter_gt_ball, Metric.closedBall_zero]
  exact not_isOpen_singleton 0

/-- A relatively open subset of an open domain is open in the ambient space. -/
theorem appendix2_relative_open_ambient {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsOpen S) {A : Set S} (hA : IsOpen A) : IsOpen (Subtype.val '' A) :=
  hS.isOpenMap_subtype_val A hA

/-- A relatively closed subset of a closed domain is closed in the ambient space. -/
theorem appendix2_relative_closed_ambient {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsClosed S) {A : Set S} (hA : IsClosed A) : IsClosed (Subtype.val '' A) :=
  hS.isClosedMap_subtype_val A hA

/-- Relative closure is ambient closure intersected with the domain, expressed by preimage. -/
theorem appendix2_relative_closure {X : Type*} [TopologicalSpace X] {S : Set X}
    (A : Set S) : closure A = Subtype.val ⁻¹' closure (Subtype.val '' A) :=
  Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image A

/-- The footnote's linear epsilon–delta rule is exactly a bound at the base point. -/
theorem appendix2_pointwise_lipschitz_rule {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) (x : X)
    {C : ℝ} (hC : 0 < C) :
    (∀ y, dist (f y) (f x) ≤ C * dist y x) ↔
      ∀ ε > 0, ∀ y, dist y x < ε / C → dist (f y) (f x) < ε := by
  constructor
  · intro h ε _ y hy
    have hd := (lt_div_iff₀ hC).mp hy
    have hf := h y
    nlinarith
  · intro h y
    by_contra hn
    have hlt : C * dist y x < dist (f y) (f x) := lt_of_not_ge hn
    have hpos : 0 < (dist (f y) (f x) + C * dist y x) / 2 := by
      nlinarith [dist_nonneg (x := y) (y := x)]
    have hd : dist y x < ((dist (f y) (f x) + C * dist y x) / 2) / C := by
      apply (lt_div_iff₀ hC).mpr
      nlinarith
    have hf := h _ hpos y hd
    nlinarith

/-- A positive pointwise Lipschitz constant implies continuity at that point. -/
theorem appendix2_pointwise_lipschitz_continuousAt {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {x : X}
    {C : ℝ} (hC : 0 < C) (hf : ∀ y, dist (f y) (f x) ≤ C * dist y x) :
    ContinuousAt f x := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  exact ⟨ε / C, div_pos hε hC, fun _ hy =>
    (appendix2_pointwise_lipschitz_rule f x hC).mp hf ε hε _ hy⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The arithmetic reference mean

Applying the abstract density result to the ordinary arithmetic mean proves
density of dyadic numerical ranks in the unit interval. This avoids assuming
any cardinal representation for the original preference-induced mean.
-/

namespace Kreps.PreferenceProperties

/-- The usual arithmetic mean, restricted to the closed unit interval. -/
noncomputable def UnitArithmeticMean : OrderedBisymmetricMean (Set.Icc (0 : ℝ) 1) where
  mean x y := ⟨(x.val + y.val) / 2, by
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]⟩
  reflexive x := by apply Subtype.ext; simp
  symmetric x y := by apply Subtype.ext; simp [add_comm]
  bisymmetric x y z w := by apply Subtype.ext; dsimp; ring
  strictMono_left y := by
    intro x z hxz
    change (x.val + y.val) / 2 < (z.val + y.val) / 2
    change x.val < z.val at hxz
    linarith
  strictMono_right x := by
    intro y z hyz
    change (x.val + y.val) / 2 < (x.val + z.val) / 2
    change y.val < z.val at hyz
    linarith

/-- The reference mean is jointly continuous. -/
theorem unitArithmeticMean_continuous : Continuous
    (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => UnitArithmeticMean.mean p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)).div_const 2 |>.subtype_mk _

/-- The reference grid realizes the usual dyadic fractions. -/
theorem unitArithmeticMean_grid (n k : ℕ) (hk : k ≤ 2 ^ n) :
    (MeanDyadicGrid UnitArithmeticMean.mean ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ n k).val =
      MeanDyadicRank n k := by
  induction n generalizing k with
  | zero =>
    norm_num at hk
    interval_cases k <;> simp [MeanDyadicGrid, MeanDyadicRank]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have h₀ : k / 2 ≤ 2 ^ n := by omega
    have h₁ : (k + 1) / 2 ≤ 2 ^ n := by omega
    change ((MeanDyadicGrid UnitArithmeticMean.mean _ _ n (k / 2)).val +
      (MeanDyadicGrid UnitArithmeticMean.mean _ _ n ((k + 1) / 2)).val) / 2 = _
    rw [ih _ h₀, ih _ h₁]
    unfold MeanDyadicRank
    have hsum : ((k / 2 : ℕ) : ℝ) + (((k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast (show k / 2 + (k + 1) / 2 = k by omega)
    rw [← add_div, hsum, pow_succ, div_mul_eq_div_div]

/-- The usual unit-interval dyadic points are dense. -/
theorem unitArithmeticMean_dense :
    Dense (MeanDyadicPoints UnitArithmeticMean ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) :=
  meanDyadicPoints_dense UnitArithmeticMean _ _ (fun x => x.property.1)
    (fun x => x.property.2) unitArithmeticMean_continuous

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Gluing interval coordinates in fixed cardinal units

If every chart transition is a translation, a global scale normalized on a seed chart uses
the same unit in every chart. This specialization preserves the common units obtained by
calibrating additive utility charts against fixed companion coordinates.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Constants attached to an open cover of a connected set agree when they agree on overlaps. -/
theorem open_cover_constants_eq {X ι Y : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hUS : ∀ i, U i ⊆ S) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (v : ι → Y) (he : ∀ i j, (U i ∩ U j).Nonempty → v i = v j)
    {seed : ι} (hne : (U seed).Nonempty) :
    ∀ i, (U i).Nonempty → v i = v seed := by
  classical
  choose c hc using fun x : S => hcover x x.property
  let f : S → Y := fun x => v (c x)
  have hlocal : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨Subtype.val ⁻¹' U (c x), (hU (c x)).preimage continuous_subtype_val, hc x, ?_⟩
    intro y hy
    exact he (c y) (c x) ⟨y, hc y, hy⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  obtain ⟨z, hz⟩ := hne
  intro i hi
  obtain ⟨x, hx⟩ := hi
  calc
    v i = f ⟨x, hUS i hx⟩ := he i (c ⟨x, hUS i hx⟩) ⟨x, hx, hc ⟨x, hUS i hx⟩⟩
    _ = f ⟨z, hUS seed hz⟩ := hlocal.apply_eq_of_preconnectedSpace _ _
    _ = v seed := he (c ⟨z, hUS seed hz⟩) seed ⟨z, hc ⟨z, hUS seed hz⟩, hz⟩

/-- Translation transitions force all affine chart slopes to equal the normalized seed slope. -/
theorem PositiveAffineIntervalAtlas.slopes_eq_one {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) {seed : ι}
    (hne : (a.domain seed).Nonempty)
    (ht : ∀ i j, ∃ B : ℝ, ∀ x ∈ a.domain i ∩ a.domain j,
      a.coord i x = a.coord j x + B)
    {f : ℝ → ℝ} (hseed : ∀ x ∈ a.domain seed, f x = a.coord seed x)
    {A B : ι → ℝ} (he : ∀ i x, x ∈ a.domain i → f x = A i * a.coord i x + B i) :
    ∀ i, (a.domain i).Nonempty → A i = 1 := by
  have hsame : ∀ i j, (a.domain i ∩ a.domain j).Nonempty → A i = A j := by
    intro i j hij
    obtain ⟨C, hC⟩ := ht i j
    have hcoeff := affine_coefficients_unique (a.increasing j)
      ((a.isOpen i).inter (a.isOpen j)) hij inter_subset_right
      (A := A i) (B := A i * C + B i) (C := A j) (D := B j) (fun x hx => by
        have hfi := he i x hx.1
        have hfj := he j x hx.2
        rw [hC x hx] at hfi
        nlinarith)
    exact hcoeff.1
  have hunit : A seed = 1 := by
    have hcoeff := affine_coefficients_unique (a.increasing seed) (a.isOpen seed)
      hne Subset.rfl (A := A seed) (B := B seed) (C := 1) (D := 0) (fun x hx => by
        have hfx := he seed x hx
        rw [hseed x hx] at hfx
        simpa only [one_mul, add_zero] using hfx.symm)
    exact hcoeff.1
  intro i hi
  exact (open_cover_constants_eq hS.isPreconnected a.domain a.isOpen a.subset a.cover
    A hsame hne i hi).trans hunit

/-- An atlas with translation transitions glues without changing any chart's cardinal unit. -/
theorem PositiveAffineIntervalAtlas.globalize_translations {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty)
    (ht : ∀ i j, ∃ B : ℝ, ∀ x ∈ a.domain i ∩ a.domain j,
      a.coord i x = a.coord j x + B) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ a.domain seed, f x = a.coord seed x) ∧
      ∀ i, ∃ B : ℝ, ∀ x ∈ a.domain i, f x = a.coord i x + B := by
  classical
  obtain ⟨f, hc, hm, hseed, hf⟩ := a.globalize hS seed hne
  choose A B _ he using hf
  have hA := a.slopes_eq_one hS hne ht hseed he
  refine ⟨f, hc, hm, hseed, fun i => ⟨B i, fun x hx => ?_⟩⟩
  simpa only [hA i ⟨x, hx⟩, one_mul] using he i x hx

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Utility representation on the nonnegative orthant

Kreps I, Proposition 1.15, pp. 14-15. Connectedness supplies an intermediate
strict preference, and a countable dense subset supplies the separator required
by Proposition 1.12. This uses the alternative topological argument invited on p. 15.
The conclusion asserts a utility representation, without claiming its continuity.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- In a connected domain, a continuous preference has no adjacent strict ranks. -/
theorem exists_strict_between [PreconnectedSpace X] (hr : Rational r)
    (hc : ContinuousPreference r) {x y : X} (hxy : Strict r x y) :
    ∃ z, Strict r x z ∧ Strict r z y := by
  have ho := continuousPreference_openStrictContours hc
  have hcover : Set.univ ⊆ StrictlyWorseThan r x ∪ StrictlyBetterThan r y := by
    intro z _
    by_cases hxz : Strict r x z
    · exact Or.inl hxz
    · right
      have hzx : r z x := by
        by_contra h
        exact hxz ((proposition_1_9a hr.1 x z).mpr h)
      exact weak_strict_trans hr.2 hzx hxy
  obtain ⟨z, _, hxz, hzy⟩ := isPreconnected_univ
    (StrictlyWorseThan r x) (StrictlyBetterThan r y) (ho x).2 (ho y).1 hcover
      ⟨y, Set.mem_univ y, hxy⟩ ⟨x, Set.mem_univ x, hxy⟩
  exact ⟨z, hxz, hzy⟩

/-- A dense subset separates all strict comparisons on a connected domain. -/
theorem dense_orderSeparating [PreconnectedSpace X] (hr : Rational r)
    (hc : ContinuousPreference r) {D : Set X} (hD : Dense D) : OrderSeparating r D := by
  intro x y hxy
  obtain ⟨z, hxz, hzy⟩ := exists_strict_between hr hc hxy
  have ho := continuousPreference_openStrictContours hc
  obtain ⟨d, hd, hxd, hdy⟩ := hD.exists_mem_open ((ho x).2.inter (ho y).1) ⟨z, hxz, hzy⟩
  exact ⟨d, hd, hxd.1, hdy⟩

/-- General form of the countable-dense-set argument for Proposition 1.15. -/
theorem represents_of_continuous_connected [PreconnectedSpace X]
    [TopologicalSpace.SeparableSpace X] (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : X → ℝ, Represents u r := by
  obtain ⟨D, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense X
  exact represents_of_countable_separating hr hcount (dense_orderSeparating hr hc hdense)

/-- The book's commodity domain, with its relative finite-dimensional topology. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- **Proposition 1.15**, pp. 14-15, for every finite number of commodities. -/
theorem proposition_1_15 (k : ℕ) {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  exact represents_of_continuous_connected hr hc

/-- Proposition 1.15 with the common-radius continuity hypothesis from Definition 1.13. -/
theorem proposition_1_15_metric (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : MetricContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r :=
  proposition_1_15 k hr (continuousPreference_iff_metric.mpr hc)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice from compact menus

Kreps I, Proposition 1.19, p. 17, and the direct-proof part of Problem 1.13, pp. 26-27.
Finite preference maxima give the finite intersection property for closed upper contours.
Compactness then yields a greatest element without assuming continuous utility exists.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X]

/-- A rational preference with closed contours attains a greatest element on each compact menu. -/
theorem compact_prefChoice_nonempty {r : X → X → Prop} (hr : Rational r)
    (hc : ClosedContours r) {A : Set X} (hcompact : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hfinite (u : Finset A) : (A ∩ ⋂ i ∈ u, NoWorseThan r i.val).Nonempty := by
    let S : Set X := insert a (Subtype.val '' (u : Set A))
    have hsfin : S.Finite := (u.finite_toSet.image Subtype.val).insert a
    have hsne : S.Nonempty := ⟨a, Set.mem_insert a _⟩
    obtain ⟨x, hx, hmax⟩ := prefChoice_finiteNonempty hr S hsfin hsne
    refine ⟨x, ?_, ?_⟩
    · rcases hx with hxa | ⟨i, _, rfl⟩
      · exact hxa ▸ ha
      · exact i.property
    · simp only [Set.mem_iInter]
      intro i hi
      exact hmax i.val (Or.inr ⟨i, hi, rfl⟩)
  obtain ⟨x, hx, hmax⟩ := hcompact.inter_iInter_nonempty
    (fun i : A => NoWorseThan r i.val) (fun i => (hc i.val).2) hfinite
  refine ⟨x, hx, fun y hy => ?_⟩
  exact Set.mem_iInter.mp hmax ⟨y, hy⟩

/-- **Proposition 1.19**, p. 17, generalized from the orthant to every topological space. -/
theorem proposition_1_19 {c : ChoiceRule X} (hf : Feasible c)
    (hn : FiniteNonempty c) (hco : Coherent c) (ha : Assumption116 c)
    (hc : ContinuousPreference (Revealed c)) {A : Set X}
    (hcompact : IsCompact A) (hne : A.Nonempty) : (c A).Nonempty := by
  have hr : Rational (Revealed c) := ⟨revealed_complete hf hn, revealed_transitive hf hn hco⟩
  rw [(proposition_1_17 hf hn hco).mpr ha]
  exact compact_prefChoice_nonempty hr ((proposition_1_14c hr).mp hc) hcompact hne

/-- The direct compactness proof requested in **Problem 1.13**, without Debreu's theorem. -/
theorem problem_1_13_direct {r : X → X → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) {A : Set X} (hcompact : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty :=
  compact_prefChoice_nonempty hr ((proposition_1_14c hr).mp hc) hcompact hne

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Utility transformation counterexamples

Kreps I, Problem 1.14c-d, p. 27. The jump at one prevents a globally strictly
increasing transformation. A bounded utility representing an unbounded one forces
an infinite value in any monotone extension to the entire real line.
-/

namespace Kreps.PreferenceProperties

/-- The piecewise utility in **Problem 1.14c**, including its stated value at one. -/
noncomputable def JumpUtility (x : ℝ) : ℝ := if x ≤ 1 then x else x + 1

/-- The jump preserves the usual strict order. -/
theorem jumpUtility_strictMono : StrictMono JumpUtility := by
  intro x y hxy
  unfold JumpUtility
  split_ifs <;> linarith

/-- On the nonnegative half-line, the jump utility represents the same preference as identity. -/
theorem jumpUtility_represents :
    Represents (fun x : Set.Ici (0 : ℝ) => JumpUtility x.val)
      (UtilityPref (fun x : Set.Ici (0 : ℝ) => x.val)) := by
  intro x y
  exact jumpUtility_strictMono.le_iff_le.symm

/-- **Problem 1.14c**: no everywhere strictly increasing transformation can undo the jump. -/
theorem problem_1_14c :
    ¬∃ f : ℝ → ℝ, StrictMono f ∧
      ∀ x : Set.Ici (0 : ℝ), x.val = f (JumpUtility x.val) := by
  rintro ⟨f, hf, heq⟩
  have h1 : f 1 = 1 := by
    simpa [JumpUtility] using (heq ⟨1, by norm_num⟩).symm
  have h2 : 1 < f 2 := by
    rw [← h1]
    exact hf (by norm_num)
  let t : ℝ := (1 + f 2) / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have hft : f (t + 1) = t := by
    simpa [JumpUtility, not_le.mpr ht] using
      (heq ⟨t, by change 0 ≤ t; linarith⟩).symm
  have hcontra : f 2 < t := by
    rw [← hft]
    exact hf (by linarith)
  dsimp [t] at hcontra
  linarith

/-- A bounded representation of the usual order on the nonnegative half-line. -/
noncomputable def FractionUtility (x : Set.Ici (0 : ℝ)) : ℝ := x.val / (x.val + 1)

/-- All values lie below the finite endpoint one. -/
theorem fractionUtility_lt_one (x : Set.Ici (0 : ℝ)) : FractionUtility x < 1 := by
  have hx : 0 ≤ x.val := x.property
  change x.val / (x.val + 1) < 1
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- The bounded utility has no negative values. -/
theorem fractionUtility_nonneg (x : Set.Ici (0 : ℝ)) : 0 ≤ FractionUtility x := by
  exact div_nonneg x.property (by have hx : 0 ≤ x.val := x.property; linarith)

/-- Bounded and unbounded utilities represent exactly the same relation. -/
theorem fractionUtility_represents :
    Represents FractionUtility (UtilityPref (fun x : Set.Ici (0 : ℝ) => x.val)) := by
  intro x y
  have hx : 0 ≤ x.val := x.property
  have hy : 0 ≤ y.val := y.property
  change y.val ≤ x.val ↔ y.val / (y.val + 1) ≤ x.val / (x.val + 1)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- The monotone extension really can require positive infinity at a finite argument. -/
theorem problem_1_14d_top :
    ExtendedUtilityTransform FractionUtility (fun x : Set.Ici (0 : ℝ) => x.val) 1 = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro y
  let x : Set.Ici (0 : ℝ) := ⟨max (y + 1) 0, le_max_right (y + 1) (0 : ℝ)⟩
  have hyx : y < x.val := by
    dsimp [x]
    have hm := le_max_left (y + 1) 0
    linarith
  exact (EReal.coe_lt_coe hyx).trans_le
    (le_sSup (show (x.val : EReal) ∈ {a : EReal | ∃ z : Set.Ici (0 : ℝ),
      FractionUtility z ≤ 1 ∧ a = (z.val : EReal)} from
        ⟨x, (fractionUtility_lt_one x).le, rfl⟩))

/-- Empty lower sections produce negative infinity in the book's supremum formula. -/
theorem problem_1_14d_bot :
    ExtendedUtilityTransform FractionUtility (fun x : Set.Ici (0 : ℝ) => x.val) (-1) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro a ⟨x, hx, _⟩
    have hnonneg := fractionUtility_nonneg x
    linarith
  · exact bot_le

/-- The positive-infinity example cannot be replaced by a real-valued monotone extension. -/
theorem problem_1_14d_no_real_extension :
    ¬∃ f : ℝ → ℝ, Monotone f ∧ ∀ x : Set.Ici (0 : ℝ), f (FractionUtility x) = x.val := by
  rintro ⟨f, hf, heq⟩
  let x : Set.Ici (0 : ℝ) := ⟨max (f 1 + 1) 0, le_max_right (f 1 + 1) (0 : ℝ)⟩
  have hle := hf (fractionUtility_lt_one x).le
  rw [heq x] at hle
  have hm := le_max_left (f 1 + 1) 0
  dsimp [x] at hle
  linarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite chains of coordinate substitutions

The substitution argument in Kreps I, Proposition 2.12, p. 41. Weak improvements
in finitely many coordinates give a weak improvement overall; one strict step
makes the full chain strict. Equal coordinate scores leave the value unchanged.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Finite I] [DecidableEq I] {B : I → Type*}

/-- Coordinatewise weak score improvements can be substituted one at a time. -/
theorem finite_coordinate_mono {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, w i a ≤ w i b →
      F (Function.update z i a) ≤ F (Function.update z i b))
    (x y : ∀ i, B i) (hxy : ∀ i, w i (x i) ≤ w i (y i)) : F x ≤ F y := by
  let : Fintype I := Fintype.ofFinite I
  have hchain (s : Finset I) : F x ≤ F (s.piecewise y x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.piecewise_insert]
      apply ih.trans
      have hz : s.piecewise y x i = x i := s.piecewise_eq_of_notMem y x hi
      have hstep := hc i (s.piecewise y x) (s.piecewise y x i) (y i)
        (by rw [hz]; exact hxy i)
      simpa only [Function.update_eq_self] using hstep
  simpa only [Finset.piecewise_univ] using hchain Finset.univ

/-- Equal scores allow substitution in both directions. -/
theorem finite_coordinate_eq {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, w i a ≤ w i b →
      F (Function.update z i a) ≤ F (Function.update z i b))
    (x y : ∀ i, B i) (hxy : ∀ i, w i (x i) = w i (y i)) : F x = F y :=
  le_antisymm (finite_coordinate_mono hc x y (fun i => (hxy i).le))
    (finite_coordinate_mono hc y x (fun i => (hxy i).ge))

/-- One strict score improvement makes a finite weak-improvement chain strict. -/
theorem finite_coordinate_strict {F : (∀ i, B i) → ℝ} {w : ∀ i, B i → ℝ}
    (hc : ∀ i z a b, F (Function.update z i a) ≤ F (Function.update z i b) ↔
      w i a ≤ w i b) (x y : ∀ i, B i)
    (hxy : ∀ i, w i (x i) ≤ w i (y i)) (hs : ∃ i, w i (x i) < w i (y i)) :
    F x < F y := by
  obtain ⟨i, hi⟩ := hs
  have hstep : F x < F (Function.update x i (y i)) := by
    have hn : ¬F (Function.update x i (y i)) ≤ F (Function.update x i (x i)) :=
      fun h => (not_le_of_gt hi) ((hc i x (y i) (x i)).mp h)
    simpa only [Function.update_eq_self] using lt_of_not_ge hn
  apply hstep.trans_le
  apply finite_coordinate_mono (fun i z a b h => (hc i z a b).mpr h)
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using hxy j

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Recursive utility values on an enumerated domain

Kreps I, Problem 2.14(d), p. 49. Start at zero and apply the preceding insertion
rule successively. Old assignments never change. The resulting sequence preserves
every comparison of the original numerical ranks, including ties and repeated
points in the enumeration. Thus the construction gives a representation on the
enumerated subset rather than merely on its finite prefixes.
-/

namespace Kreps.PreferenceProperties

/-- The first `n + 1` assigned values after `n` successive insertions. -/
noncomputable def RecursiveRankStage (v : ℕ → ℝ) : (n : ℕ) → Fin (n + 1) → ℝ
  | 0 => fun _ => 0
  | n + 1 => Fin.lastCases
      (InsertedRank (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) (v (n + 1)))
      (RecursiveRankStage v n)

/-- A new stage retains each previously assigned value. -/
theorem recursiveRankStage_castSucc (v : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    RecursiveRankStage v (n + 1) i.castSucc = RecursiveRankStage v n i := by
  simp only [RecursiveRankStage, Fin.lastCases_castSucc]

/-- The newly appended value is computed by the book's insertion rule. -/
theorem recursiveRankStage_last (v : ℕ → ℝ) (n : ℕ) :
    RecursiveRankStage v (n + 1) (Fin.last (n + 1)) =
      InsertedRank (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) (v (n + 1)) := by
  simp only [RecursiveRankStage, Fin.lastCases_last]

/-- Every finite stage preserves all original rank comparisons. -/
theorem recursiveRankStage_preserving (v : ℕ → ℝ) (n : ℕ) :
    RankPreserving (fun i : Fin (n + 1) => v i) (RecursiveRankStage v n) := by
  induction n with
  | zero =>
      intro i j
      fin_cases i
      fin_cases j
      simp [RecursiveRankStage]
  | succ n ih =>
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · simpa only [Fin.val_last, Fin.val_castSucc, recursiveRankStage_last,
            recursiveRankStage_castSucc] using
            (insertedRank_compare ih (v (n + 1)) j).2
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.val_last, Fin.val_castSucc, recursiveRankStage_last,
            recursiveRankStage_castSucc] using
            (insertedRank_compare ih (v (n + 1)) i).1
        · simpa only [Fin.val_castSucc, recursiveRankStage_castSucc] using ih i j

/-- The value permanently assigned to the `n`th enumerated point. -/
noncomputable def RecursiveRank (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  RecursiveRankStage v n (Fin.last n)

/-- The arbitrary initial normalization is zero. -/
theorem recursiveRank_zero (v : ℕ → ℝ) : RecursiveRank v 0 = 0 := rfl

/-- Each finite stage consists of the already permanent assigned values. -/
theorem recursiveRankStage_eq_rank (v : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    RecursiveRankStage v n i = RecursiveRank v i := by
  induction n with
  | zero =>
      fin_cases i
      rfl
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rfl
      · rw [recursiveRankStage_castSucc]
        exact ih i

/-- The permanent sequence satisfies the four-case recursion on its previous values. -/
theorem recursiveRank_succ (v : ℕ → ℝ) (n : ℕ) :
    RecursiveRank v (n + 1) =
      InsertedRank (fun i : Fin (n + 1) => v i)
        (fun i => RecursiveRank v i) (v (n + 1)) := by
  change RecursiveRankStage v (n + 1) (Fin.last (n + 1)) = _
  rw [recursiveRankStage_last]
  congr 1
  funext i
  exact recursiveRankStage_eq_rank v n i

/-- All comparisons are preserved in the infinite enumerated sequence. -/
theorem recursiveRank_preserving (v : ℕ → ℝ) : RankPreserving v (RecursiveRank v) := by
  intro i j
  let n := max i j
  let i' : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le (le_max_left i j)⟩
  let j' : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le (le_max_right i j)⟩
  have h := recursiveRankStage_preserving v n i' j'
  simpa only [recursiveRankStage_eq_rank] using h

/-- Equal original ranks receive equal assigned values, even at different enumeration indices. -/
theorem recursiveRank_eq_iff (v : ℕ → ℝ) (i j : ℕ) :
    RecursiveRank v i = RecursiveRank v j ↔ v i = v j := by
  simp only [le_antisymm_iff, ← recursiveRank_preserving v i j,
    ← recursiveRank_preserving v j i]

/-- Strict original comparisons are preserved. -/
theorem recursiveRank_lt_iff (v : ℕ → ℝ) (i j : ℕ) :
    RecursiveRank v i < RecursiveRank v j ↔ v i < v j :=
  (rankPreserving_lt (recursiveRank_preserving v) i j).symm

/-- **Problem 2.14(d):** the recursively assigned sequence represents the sampled preference. -/
theorem problem_2_14d_sequence {X : Type*} {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) (q : ℕ → X) :
    Represents (RecursiveRank (v ∘ q)) (fun i j => r (q i) (q j)) := by
  intro i j
  exact (hv (q i) (q j)).trans (recursiveRank_preserving (v ∘ q) j i)

/-- A sampled preference needs only rationality for the recursive representation to exist. -/
theorem problem_2_14d_exists {X : Type*} {r : X → X → Prop}
    (hr : Rational r) (q : ℕ → X) :
    ∃ v : ℕ → ℝ, Represents (RecursiveRank v) (fun i j => r (q i) (q j)) := by
  have hs : Rational (fun i j => r (q i) (q j)) :=
    ⟨fun i j => hr.1 (q i) (q j), fun i j k => hr.2 (q i) (q j) (q k)⟩
  obtain ⟨v, hv⟩ := proposition_1_11 hs
  refine ⟨v, ?_⟩
  intro i j
  exact (hv i j).trans (recursiveRank_preserving v j i)

/-- Copy the permanent value of any enumeration index of a point in the sampled range. -/
noncomputable def RecursiveRangeUtility {X : Type*} (q : ℕ → X) (v : X → ℝ)
    (x : Set.range q) : ℝ := RecursiveRank (v ∘ q) x.property.choose

/-- Choosing an enumeration index does not affect the assigned value. -/
theorem recursiveRangeUtility_apply {X : Type*} (q : ℕ → X) (v : X → ℝ) (n : ℕ) :
    RecursiveRangeUtility q v ⟨q n, Set.mem_range_self n⟩ = RecursiveRank (v ∘ q) n := by
  apply (recursiveRank_eq_iff (v ∘ q) _ n).mpr
  change v (q _) = v (q n)
  exact congrArg v (Set.mem_range_self n).choose_spec

/-- **Problem 2.14(d):** a well-defined representation on the enumerated subset itself. -/
theorem problem_2_14d {X : Type*} {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) (q : ℕ → X) :
    Represents (RecursiveRangeUtility q v) (fun x y => r x.val y.val) := by
  intro x y
  have hx := x.property.choose_spec
  have hy := y.property.choose_spec
  have h := problem_2_14d_sequence hv q x.property.choose y.property.choose
  simpa only [hx, hy, RecursiveRangeUtility] using h

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: limsup and liminf

Definition A2.22 and Proposition A2.23, pp. 450–451. Suprema, infima and
accumulation points are taken in the extended real line so that every sequence
is covered. The finite-limit theorem separately identifies ordinary real convergence.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The extended supremum of a sequence tail in Definition A2.22. -/
noncomputable def SequenceTailSup (u : ℕ → ℝ) (N : ℕ) : EReal :=
  ⨆ n ≥ N, (u n : EReal)

/-- The extended infimum of a sequence tail in Definition A2.22. -/
noncomputable def SequenceTailInf (u : ℕ → ℝ) (N : ℕ) : EReal :=
  ⨅ n ≥ N, (u n : EReal)

/-- Tail suprema are nonincreasing, including infinite values. -/
theorem sequenceTailSup_antitone (u : ℕ → ℝ) : Antitone (SequenceTailSup u) := by
  intro M N hMN
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact le_iSup_of_le n (le_iSup_of_le (hMN.trans hn) le_rfl)

/-- Tail infima are nondecreasing. -/
theorem sequenceTailInf_monotone (u : ℕ → ℝ) : Monotone (SequenceTailInf u) := by
  intro M N hMN
  apply le_iInf
  intro n
  apply le_iInf
  intro hn
  exact iInf_le_of_le n (iInf_le_of_le (hMN.trans hn) le_rfl)

/-- **Definition A2.22:** limsup is the infimum of the tail suprema. -/
theorem definition_A2_22_limsup (u : ℕ → ℝ) :
    Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⨅ N, SequenceTailSup u N :=
  Filter.limsup_eq_iInf_iSup_of_nat

/-- **Definition A2.22:** liminf is the supremum of the tail infima. -/
theorem definition_A2_22_liminf (u : ℕ → ℝ) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⨆ N, SequenceTailInf u N :=
  Filter.liminf_eq_iSup_iInf_of_nat

/-- The tail suprema actually converge to the limsup, as in the book's definition. -/
theorem sequenceTailSup_tendsto (u : ℕ → ℝ) :
    Filter.Tendsto (SequenceTailSup u) Filter.atTop
      (𝓝 (Filter.limsup (fun n => (u n : EReal)) Filter.atTop)) := by
  rw [definition_A2_22_limsup]
  exact tendsto_atTop_iInf (sequenceTailSup_antitone u)

/-- The tail infima converge to the liminf. -/
theorem sequenceTailInf_tendsto (u : ℕ → ℝ) :
    Filter.Tendsto (SequenceTailInf u) Filter.atTop
      (𝓝 (Filter.liminf (fun n => (u n : EReal)) Filter.atTop)) := by
  rw [definition_A2_22_liminf]
  exact tendsto_atTop_iSup (sequenceTailInf_monotone u)

/-- The limsup is the greatest extended-real accumulation point. -/
theorem appendix2_limsup_greatest_accumulation (u : ℕ → ℝ) :
    IsGreatest {x : EReal | MapClusterPt x Filter.atTop (fun n => (u n : EReal))}
      (Filter.limsup (fun n => (u n : EReal)) Filter.atTop) :=
  isGreatest_mapClusterPt_limsup

/-- The liminf is the least extended-real accumulation point. -/
theorem appendix2_liminf_least_accumulation (u : ℕ → ℝ) :
    IsLeast {x : EReal | MapClusterPt x Filter.atTop (fun n => (u n : EReal))}
      (Filter.liminf (fun n => (u n : EReal)) Filter.atTop) :=
  isLeast_mapClusterPt_liminf

/-- **Proposition A2.23:** equality of extended liminf and limsup characterizes convergence. -/
theorem proposition_A2_23 (u : ℕ → ℝ) :
    (∃ x : EReal, Filter.Tendsto (fun n => (u n : EReal)) Filter.atTop (𝓝 x)) ↔
      Filter.liminf (fun n => (u n : EReal)) Filter.atTop =
        Filter.limsup (fun n => (u n : EReal)) Filter.atTop := by
  constructor
  · rintro ⟨x, hx⟩
    exact hx.liminf_eq.trans hx.limsup_eq.symm
  · intro h
    exact ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm⟩

/-- Ordinary real convergence requires the common extended limit to be finite. -/
theorem appendix2_finite_limit (u : ℕ → ℝ) (x : ℝ) :
    Filter.Tendsto u Filter.atTop (𝓝 x) ↔
      Filter.liminf (fun n => (u n : EReal)) Filter.atTop = (x : EReal) ∧
        Filter.limsup (fun n => (u n : EReal)) Filter.atTop = (x : EReal) := by
  constructor
  · intro h
    have he := EReal.tendsto_coe.mpr h
    exact ⟨he.liminf_eq, he.limsup_eq⟩
  · rintro ⟨hi, hs⟩
    exact EReal.tendsto_coe.mp (tendsto_of_liminf_eq_limsup hi hs)

/-- Divergence to positive infinity gives infinite liminf and limsup. -/
theorem appendix2_positive_infinite_limit {u : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop Filter.atTop) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊤ ∧
      Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊤ := by
  have he := EReal.tendsto_coe_nhds_top_iff.mpr hu
  exact ⟨he.liminf_eq, he.limsup_eq⟩

/-- Divergence to negative infinity gives the negative-infinite caveat in the text. -/
theorem appendix2_negative_infinite_limit {u : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop Filter.atBot) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊥ ∧
      Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊥ := by
  have he := EReal.tendsto_coe_nhds_bot_iff.mpr hu
  exact ⟨he.liminf_eq, he.limsup_eq⟩

/-- Removing a finite prefix cannot bound an unbounded-above real sequence. -/
theorem sequenceTailSup_unbounded {u : ℕ → ℝ} (hu : ¬BddAbove (Set.range u)) (N : ℕ) :
    SequenceTailSup u N = ⊤ := by
  have ht : ¬BddAbove (u '' Set.Ici N) := by
    rintro ⟨M, hM⟩
    apply hu
    apply Filter.IsBoundedUnder.bddAbove_range
    exact Filter.isBoundedUnder_of_eventually_le (a := M)
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => hM ⟨n, hn, rfl⟩⟩)
  simpa only [Set.image_image, Function.comp_def, sSup_image, Set.mem_Ici,
    SequenceTailSup] using appendix2_extended_sup_unbounded ht

/-- An unbounded-above sequence has positive-infinite limsup even if it does not diverge. -/
theorem appendix2_limsup_unbounded {u : ℕ → ℝ} (hu : ¬BddAbove (Set.range u)) :
    Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊤ := by
  rw [definition_A2_22_limsup]
  simp only [sequenceTailSup_unbounded hu, iInf_const]

/-- The lower-tail version of the same finite-prefix observation. -/
theorem sequenceTailInf_unbounded {u : ℕ → ℝ} (hu : ¬BddBelow (Set.range u)) (N : ℕ) :
    SequenceTailInf u N = ⊥ := by
  have ht : ¬BddBelow (u '' Set.Ici N) := by
    rintro ⟨M, hM⟩
    apply hu
    apply Filter.IsBoundedUnder.bddBelow_range
    exact Filter.isBoundedUnder_of_eventually_ge (a := M)
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => hM ⟨n, hn, rfl⟩⟩)
  simpa only [Set.image_image, Function.comp_def, sInf_image, Set.mem_Ici,
    SequenceTailInf] using appendix2_extended_inf_unbounded ht

/-- An unbounded-below sequence has negative-infinite liminf. -/
theorem appendix2_liminf_unbounded {u : ℕ → ℝ} (hu : ¬BddBelow (Set.range u)) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊥ := by
  rw [definition_A2_22_liminf]
  simp only [sequenceTailInf_unbounded hu, iSup_const]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuous cardinal scales for strict bisymmetric means

The lower-cut scale is continuous because its range contains all dyadic ranks.
Density of the original mean grid makes the scale strict, and continuity
extends the grid midpoint identity to every pair of points.
-/

namespace Kreps.PreferenceProperties

variable {α : Type*} [LinearOrder α]

/-- The completed scale with its unit-interval codomain made explicit. -/
noncomputable def MeanUnitScale (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) (x : α) : Set.Icc (0 : ℝ) 1 :=
  ⟨MeanCardinalScale M a b x, meanCardinalScale_mem M a b x (ha x)⟩

/-- The completed scale has dense range, since it attains every dyadic rank. -/
theorem meanUnitScale_denseRange (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) : DenseRange (MeanUnitScale M a b ha) := by
  apply unitArithmeticMean_dense.mono
  rintro q ⟨n, k, hk, rfl⟩
  refine ⟨MeanDyadicGrid M.mean a b n k, ?_⟩
  apply Subtype.ext
  exact (meanCardinalScale_grid M hab ha n k hk).trans
    (unitArithmeticMean_grid n k hk).symm

/-- Monotonicity and dense numerical range make the completed scale continuous. -/
theorem meanCardinalScale_continuous [TopologicalSpace α] [OrderTopology α]
    (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) (ha : ∀ x, a ≤ x) :
    Continuous (MeanCardinalScale M a b) := by
  have hm : Monotone (MeanUnitScale M a b ha) := meanCardinalScale_mono M a b ha
  exact continuous_subtype_val.comp
    (hm.continuous_of_denseRange (meanUnitScale_denseRange M hab ha))

/-- The completed scale preserves means of arbitrary dyadic grid points. -/
theorem meanCardinalScale_grid_mean (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (n m i j : ℕ)
    (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ m) :
    MeanCardinalScale M a b
      (M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b m j)) =
      (MeanCardinalScale M a b (MeanDyadicGrid M.mean a b n i) +
        MeanCardinalScale M a b (MeanDyadicGrid M.mean a b m j)) / 2 := by
  have hi' : i * 2 ^ m ≤ 2 ^ (n + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + m) := by
    rw [Nat.add_comm n m, pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hsum : i * 2 ^ m + j * 2 ^ n ≤ 2 ^ (n + m + 1) := by
    rw [pow_succ]
    omega
  have hleft := meanDyadicGrid_refine M a b n m i
  have hright := meanDyadicGrid_refine M a b m n j
  rw [Nat.add_comm m n] at hright
  have hmean : M.mean (MeanDyadicGrid M.mean a b n i) (MeanDyadicGrid M.mean a b m j) =
      MeanDyadicGrid M.mean a b (n + m + 1) (i * 2 ^ m + j * 2 ^ n) := by
    rw [← hleft, ← hright]
    exact meanDyadicGrid_midpoint M a b (n + m) _ _ hi' hj'
  rw [hmean, meanCardinalScale_grid M hab ha _ _ hsum,
    meanCardinalScale_grid M hab ha _ _ hi, meanCardinalScale_grid M hab ha _ _ hj]
  simp only [MeanDyadicRank, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_succ, pow_add]
  field_simp

/-- Continuity extends the midpoint identity from the dense grid to all points. -/
theorem meanCardinalScale_mean [TopologicalSpace α] [OrderTopology α]
    (M : OrderedBisymmetricMean α) {a b : α} (hab : a < b) (ha : ∀ x, a ≤ x)
    (hd : Dense (MeanDyadicPoints M a b))
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) (x y : α) :
    MeanCardinalScale M a b (M.mean x y) =
      (MeanCardinalScale M a b x + MeanCardinalScale M a b y) / 2 := by
  have hs := meanCardinalScale_continuous M hab ha
  have hclosed : IsClosed {p : α × α | MeanCardinalScale M a b (M.mean p.1 p.2) =
      (MeanCardinalScale M a b p.1 + MeanCardinalScale M a b p.2) / 2} :=
    isClosed_eq (hs.comp hc) ((hs.comp continuous_fst).add
      (hs.comp continuous_snd) |>.div_const 2)
  have hsub : MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b ⊆
      {p : α × α | MeanCardinalScale M a b (M.mean p.1 p.2) =
        (MeanCardinalScale M a b p.1 + MeanCardinalScale M a b p.2) / 2} := by
    rintro ⟨u, v⟩ ⟨⟨n, i, hi, rfl⟩, ⟨m, j, hj, rfl⟩⟩
    exact meanCardinalScale_grid_mean M hab ha n m i j hi hj
  have hxy : (x, y) ∈ closure (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) := by
    rw [closure_prod_eq]
    exact ⟨hd x, hd y⟩
  exact closure_minimal hsub hclosed hxy

/-- A compact interval's continuous strict bisymmetric mean admits a continuous cardinal scale. -/
theorem exists_continuous_bisymmetricMean_scale [TopologicalSpace α] [OrderTopology α]
    [CompactSpace α] [DenselyOrdered α] (M : OrderedBisymmetricMean α) {a b : α}
    (hab : a < b) (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) :
    ∃ φ : α → ℝ, Continuous φ ∧ StrictMono φ ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ x y, φ (M.mean x y) = (φ x + φ y) / 2 := by
  have hd := meanDyadicPoints_dense M a b ha hb hc
  refine ⟨MeanCardinalScale M a b, meanCardinalScale_continuous M hab ha,
    meanCardinalScale_strictMono M hab ha hd, ?_, ?_, meanCardinalScale_mean M hab ha hd hc⟩
  · simpa only [meanDyadicGrid_left, MeanDyadicRank, Nat.cast_zero, zero_div] using
      meanCardinalScale_grid M hab ha 0 0 (by norm_num)
  · simpa [MeanDyadicGrid, MeanDyadicRank] using
      meanCardinalScale_grid M hab ha 0 1 (by norm_num)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local midpoint identities and affine uniqueness

Supporting the overlap argument for Proposition 2.14. A continuous function
on an interval satisfying the midpoint identity for all sufficiently small
steps is affine. The proof uses a compact maximum argument, including the
endpoints, rather than assuming differentiability of utility.
-/

namespace Kreps.PreferenceProperties

/-- A local midpoint identity propagates nonpositive endpoint bounds over a compact interval. -/
theorem local_midpoint_nonpos {f : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b)) (ha : f a ≤ 0) (hb : f b ≤ 0) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∀ x ∈ Set.Icc a b, f x ≤ 0 := by
  let : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  let F : Set.Icc a b → ℝ := fun x => f x.val
  have hF : Continuous F := continuousOn_iff_continuous_domRestrict.mp hc
  obtain ⟨m, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuousOn
  have hK : IsCompact {x : Set.Icc a b | F x = F m} :=
    (isClosed_eq hF continuous_const).isCompact
  obtain ⟨z, hz⟩ := hK.exists_isLeast ⟨m, rfl⟩
  have hzM : f z.val = f m.val := hz.1
  have hM : f m.val ≤ 0 := by
    by_contra h
    have hpos : 0 < f z.val := by linarith
    have hza : a < z.val := lt_of_le_of_ne z.property.1 (by
      intro he; have : f z.val = f a := congrArg f he.symm; linarith)
    have hzb : z.val < b := lt_of_le_of_ne z.property.2 (by
      intro he; have : f z.val = f b := congrArg f he; linarith)
    let d := min δ (min (z.val - a) (b - z.val))
    have hd : 0 < d := lt_min hδ (lt_min (sub_pos.mpr hza) (sub_pos.mpr hzb))
    have hdδ : d ≤ δ := min_le_left _ _
    have hda : d ≤ z.val - a := (min_le_right _ _).trans (min_le_left _ _)
    have hdb : d ≤ b - z.val := (min_le_right _ _).trans (min_le_right _ _)
    let u : Set.Icc a b := ⟨z.val - d / 2, by constructor <;> linarith⟩
    let v : Set.Icc a b := ⟨z.val + d / 2, by constructor <;> linarith⟩
    have hu : f u.val ≤ f m.val := hmax (Set.mem_univ u)
    have hv : f v.val ≤ f m.val := hmax (Set.mem_univ v)
    have hmid := hm z.val (d / 2) (by linarith) (by linarith) u.property.1 v.property.2
    have he : F u = F m := by dsimp [F, u, v] at *; linarith
    have hzle : z ≤ u := hz.2 he
    change z.val ≤ z.val - d / 2 at hzle
    linarith
  intro x hx
  exact (hmax (Set.mem_univ (⟨x, hx⟩ : Set.Icc a b))).trans hM

/-- A uniform local midpoint identity makes a continuous function affine on a compact interval. -/
theorem local_midpoint_affine_Icc {f : ℝ → ℝ} {a b δ : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∃ A B : ℝ, ∀ x ∈ Set.Icc a b, f x = A * x + B := by
  let A := (f b - f a) / (b - a)
  let g := fun x => f x - (A * (x - a) + f a)
  have hga : g a = 0 := by dsimp [g]; ring
  have hgb : g b = 0 := by
    dsimp [g, A]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hcg : ContinuousOn g (Set.Icc a b) := hc.sub
    (((continuous_const.mul (continuous_id.sub continuous_const)).add
      continuous_const).continuousOn)
  have hgm : ∀ x h, 0 < h → h < δ → a ≤ x - h → x + h ≤ b →
      g x = (g (x - h) + g (x + h)) / 2 := by
    intro x h hh hhδ hxa hxb
    have := hm x h hh hhδ hxa hxb
    dsimp [g]
    linarith
  have hle := local_midpoint_nonpos hab.le hcg hga.le hgb.le hδ hgm
  have hge := local_midpoint_nonpos hab.le hcg.neg (by simp [hga]) (by simp [hgb]) hδ
    (fun x h hh hhδ hxa hxb => by
      have := hgm x h hh hhδ hxa hxb
      dsimp
      linarith)
  refine ⟨A, f a - A * a, fun x hx => ?_⟩
  have h₁ := hle x hx
  have h₂ := hge x hx
  dsimp [g] at h₁ h₂
  linarith

/-- Local midpoint identities with a common positive radius give one affine scale on an interval. -/
theorem local_midpoint_affine_interval {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S) {a b δ : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) (hδ : 0 < δ)
    (hm : ∀ x h, 0 < h → h < δ → x - h ∈ S → x + h ∈ S →
      f x = (f (x - h) + f (x + h)) / 2) :
    ∃ A B : ℝ, ∀ x ∈ S, f x = A * x + B := by
  refine ⟨(f b - f a) / (b - a), f a - (f b - f a) / (b - a) * a, ?_⟩
  intro x hx
  have hL : min a x ∈ S := by
    by_cases h : a ≤ x
    · simpa only [min_eq_left h] using ha
    · simpa only [min_eq_right (le_of_not_ge h)] using hx
  have hR : max b x ∈ S := by
    by_cases h : b ≤ x
    · simpa only [max_eq_right h] using hx
    · simpa only [max_eq_left (le_of_not_ge h)] using hb
  have hLR : min a x < max b x := (min_le_left _ _).trans_lt
    (hab.trans_le (le_max_left _ _))
  have hsub : Set.Icc (min a x) (max b x) ⊆ S := hS.out hL hR
  obtain ⟨A, B, h⟩ := local_midpoint_affine_Icc hLR (hc.mono hsub) hδ
    (fun y t ht htδ hlo hhi => hm y t ht htδ
      (hsub ⟨hlo, by linarith⟩) (hsub ⟨by linarith, hhi⟩))
  have hfa := h a ⟨min_le_left _ _, hab.le.trans (le_max_left _ _)⟩
  have hfb := h b ⟨(min_le_left _ _).trans hab.le, le_max_left _ _⟩
  have hfx := h x ⟨min_le_right _ _, le_max_right _ _⟩
  have hA : A = (f b - f a) / (b - a) :=
    (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr (by linarith)
  rw [← hA]
  linarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Globalizing aligned local additive representations

Supporting Proposition 2.14. Straight paths inside products of real intervals
make their total score monotone between ordered endpoints. Consequently local
representation by one aligned sum is a global representation. Constructing
and aligning those coordinate scales is a separate, explicit obligation.
-/

namespace Kreps.PreferenceProperties

open scoped unitInterval BigOperators

/-- Coordinatewise straight interpolation stays in a product of real intervals. -/
def intervalProductPath {K : Type*} {S : K → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (x y : ∀ i, S i) (t : I) (i : K) : S i :=
  ⟨(1 - t.val) * (x i).val + t.val * (y i).val, by
    simpa only [smul_eq_mul] using (hS i).convex (x i).property (y i).property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩

/-- Straight interpolation is continuous in the product's relative topology. -/
theorem intervalProductPath_continuous {K : Type*} {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i) :
    Continuous (intervalProductPath hS x y) := by
  apply continuous_pi
  intro i
  exact (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

/-- Straight interpolation has the prescribed endpoints. -/
theorem intervalProductPath_endpoints {K : Type*} {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i) :
    intervalProductPath hS x y 0 = x ∧ intervalProductPath hS x y 1 = y := by
  constructor <;> funext i <;> apply Subtype.ext <;> simp [intervalProductPath]

/-- Total score increases along the straight path whenever its endpoint scores are ordered. -/
theorem intervalProductPath_sum_monotone {K : Type*} [Fintype K] {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val ≤ ∑ i, (y i).val) :
    Monotone (fun t : I => ∑ i, (intervalProductPath hS x y t i).val) := by
  have hs (t : I) : (∑ i, (intervalProductPath hS x y t i).val) =
      (1 - t.val) * (∑ i, (x i).val) + t.val * (∑ i, (y i).val) := by
    simp [intervalProductPath, Finset.sum_add_distrib, Finset.mul_sum]
  intro a b hab
  change a.val ≤ b.val at hab
  change (∑ i, (intervalProductPath hS x y a i).val) ≤
    ∑ i, (intervalProductPath hS x y b i).val
  rw [hs, hs]
  have := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hab)
  nlinarith

/-- Local representation by one aligned sum is global on any finite product of real intervals. -/
theorem sum_represents_of_locally_represents {K : Type*} [Fintype K] {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) {u : (∀ i, S i) → ℝ}
    (hl : ∀ x, ∃ U : Set (∀ i, S i), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ ∑ i, (y i).val ≤ ∑ i, (z i).val) :
    Represents (fun x : ∀ i, S i => ∑ i, (x i).val) (UtilityPref u) := by
  have h := global_order_of_local_comparisons hl (fun x y hxy =>
    ⟨intervalProductPath hS x y, intervalProductPath_continuous hS x y,
      (intervalProductPath_endpoints hS x y).1, (intervalProductPath_endpoints hS x y).2,
      intervalProductPath_sum_monotone hS x y hxy⟩)
  intro x y
  exact h y x

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Monotonicity and insatiability

Kreps I, Section 2.1, pp. 31-32: Definitions 2.1 and 2.3, Proposition 2.2,
and the positive implications in Problem 2.6. Coordinatewise strict increases
are kept distinct from a weak increase with at least one strict coordinate.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop}

/-- **Definition 2.1:** coordinatewise increases are weak preference improvements. -/
def MonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → r x y

/-- **Definition 2.1:** a distinct weakly larger bundle is strictly preferred. -/
def StrictlyMonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → x ≠ y → Strict r x y

/-- The intermediate condition on p. 32 requires a strict increase in every coordinate. -/
def StrictAllIncreasePreference {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x y, (∀ j, y.val j < x.val j) → Strict r x y

/-- **Definition 2.3a:** every bundle has a strictly better alternative. -/
def GloballyInsatiable (r : X → X → Prop) : Prop := ∀ x, ∃ y, Strict r y x

/-- **Definition 2.3b:** a strict improvement exists at distance at most every positive radius. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

/-- **Proposition 2.2**, first equivalence. -/
theorem proposition_2_2_monotone [PartialOrder X] {u : X → ℝ} (hu : Represents u r) :
    MonotonePreference r ↔ Monotone u := by
  constructor
  · intro h x y hxy
    exact (hu y x).mp (h y x hxy)
  · intro h x y hyx
    exact (hu x y).mpr (h hyx)

/-- **Proposition 2.2**, second equivalence. -/
theorem proposition_2_2_strict [PartialOrder X] {u : X → ℝ} (hu : Represents u r) :
    StrictlyMonotonePreference r ↔ StrictMono u := by
  constructor
  · intro h x y hxy
    exact (strict_iff_utility_lt hu y x).mp (h y x hxy.le (ne_of_gt hxy))
  · intro h x y hyx hne
    exact (strict_iff_utility_lt hu x y).mpr (h (lt_of_le_of_ne hyx hne.symm))

/-- The universal quantifier emphasized after Proposition 2.2 and in Problem 2.1. -/
theorem monotone_all_representations [PartialOrder X] (hr : MonotonePreference r) :
    ∀ u : X → ℝ, Represents u r → Monotone u :=
  fun _ hu => (proposition_2_2_monotone hu).mp hr

/-- Existence of one nondecreasing representation suffices for monotone preference. -/
theorem monotone_of_some_representation [PartialOrder X]
    (h : ∃ u : X → ℝ, Represents u r ∧ Monotone u) : MonotonePreference r := by
  obtain ⟨u, hu, hm⟩ := h
  exact (proposition_2_2_monotone hu).mpr hm

/-- Every representation of strictly monotone preference is strictly increasing. -/
theorem strict_all_representations [PartialOrder X] (hr : StrictlyMonotonePreference r) :
    ∀ u : X → ℝ, Represents u r → StrictMono u :=
  fun _ hu => (proposition_2_2_strict hu).mp hr

/-- Existence of one strictly increasing representation suffices. -/
theorem strict_of_some_representation [PartialOrder X]
    (h : ∃ u : X → ℝ, Represents u r ∧ StrictMono u) : StrictlyMonotonePreference r := by
  obtain ⟨u, hu, hm⟩ := h
  exact (proposition_2_2_strict hu).mpr hm

/-- Rational strictly monotone preferences are monotone, including equality of bundles. -/
theorem strictlyMonotone_monotone [PartialOrder X] (hc : Complete r)
    (hs : StrictlyMonotonePreference r) : MonotonePreference r := by
  intro x y hyx
  by_cases hxy : x = y
  · subst y
    exact complete_refl hc x
  · exact (hs x y hyx hxy).1

/-- A strict coordinatewise increase is a nontrivial weak increase in positive dimension. -/
theorem strictlyMonotone_strictAllIncrease {k : ℕ} (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hs : StrictlyMonotonePreference r) : StrictAllIncreasePreference r := by
  intro x y hxy
  refine hs x y (fun j => (hxy j).le) ?_
  intro he
  have h := hxy ⟨0, hk⟩
  rw [he] at h
  exact (lt_irrefl _ h)

/-- The closed-radius definition is equivalent to using open balls. -/
theorem locallyInsatiable_iff_open [PseudoMetricSpace X] :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x < ε ∧ Strict r y x := by
  constructor
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x (ε / 2) (by positivity)
    exact ⟨y, lt_of_le_of_lt hy (by linarith), hr⟩
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x ε hε
    exact ⟨y, hy.le, hr⟩

/-- Local insatiability implies global insatiability. -/
theorem locallyInsatiable_global [PseudoMetricSpace X] (h : LocallyInsatiable r) :
    GloballyInsatiable r := by
  intro x
  obtain ⟨y, _, hy⟩ := h x 1 zero_lt_one
  exact ⟨y, hy⟩

/-- Insatiability in terms of any representing utility, as observed on p. 32. -/
theorem globallyInsatiable_iff_utility {u : X → ℝ} (hu : Represents u r) :
    GloballyInsatiable r ↔ ∀ x, ∃ y, u x < u y := by
  simp only [GloballyInsatiable, strict_iff_utility_lt hu]

/-- The corresponding local numerical restatement. -/
theorem locallyInsatiable_iff_utility [PseudoMetricSpace X] {u : X → ℝ}
    (hu : Represents u r) :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ u x < u y := by
  simp only [LocallyInsatiable, strict_iff_utility_lt hu]

/-- Add the same positive amount to every component. -/
def RaisedBundle {k : ℕ} (x : NonnegativeOrthant k) (δ : ℝ) (hδ : 0 ≤ δ) :
    NonnegativeOrthant k := ⟨fun j => x.val j + δ, fun j => add_nonneg (x.property j) hδ⟩

/-- In the finite-product metric, the common coordinate increase bounds the distance. -/
theorem raisedBundle_dist_le {k : ℕ} (x : NonnegativeOrthant k) {δ : ℝ} (hδ : 0 ≤ δ) :
    dist (RaisedBundle x δ hδ) x ≤ δ := by
  change dist (fun j => x.val j + δ) x.val ≤ δ
  apply (dist_pi_le_iff hδ).mpr
  intro j
  simp [abs_of_nonneg hδ]

/-- **Problem 2.6:** strict all-coordinate improvement gives LNS without continuity. -/
theorem strictAllIncrease_locallyInsatiable {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hs : StrictAllIncreasePreference r) : LocallyInsatiable r := by
  intro x ε hε
  refine ⟨RaisedBundle x ε hε.le, raisedBundle_dist_le x hε.le, ?_⟩
  apply hs
  intro j
  change x.val j < x.val j + ε
  linarith

/-- Monotonicity and LNS give strict all-coordinate improvement without continuity. -/
theorem monotone_locallyInsatiable_strictAllIncrease {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hm : MonotonePreference r) (hl : LocallyInsatiable r) :
    StrictAllIncreasePreference r := by
  intro x y hyx
  let U : Set (NonnegativeOrthant k) := {z | ∀ j, z.val j < x.val j}
  have ho : IsOpen U := by
    have heq : U = ⋂ j, {z : NonnegativeOrthant k | z.val j < x.val j} := by
      ext z
      simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_apply j).comp continuous_subtype_val) continuous_const
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp ho y hyx
  obtain ⟨z, hz, hzy⟩ := locallyInsatiable_iff_open.mp hl y ε hε
  have hzx : z ≤ x := fun j => (hb hz j).le
  exact weak_strict_trans hr.2 (hm x z hzx) hzy

/-- Continuity supplies the missing weak monotonicity in **Problem 2.6**. -/
theorem continuous_strictAllIncrease_monotone {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StrictAllIncreasePreference r) :
    MonotonePreference r := by
  intro x y hyx
  by_contra hnot
  have hyx' := (proposition_1_9a hr.1 y x).mpr hnot
  obtain ⟨ε, hε, hb⟩ := continuousPreference_iff_metric.mp hc y x hyx'
  let z := RaisedBundle x (ε / 2) (by positivity)
  have hz : dist z x < ε :=
    lt_of_le_of_lt (raisedBundle_dist_le x (by positivity)) (by linarith)
  have hyz := hb y z (by simpa using hε) hz
  have hzy : Strict r z y := hs z y (fun j => by
    change y.val j < x.val j + ε / 2
    have h := hyx j
    linarith)
  exact hyz.2 hzy.1

/-- **Problem 2.6**, full equivalence under the stated continuity assumption. -/
theorem problem_2_6 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) :
    StrictAllIncreasePreference r ↔ MonotonePreference r ∧ LocallyInsatiable r :=
  ⟨fun hs => ⟨continuous_strictAllIncrease_monotone hr hc hs,
      strictAllIncrease_locallyInsatiable hs⟩,
    fun h => monotone_locallyInsatiable_strictAllIncrease hr h.1 h.2⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Convex preferences and convex choice sets

Kreps I, Definition 2.4 and Propositions 2.5-2.6, p. 33; Problem 2.4, p. 46.
The statements are proved on any convex real-vector-space domain. Specializing the
domain to the nonnegative orthant gives the book's setting. Subtype mixtures retain
domain membership, and convexity of a menu is proved equivalent to Mathlib's ambient
set convexity. In particular, no nonemptiness of the maximizing set is assumed.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- A convex combination stays in its convex consumption domain. -/
def Mix (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- Weight zero selects the second bundle. -/
theorem mix_zero (hS : Convex ℝ S) (x y : S) (ha : (0 : ℝ) ∈ Set.Icc 0 1) :
    Mix hS x y 0 ha = y := by
  apply Subtype.ext
  simp [Mix]

/-- Weight one selects the first bundle. -/
theorem mix_one (hS : Convex ℝ S) (x y : S) (ha : (1 : ℝ) ∈ Set.Icc 0 1) :
    Mix hS x y 1 ha = x := by
  apply Subtype.ext
  simp [Mix]

/-- Mixing a bundle with itself leaves it unchanged. -/
theorem mix_self (hS : Convex ℝ S) (x : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Mix hS x x a ha = x := by
  apply Subtype.ext
  simp [Mix, ← add_smul]

/-- Reversing the endpoints replaces the weight by its complement. -/
theorem mix_swap (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Mix hS x y a ha =
      Mix hS y x (1 - a) ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩ := by
  apply Subtype.ext
  simp [Mix, add_comm]

/-- Convexity of a menu inside its convex domain. -/
def ConvexMenu (hS : Convex ℝ S) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a, ∀ ha : a ∈ Set.Icc 0 1, Mix hS x y a ha ∈ A

/-- The menu definition is exactly convexity of its image in the ambient vector space. -/
theorem convexMenu_iff (hS : Convex ℝ S) (A : Set S) :
    ConvexMenu hS A ↔ Convex ℝ (Subtype.val '' A) := by
  constructor
  · intro h x hx y hy a b ha hb hab
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    refine ⟨Mix hS x y a ha', h x hx y hy a ha', ?_⟩
    change a • x.val + (1 - a) • y.val = a • x.val + b • y.val
    rw [show 1 - a = b by linarith]
  · intro h x hx y hy a ha
    have hm := h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha.1
      (sub_nonneg.mpr ha.2) (show a + (1 - a) = 1 by ring)
    obtain ⟨z, hz, he⟩ := hm
    have hz' : z = Mix hS x y a ha := Subtype.ext he
    exact hz' ▸ hz

/-- **Definition 2.4a:** mixtures are weakly preferred to the worse endpoint. -/
def ConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- **Definition 2.4b:** interior mixtures of distinct comparable endpoints strictly improve. -/
def StrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- **Definition 2.4c:** convexity plus strict improvement when the endpoints differ in rank. -/
def SemiStrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ConvexPreference hS r ∧ ∀ x y, Strict r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- Strict convexity includes weak convexity, including endpoint and equal-bundle cases. -/
theorem strictlyConvex_convex {hS : Convex ℝ S} {r : S → S → Prop} (hc : Complete r)
    (hs : StrictlyConvexPreference hS r) : ConvexPreference hS r := by
  intro x y hxy a ha
  by_cases he : x = y
  · subst y
    rw [mix_self]
    exact complete_refl hc x
  by_cases h0 : a = 0
  · subst a
    rw [mix_zero]
    exact complete_refl hc y
  by_cases h1 : a = 1
  · subst a
    rw [mix_one]
    exact hxy
  exact (hs x y he hxy a ⟨lt_of_le_of_ne ha.1 (Ne.symm h0),
    lt_of_le_of_ne ha.2 h1⟩).1

/-- Strict convexity implies semi-strict convexity. -/
theorem strictlyConvex_semiStrict {hS : Convex ℝ S} {r : S → S → Prop} (hc : Complete r)
    (hs : StrictlyConvexPreference hS r) : SemiStrictlyConvexPreference hS r := by
  refine ⟨strictlyConvex_convex hc hs, fun x y hxy a ha => ?_⟩
  apply hs x y _ hxy.1 a ha
  intro he
  subst y
  exact hxy.2 hxy.1

/-- The upper-contour characterization, stated internally to the consumption domain. -/
theorem convexPreference_iff_contours {hS : Convex ℝ S} {r : S → S → Prop}
    (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, ConvexMenu hS (NoWorseThan r z) := by
  constructor
  · intro hc z x hx y hy a ha
    rcases hr.1 x y with hxy | hyx
    · exact hr.2 _ y z (hc x y hxy a ha) hy
    · change r (Mix hS x y a ha) z
      rw [mix_swap]
      exact hr.2 _ x z (hc y x hyx (1 - a)
        ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩) hx
  · intro h x y hxy a ha
    exact h y x hxy y (complete_refl hr.1 y) a ha

/-- **Proposition 2.5:** every NWT set is convex in the ambient vector space. -/
theorem proposition_2_5 {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, Convex ℝ (Subtype.val '' NoWorseThan r z) := by
  rw [convexPreference_iff_contours hr]
  exact forall_congr' fun z => convexMenu_iff hS (NoWorseThan r z)

/-- **Proposition 2.6**, convexity of the best set, which is allowed to be empty. -/
theorem proposition_2_6_convex {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r)
    (hc : ConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    ConvexMenu hS (PrefChoice r A) := by
  intro x hx y hy a ha
  refine ⟨hA x hx.1 y hy.1 a ha, fun z hz => ?_⟩
  exact hr.2 _ y z (hc x y (hx.2 y hy.1) a ha) (hy.2 z hz)

/-- **Proposition 2.6**, strict convexity gives at most one best bundle. -/
theorem proposition_2_6_unique {hS : Convex ℝ S} {r : S → S → Prop}
    (hs : StrictlyConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    (PrefChoice r A).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := hs x y hne (hx.2 y hy.1) (1 / 2) (by constructor <;> norm_num)
  exact hm.2 (hy.2 _ (hA x hx.1 y hy.1 (1 / 2) (by constructor <;> norm_num)))

/-- **Problem 2.4** is precisely the upper-contour equivalence. -/
theorem problem_2_4 {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, Convex ℝ (Subtype.val '' NoWorseThan r z) :=
  proposition_2_5 hr

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Weak separability and an increasing aggregator

Kreps I, Definition 2.11 and Proposition 2.12, pp. 40-41. A bundle consists of
finitely many independent commodity blocks and an arbitrary leftover bundle.
The aggregator is defined only on attained subutility ranges and is strictly
increasing when some block score increases and none decreases.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*} {L : Type*}

/-- The selected disjoint blocks, together with all leftover goods. -/
abbrev BlockBundle (B : I → Type*) (L : Type*) := (∀ i, B i) × L

/-- Substitute one block while keeping every other good fixed. -/
def ReplaceBlock [DecidableEq I] (s : BlockBundle B L) (i : I) (a : B i) : BlockBundle B L :=
  (Function.update s.1 i a, s.2)

/-- **Definition 2.11:** comparisons within each block ignore the surrounding bundle. -/
def WeaklySeparable [DecidableEq I] (r : BlockBundle B L → BlockBundle B L → Prop) : Prop :=
  ∀ i a b s t, r (ReplaceBlock s i a) (ReplaceBlock s i b) ↔
    r (ReplaceBlock t i a) (ReplaceBlock t i b)

/-- Independence of the surrounding goods also preserves strict comparisons. -/
theorem weaklySeparable_strict [DecidableEq I]
    {r : BlockBundle B L → BlockBundle B L → Prop} (hs : WeaklySeparable r)
    (i : I) (a b : B i) (s t : BlockBundle B L) :
    Strict r (ReplaceBlock s i a) (ReplaceBlock s i b) ↔
      Strict r (ReplaceBlock t i a) (ReplaceBlock t i b) :=
  and_congr (hs i a b s t) (not_congr (hs i b a s t))

/-- The book's subutility, evaluated against a fixed reference bundle. -/
def BaselineSubutility [DecidableEq I] (u : BlockBundle B L → ℝ) (s₀ : BlockBundle B L)
    (i : I) (a : B i) : ℝ := u (ReplaceBlock s₀ i a)

/-- Weak separability transports each baseline comparison to every surrounding bundle. -/
theorem baseline_comparison_iff [DecidableEq I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ : BlockBundle B L) (i : I) (s : BlockBundle B L)
    (a b : B i) :
    u (ReplaceBlock s i a) ≤ u (ReplaceBlock s i b) ↔
      BaselineSubutility u s₀ i a ≤ BaselineSubutility u s₀ i b := by
  calc
    u (ReplaceBlock s i a) ≤ u (ReplaceBlock s i b) ↔
        r (ReplaceBlock s i b) (ReplaceBlock s i a) := (hu _ _).symm
    _ ↔ r (ReplaceBlock s₀ i b) (ReplaceBlock s₀ i a) := hs i b a s s₀
    _ ↔ BaselineSubutility u s₀ i a ≤ BaselineSubutility u s₀ i b := hu _ _

/-- Each coordinate carries its score and evidence that the score is attained. -/
def BlockScores (w : ∀ i, B i → ℝ) (x : ∀ i, B i) : ∀ i, Set.range (w i) :=
  fun i => ⟨w i (x i), x i, rfl⟩

/-- Block substitution changes exactly the corresponding score coordinate. -/
theorem blockScores_update [DecidableEq I] (w : ∀ i, B i → ℝ)
    (x : ∀ i, B i) (i : I) (a : B i) :
    BlockScores w (Function.update x i a) =
      Function.update (BlockScores w x) i ⟨w i a, a, rfl⟩ := by
  funext j
  apply Subtype.ext
  by_cases hj : j = i
  · subst j
    simp [BlockScores]
  · simp [BlockScores, Function.update_of_ne hj]

/-- Select an actual block attaining a given subutility value. -/
noncomputable def ScoreRepresentative (w : ∀ i, B i → ℝ) (i : I)
    (q : Set.range (w i)) : B i := Classical.choose q.property

/-- The selected block has exactly the specified score. -/
theorem scoreRepresentative_spec (w : ∀ i, B i → ℝ) (i : I) (q : Set.range (w i)) :
    w i (ScoreRepresentative w i q) = q.val := Classical.choose_spec q.property

/-- Reconstruct utility from representatives of the attained block scores. -/
noncomputable def SubutilityAggregator (u : BlockBundle B L → ℝ) (w : ∀ i, B i → ℝ)
    (p : (∀ i, Set.range (w i)) × L) : ℝ :=
  u ((fun i => ScoreRepresentative w i (p.1 i)), p.2)

/-- Strict increase in the first coordinates, with the leftover goods held fixed. -/
def IncreasingAggregator (w : ∀ i, B i → ℝ)
    (V : ((∀ i, Set.range (w i)) × L) → ℝ) : Prop :=
  ∀ l, StrictMono (fun q => V (q, l))

/-- The exact factorization of the given utility required by **Proposition 2.12**. -/
def WeakSeparabilityRepresentation (u : BlockBundle B L → ℝ) : Prop :=
  ∃ w : ∀ i, B i → ℝ, ∃ V : ((∀ i, Set.range (w i)) × L) → ℝ,
    IncreasingAggregator w V ∧ ∀ x, u x = V (BlockScores w x.1, x.2)

/-- A strictly increasing aggregator orders changes in one block by its subutility. -/
theorem aggregator_coordinate_comparison [DecidableEq I] {w : ∀ i, B i → ℝ}
    {V : ((∀ i, Set.range (w i)) × L) → ℝ} (hV : IncreasingAggregator w V)
    (x : ∀ i, B i) (l : L) (i : I) (a b : B i) :
    V (BlockScores w (Function.update x i a), l) ≤
      V (BlockScores w (Function.update x i b), l) ↔ w i a ≤ w i b := by
  rw [blockScores_update, blockScores_update]
  exact ((hV l).comp Function.update_strictMono).le_iff_le

/-- The aggregator form implies independence of the surrounding goods. -/
theorem weaklySeparable_of_representation [DecidableEq I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hf : WeakSeparabilityRepresentation u) : WeaklySeparable r := by
  obtain ⟨w, V, hV, he⟩ := hf
  intro i a b s t
  have hcompare (z : BlockBundle B L) :
      r (ReplaceBlock z i a) (ReplaceBlock z i b) ↔ w i b ≤ w i a := by
    rw [hu, he (ReplaceBlock z i b), he (ReplaceBlock z i a)]
    exact aggregator_coordinate_comparison hV z.1 z.2 i b a
  exact (hcompare s).trans (hcompare t).symm

/-- Equal subutility coordinates give equal overall utility by the finite substitution chain. -/
theorem subutilityAggregator_factors [DecidableEq I] [Finite I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ x : BlockBundle B L) :
    u x = SubutilityAggregator u (BaselineSubutility u s₀)
      (BlockScores (BaselineSubutility u s₀) x.1, x.2) := by
  let w := BaselineSubutility u s₀
  change u (x.1, x.2) = u ((fun i => ScoreRepresentative w i (BlockScores w x.1 i)), x.2)
  apply finite_coordinate_eq (F := fun z => u (z, x.2)) (w := w)
    (fun i z a b h => (baseline_comparison_iff hu hs s₀ i (z, x.2) a b).mpr h)
  intro i
  exact (scoreRepresentative_spec w i (BlockScores w x.1 i)).symm

/-- A strict increase of any score makes the finite substitution chain strict. -/
theorem subutilityAggregator_increasing [DecidableEq I] [Finite I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ : BlockBundle B L) :
    IncreasingAggregator (BaselineSubutility u s₀)
      (SubutilityAggregator u (BaselineSubutility u s₀)) := by
  let w := BaselineSubutility u s₀
  intro l q t hqt
  have hle := le_of_lt hqt
  have hn := not_le_of_gt hqt
  change ¬∀ i, t i ≤ q i at hn
  obtain ⟨i, hi⟩ := not_forall.mp hn
  change u ((fun j => ScoreRepresentative w j (q j)), l) <
    u ((fun j => ScoreRepresentative w j (t j)), l)
  apply finite_coordinate_strict (F := fun z => u (z, l)) (w := w)
    (fun j z a b => baseline_comparison_iff hu hs s₀ j (z, l) a b)
  · intro j
    rw [scoreRepresentative_spec w j (q j), scoreRepresentative_spec w j (t j)]
    exact hle j
  · refine ⟨i, ?_⟩
    rw [scoreRepresentative_spec w i (q i), scoreRepresentative_spec w i (t i)]
    exact lt_of_not_ge hi

/-- The baseline construction supplies both the exact factorization and strict increase. -/
theorem weakSeparabilityRepresentation_of_separable [DecidableEq I] [Finite I]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (s₀ : BlockBundle B L) :
    WeakSeparabilityRepresentation u :=
  ⟨BaselineSubutility u s₀, SubutilityAggregator u (BaselineSubutility u s₀),
    subutilityAggregator_increasing hu hs s₀, subutilityAggregator_factors hu hs s₀⟩

/-- **Proposition 2.12:** weak separability is equivalent to the given utility's factorization. -/
theorem proposition_2_12 [DecidableEq I] [Finite I] [Nonempty (BlockBundle B L)]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) : WeaklySeparable r ↔ WeakSeparabilityRepresentation u := by
  constructor
  · intro hs
    obtain ⟨s₀⟩ := ‹Nonempty (BlockBundle B L)›
    exact weakSeparabilityRepresentation_of_separable hu hs s₀
  · exact weaklySeparable_of_representation hu

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Upper semicontinuity of weighted lower-contour utility

Kreps I, Problem 2.10, p. 47. Nonnegative summable weights give an upper
semicontinuous utility sum for any sequence of reference points. Strictly
positive weights represent preference when the references separate strict ranks.
The dyadic weights are exactly `1 / 2^(n+1)`, with zero-based enumeration of the
book's points `q¹,q²,...`. Density of their range suffices for representation.
-/

namespace Kreps.PreferenceProperties

variable {X I : Type*} {r : X → X → Prop}

/-- Sum the weights of enumerated reference points no better than the given alternative. -/
noncomputable def SampledWeightedUtility (r : X → X → Prop) (q : I → X)
    (w : I → ℝ) (x : X) : ℝ := ∑' i, {j | r x (q j)}.indicator w i

/-- Closed weak upper contours make each nonnegative weighted indicator upper semicontinuous. -/
theorem sampledWeightedTerm_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) (q : I → X) {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i : I) :
    UpperSemicontinuous (fun x => {j | r x (q j)}.indicator w i) := by
  change UpperSemicontinuous ((NoWorseThan r (q i)).indicator (fun _ => w i))
  exact (((proposition_1_14c hr).mp hc) (q i)).2.upperSemicontinuous_indicator (hw i)

/-- Summability supplies a uniform tail bound, preserving upper semicontinuity of the series. -/
theorem sampledWeightedUtility_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) (q : I → X) {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) :
    UpperSemicontinuous (SampledWeightedUtility r q w) := by
  apply upperSemicontinuous_tsum_of_norm_le hs (sampledWeightedTerm_upperSemicontinuous hr hc q hw)
  intro i x
  classical
  change ‖if r x (q i) then w i else 0‖ ≤ w i
  split_ifs
  · simp only [Real.norm_eq_abs, abs_of_nonneg (hw i), le_refl]
  · simpa only [norm_zero] using hw i

/-- The set-indexed weighted utility from Chapter 1 satisfies the same conclusion. -/
theorem weightedUtility_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) {D : Set X} {w : D → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hs : Summable w) : UpperSemicontinuous (WeightedUtility r D w) :=
  sampledWeightedUtility_upperSemicontinuous hr hc Subtype.val hw hs

/-- Weak preference increases every sampled weighted term. -/
theorem sampledWeightedTerm_mono (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (ht : TransitivePref r) {x y : X} (hxy : r x y) (i : I) :
    {j | r y (q j)}.indicator w i ≤ {j | r x (q j)}.indicator w i := by
  classical
  change (if r y (q i) then w i else 0) ≤ if r x (q i) then w i else 0
  by_cases hy : r y (q i)
  · simp [hy, ht x y (q i) hxy hy]
  · simp only [hy, ite_false]
    split_ifs
    · exact hw i
    · exact le_rfl

/-- Weak preference increases the sampled weighted sum. -/
theorem sampledWeightedUtility_mono (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : TransitivePref r) {x y : X} (hxy : r x y) :
    SampledWeightedUtility r q w y ≤ SampledWeightedUtility r q w x :=
  Summable.tsum_le_tsum (sampledWeightedTerm_mono q hw ht hxy)
    (hs.indicator _) (hs.indicator _)

/-- A sampled separating point contributes a strictly positive increase. -/
theorem sampledWeightedUtility_strict (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (hs : Summable w) (ht : TransitivePref r) (hq : OrderSeparating r (Set.range q))
    {x y : X} (hxy : Strict r x y) :
    SampledWeightedUtility r q w y < SampledWeightedUtility r q w x := by
  classical
  obtain ⟨z, ⟨i, rfl⟩, hxz, hzy⟩ := hq x y hxy
  have hi : {j | r y (q j)}.indicator w i < {j | r x (q j)}.indicator w i := by
    change (if r y (q i) then w i else 0) < if r x (q i) then w i else 0
    simpa only [hzy.2, hxz, ite_false, ite_true] using hw i
  exact Summable.tsum_lt_tsum (sampledWeightedTerm_mono q (fun j => (hw j).le) ht hxy.1)
    hi (hs.indicator _) (hs.indicator _)

/-- Positive summable weights on any separating enumeration represent preference. -/
theorem sampledWeightedUtility_represents (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (hs : Summable w) (hr : Rational r) (hq : OrderSeparating r (Set.range q)) :
    Represents (SampledWeightedUtility r q w) r := by
  intro x y
  constructor
  · exact sampledWeightedUtility_mono q (fun i => (hw i).le) hs hr.2
  · intro h
    by_contra hxy
    have hyx : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact not_lt_of_ge h (sampledWeightedUtility_strict q hw hs hr.2 hq hyx)

/-- The book's geometric weights, with the first enumerated point indexed by zero. -/
noncomputable def DyadicWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- These are exactly the displayed reciprocal powers of two. -/
theorem dyadicWeight_formula (n : ℕ) : DyadicWeight n = 1 / (2 : ℝ) ^ (n + 1) := by
  simp [DyadicWeight]

/-- Every enumerated point has strictly positive weight. -/
theorem dyadicWeight_pos (n : ℕ) : 0 < DyadicWeight n := pow_pos (by norm_num) _

/-- The geometric sequence is summable. -/
theorem dyadicWeight_summable : Summable DyadicWeight := by
  have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  simp only [pow_succ]
  exact hs.mul_right (1 / 2)

/-- The sampled dyadic sum is the formula displayed in Problem 2.10. -/
theorem sampledDyadicUtility_formula [DecidableRel r] (q : ℕ → X) (x : X) :
    SampledWeightedUtility r q DyadicWeight x =
      ∑' n, if r x (q n) then 1 / (2 : ℝ) ^ (n + 1) else 0 := by
  apply tsum_congr
  intro n
  classical
  by_cases h : r x (q n)
  · simp [h, dyadicWeight_formula]
  · simp [h]

/-- **Problem 2.10:** the displayed utility is upper semicontinuous for any enumeration. -/
theorem problem_2_10 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (q : ℕ → NonnegativeOrthant k) :
    UpperSemicontinuous (SampledWeightedUtility r q DyadicWeight) :=
  sampledWeightedUtility_upperSemicontinuous hr hc q (fun n => (dyadicWeight_pos n).le)
    dyadicWeight_summable

/-- For an enumeration with dense range, the same formula also represents preference. -/
theorem problem_2_10_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (q : ℕ → NonnegativeOrthant k) (hq : Dense (Set.range q)) :
    Represents (SampledWeightedUtility r q DyadicWeight) r := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  exact sampledWeightedUtility_represents q dyadicWeight_pos dyadicWeight_summable hr
    (dense_orderSeparating hr hc hq)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: sequential semicontinuity

Proposition A2.25, p. 451. Extended-real limsup and liminf include sequences
whose function values are unbounded. Subtype domains give the stated relative version.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Real-valued upper semicontinuity is unchanged by inclusion in the extended real line. -/
theorem upperSemicontinuousAt_real_coe {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt (fun y => (f y : EReal)) x ↔ UpperSemicontinuousAt f x := by
  constructor
  · intro h r hr
    exact (h (r : EReal) (EReal.coe_lt_coe hr)).mono fun _ hy =>
      EReal.coe_lt_coe_iff.mp hy
  · intro h a hxa
    induction a using EReal.rec with
    | bot => exact False.elim (not_lt_bot hxa)
    | coe r =>
      exact (h r (EReal.coe_lt_coe_iff.mp hxa)).mono fun _ hy => EReal.coe_lt_coe hy
    | top => exact Filter.Eventually.of_forall fun y => EReal.coe_lt_top (f y)

/-- Real-valued lower semicontinuity is also unchanged by the inclusion. -/
theorem lowerSemicontinuousAt_real_coe {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt (fun y => (f y : EReal)) x ↔ LowerSemicontinuousAt f x := by
  constructor
  · intro h r hr
    exact (h (r : EReal) (EReal.coe_lt_coe hr)).mono fun _ hy =>
      EReal.coe_lt_coe_iff.mp hy
  · intro h a hax
    induction a using EReal.rec with
    | bot => exact Filter.Eventually.of_forall fun y => EReal.bot_lt_coe (f y)
    | coe r =>
      exact (h r (EReal.coe_lt_coe_iff.mp hax)).mono fun _ hy => EReal.coe_lt_coe hy
    | top => exact False.elim (not_top_lt hax)

/-- Upper semicontinuity at a point is characterized by sequential limsup inequalities. -/
theorem appendix2_upper_sequence_iff {X γ : Type*} [PseudoMetricSpace X]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ] (f : X → γ) (x : X) :
    UpperSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) → Filter.limsup (f ∘ u) Filter.atTop ≤ f x := by
  constructor
  · intro h u hu
    exact hu.limsup_comp_le_limsup.trans (upperSemicontinuousAt_iff_limsup_le.mp h)
  · intro h a ha
    have hx : x ∉ closure {y | a ≤ f y} := by
      intro hmem
      obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
      have hlo : a ≤ Filter.liminf (f ∘ u) Filter.atTop :=
        Filter.le_liminf_of_le (by isBoundedDefault) (Filter.Eventually.of_forall hu)
      have hls : Filter.liminf (f ∘ u) Filter.atTop ≤ Filter.limsup (f ∘ u) Filter.atTop :=
        Filter.liminf_le_limsup
      exact (not_le_of_gt ha) (hlo.trans (hls.trans (h u hlim)))
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    exact lt_of_not_ge (fun hge => hy (subset_closure hge))

/-- The lower-semicontinuity version follows by reversing the complete order. -/
theorem appendix2_lower_sequence_iff {X γ : Type*} [PseudoMetricSpace X]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ] (f : X → γ) (x : X) :
    LowerSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) → f x ≤ Filter.liminf (f ∘ u) Filter.atTop :=
  appendix2_upper_sequence_iff (γ := γᵒᵈ) f x

/-- **Proposition A2.25:** upper semicontinuity at a point is the limsup inequality. -/
theorem proposition_A2_25_upper {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    UpperSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) →
        Filter.limsup (fun n => (f (u n) : EReal)) Filter.atTop ≤ (f x : EReal) :=
  (upperSemicontinuousAt_real_coe f x).symm.trans (appendix2_upper_sequence_iff _ x)

/-- **Proposition A2.25:** lower semicontinuity at a point is the liminf inequality. -/
theorem proposition_A2_25_lower {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (x : X) :
    LowerSemicontinuousAt f x ↔ ∀ u : ℕ → X,
      Filter.Tendsto u Filter.atTop (𝓝 x) →
        (f x : EReal) ≤ Filter.liminf (fun n => (f (u n) : EReal)) Filter.atTop :=
  (lowerSemicontinuousAt_real_coe f x).symm.trans (appendix2_lower_sequence_iff _ x)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 2: the two sequence examples

The sequences `{10,20,30,...}` and `{1.1,2.1,1.01,2.01,...}` on pp. 445–446.
Natural-number indexing begins at zero, so the first formula uses `n + 1`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The diverging sequence displayed on p. 445. -/
def TenSequence (n : ℕ) : ℝ := 10 * (n + 1)

/-- The multiples of ten diverge to positive infinity. -/
theorem tenSequence_tendsto : Filter.Tendsto TenSequence Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b / 10)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [TenSequence]
  nlinarith

/-- The diverging sequence has no real accumulation point, as asserted on p. 446. -/
theorem tenSequence_no_accumulation (x : ℝ) : ¬MapClusterPt x Filter.atTop TenSequence := by
  intro h
  obtain ⟨φ, hφ, hlim⟩ := h.tendsto_subseq
  exact not_tendsto_atTop_of_tendsto_nhds hlim (tenSequence_tendsto.comp hφ.tendsto_atTop)

/-- In particular the sequence has no finite limit. -/
theorem tenSequence_no_limit : ¬∃ x : ℝ, Filter.Tendsto TenSequence Filter.atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  exact tenSequence_no_accumulation x hx.mapClusterPt

/-- The alternating decimal sequence, with each decimal increment used twice. -/
noncomputable def AlternatingDecimalSequence (n : ℕ) : ℝ :=
  (if n % 2 = 0 then 1 else 2) + (1 / 10 : ℝ) ^ (n / 2 + 1)

/-- The even-indexed subsequence approaches one. -/
theorem alternatingDecimal_even (n : ℕ) :
    AlternatingDecimalSequence (2 * n) = 1 + (1 / 10 : ℝ) ^ (n + 1) := by
  have hm : (2 * n) % 2 = 0 := by omega
  have hd : (2 * n) / 2 = n := by omega
  simp only [AlternatingDecimalSequence, hm, hd, ite_true]

/-- The odd-indexed subsequence approaches two. -/
theorem alternatingDecimal_odd (n : ℕ) :
    AlternatingDecimalSequence (2 * n + 1) = 2 + (1 / 10 : ℝ) ^ (n + 1) := by
  have hm : (2 * n + 1) % 2 ≠ 0 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp only [AlternatingDecimalSequence, hm, hd, ite_false]

/-- The displayed decimal perturbations tend to zero. -/
theorem decimalPerturbation_tendsto :
    Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ (n / 2 + 1)) Filter.atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply hp.comp
  apply Filter.tendsto_atTop.mpr
  intro N
  exact Filter.eventually_atTop.mpr ⟨2 * N, fun n hn => by omega⟩

/-- Both printed subsequences converge to their stated, distinct limits. -/
theorem alternatingDecimal_subsequence_limits :
    Filter.Tendsto (fun n => AlternatingDecimalSequence (2 * n)) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (fun n => AlternatingDecimalSequence (2 * n + 1)) Filter.atTop (𝓝 2) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  constructor
  · simpa only [alternatingDecimal_even, pow_succ, zero_mul, add_zero] using
      (tendsto_const_nhds.add (hp.mul_const (1 / 10 : ℝ)) :
        Filter.Tendsto (fun n => 1 + (1 / 10 : ℝ) ^ n * (1 / 10)) Filter.atTop (𝓝 (1 + 0 * _)))
  · simpa only [alternatingDecimal_odd, pow_succ, zero_mul, add_zero] using
      (tendsto_const_nhds.add (hp.mul_const (1 / 10 : ℝ)) :
        Filter.Tendsto (fun n => 2 + (1 / 10 : ℝ) ^ n * (1 / 10)) Filter.atTop (𝓝 (2 + 0 * _)))

/-- The accumulation points are exactly one and two. -/
theorem appendix2_alternating_accumulation (x : ℝ) :
    MapClusterPt x Filter.atTop AlternatingDecimalSequence ↔ x = 1 ∨ x = 2 := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hlim⟩ := h.tendsto_subseq
    have hbase := hlim.sub (decimalPerturbation_tendsto.comp hφ.tendsto_atTop)
    have hin : ∀ n, AlternatingDecimalSequence (φ n) -
        (1 / 10 : ℝ) ^ (φ n / 2 + 1) ∈ ({1, 2} : Set ℝ) := by
      intro n
      by_cases hn : φ n % 2 = 0 <;> simp [AlternatingDecimalSequence, hn]
    have hc : IsClosed ({1, 2} : Set ℝ) := (by simp : Set.Finite ({1, 2} : Set ℝ)).isClosed
    have hx := hc.mem_of_tendsto hbase (Filter.Eventually.of_forall hin)
    simpa only [sub_zero, Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  · rintro (rfl | rfl)
    · have hm : StrictMono (fun n : ℕ => 2 * n) := by intro a b h; dsimp; omega
      exact MapClusterPt.of_comp hm.tendsto_atTop
        alternatingDecimal_subsequence_limits.1.mapClusterPt
    · have hm : StrictMono (fun n : ℕ => 2 * n + 1) := by intro a b h; dsimp; omega
      exact MapClusterPt.of_comp hm.tendsto_atTop
        alternatingDecimal_subsequence_limits.2.mapClusterPt

/-- The alternating sequence has no limit despite its two accumulation points. -/
theorem appendix2_alternating_no_limit :
    ¬∃ x : ℝ, Filter.Tendsto AlternatingDecimalSequence Filter.atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have he : StrictMono (fun n : ℕ => 2 * n) := by intro a b h; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro a b h; dsimp; omega
  have h1 := tendsto_nhds_unique (hx.comp he.tendsto_atTop)
    alternatingDecimal_subsequence_limits.1
  have h2 := tendsto_nhds_unique (hx.comp ho.tendsto_atTop)
    alternatingDecimal_subsequence_limits.2
  linarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Uniqueness of additive scales on interval rectangles

Preparation for Proposition 2.14. Preserving the indifferences of an additive
representation on two nontrivial intervals forces a common affine scale.
Strict increase makes its slope positive. No smoothness assumption is used.
-/

namespace Kreps.PreferenceProperties

/-- Transformed coordinate scores preserve equal sums on a rectangle. -/
def PreservesPairSumEquality (f g : ℝ → ℝ) (S T : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
    x + y = x' + y' → f x + g y = f x' + g y'

/-- The equal-sum condition is symmetric in its two coordinates. -/
theorem preservesPairSumEquality_symm {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) : PreservesPairSumEquality g f T S := by
  intro y hy y' hy' x hx x' hx' he
  have := h x hx x' hx' y hy y' hy' (by linarith)
  linarith

/-- Short compensating changes in the second coordinate give a local midpoint law in the first. -/
theorem preservesPairSumEquality_midpoint {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    {a b : ℝ} (ha : a ∈ T) (hb : b ∈ T) (x t : ℝ) (ht : 0 < t) (htb : t < b - a)
    (hlo : x - t ∈ S) (hhi : x + t ∈ S) :
    f x = (f (x - t) + f (x + t)) / 2 := by
  have hx : x ∈ S := hS.out hlo hhi ⟨by linarith, by linarith⟩
  have hat : a + t ∈ T := hT.out ha hb ⟨by linarith, by linarith⟩
  have h₁ := h (x - t) hlo x hx (a + t) hat a ha (by ring)
  have h₂ := h x hx (x + t) hhi (a + t) hat a ha (by ring)
  linarith

/-- Equal-sum preservation makes the first coordinate transformation affine. -/
theorem preservesPairSumEquality_affine_left {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hc : ContinuousOn f S) {a b c d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hcT : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B : ℝ, ∀ x ∈ S, f x = A * x + B :=
  local_midpoint_affine_interval hS hc ha hb hab (sub_pos.mpr hcd)
    (fun x t ht htd hlo hhi => preservesPairSumEquality_midpoint h hS hT hcT hd
      x t ht htd hlo hhi)

/-- Two continuous additive scales on nontrivial intervals differ by one common affine slope. -/
theorem pair_additive_affine_unique {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hf : ContinuousOn f S) (hg : ContinuousOn g T) {a b c d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B C : ℝ, (∀ x ∈ S, f x = A * x + B) ∧ (∀ y ∈ T, g y = A * y + C) := by
  obtain ⟨A, B, hA⟩ := preservesPairSumEquality_affine_left h hS hT hf ha hb hab hc hd hcd
  obtain ⟨A', C, hA'⟩ := preservesPairSumEquality_affine_left
    (preservesPairSumEquality_symm h) hT hS hg hc hd hcd ha hb hab
  let t := min (b - a) (d - c)
  have ht : 0 < t := lt_min (sub_pos.mpr hab) (sub_pos.mpr hcd)
  have htS : t ≤ b - a := min_le_left _ _
  have htT : t ≤ d - c := min_le_right _ _
  have hat : a + t ∈ S := hS.out ha hb ⟨by linarith, by linarith⟩
  have hct : c + t ∈ T := hT.out hc hd ⟨by linarith, by linarith⟩
  have he := h (a + t) hat a ha c hc (c + t) hct (by ring)
  rw [hA _ hat, hA _ ha, hA' _ hc, hA' _ hct] at he
  have hAA : A = A' := by nlinarith
  exact ⟨A, B, C, hA, hAA ▸ hA'⟩

/-- Strict increase makes the common affine scale positive. -/
theorem pair_additive_positive_affine_unique {f g : ℝ → ℝ} {S T : Set ℝ}
    (h : PreservesPairSumEquality f g S T) (hS : S.OrdConnected) (hT : T.OrdConnected)
    (hf : ContinuousOn f S) (hg : ContinuousOn g T) (hmono : StrictMonoOn f S)
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ A B C : ℝ, 0 < A ∧ (∀ x ∈ S, f x = A * x + B) ∧
      (∀ y ∈ T, g y = A * y + C) := by
  obtain ⟨A, B, C, hA, hC⟩ := pair_additive_affine_unique h hS hT hf hg ha hb hab hc hd hcd
  have hlt := hmono ha hb hab
  rw [hA _ ha, hA _ hb] at hlt
  exact ⟨A, B, C, by nlinarith, hA, hC⟩

/-- Two nontrivial coordinates fix one positive affine slope for an entire family of intervals. -/
theorem family_additive_positive_affine_unique {I : Type*} {S : I → Set ℝ}
    {f : I → ℝ → ℝ} (hS : ∀ i, (S i).OrdConnected) (hf : ∀ i, ContinuousOn (f i) (S i))
    (hp : ∀ i j, i ≠ j → PreservesPairSumEquality (f i) (f j) (S i) (S j))
    (z : I → ℝ) (hz : ∀ i, z i ∈ S i) {i₀ j₀ : I} (hij : i₀ ≠ j₀)
    (hmono : StrictMonoOn (f i₀) (S i₀)) {a b c d : ℝ}
    (ha : a ∈ S i₀) (hb : b ∈ S i₀) (hab : a < b)
    (hc : c ∈ S j₀) (hd : d ∈ S j₀) (hcd : c < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ i x, x ∈ S i →
      f i x = A * x + (f i (z i) - A * z i) := by
  classical
  obtain ⟨A, B, _, hpos, hA, _⟩ := pair_additive_positive_affine_unique (hp i₀ j₀ hij)
    (hS i₀) (hS j₀) (hf i₀) (hf j₀) hmono ha hb hab hc hd hcd
  refine ⟨A, hpos, fun i x hx => ?_⟩
  by_cases hi : i = i₀
  · subst i
    have hxA := hA x hx
    have hzA := hA (z i₀) (hz i₀)
    linarith
  · by_cases hnt : (S i).Nontrivial
    · obtain ⟨c', hc', d', hd', hcd'⟩ := hnt.exists_lt
      obtain ⟨A', B', C', hA', hC'⟩ := pair_additive_affine_unique
        (hp i₀ i (Ne.symm hi)) (hS i₀) (hS i) (hf i₀) (hf i) ha hb hab hc' hd' hcd'
      have hAa := hA a ha
      have hAb := hA b hb
      have hA'a := hA' a ha
      have hA'b := hA' b hb
      have he : A = A' := by nlinarith
      have hxA := hC' x hx
      have hzA := hC' (z i) (hz i)
      rw [← he] at hxA hzA
      linarith
    · have he : x = z i := by
        by_contra hne
        exact hnt ⟨x, hx, z i, hz i, hne⟩
      rw [he]
      ring

/-- Fixing every baseline and one unit increment removes all affine freedom on an overlap. -/
theorem normalized_additive_scales_unique {I : Type*} {S : I → Set ℝ} {f : I → ℝ → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hf : ∀ i, ContinuousOn (f i) (S i))
    (hp : ∀ i j, i ≠ j → PreservesPairSumEquality (f i) (f j) (S i) (S j))
    (hz : ∀ i, (0 : ℝ) ∈ S i) (hzero : ∀ i, f i 0 = 0)
    {i₀ j₀ : I} (hij : i₀ ≠ j₀) (hmono : StrictMonoOn (f i₀) (S i₀))
    (hunit : (1 : ℝ) ∈ S i₀) (hone : f i₀ 1 = 1) {c d : ℝ}
    (hc : c ∈ S j₀) (hd : d ∈ S j₀) (hcd : c < d) :
    ∀ i x, x ∈ S i → f i x = x := by
  obtain ⟨A, _, hA⟩ := family_additive_positive_affine_unique hS hf hp (fun _ => 0) hz hij
    hmono (hz i₀) hunit zero_lt_one hc hd hcd
  have hAu := hA i₀ 1 hunit
  have hAone : A = 1 := by simpa only [hone, hzero, mul_one, mul_zero, sub_zero, add_zero]
    using hAu.symm
  intro i x hx
  simpa only [hAone, one_mul, hzero, mul_zero, sub_zero, add_zero] using hA i x hx

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concavity, quasi-concavity and representation

Kreps I, Definition 2.7 and Proposition 2.8, pp. 34-35. Functions are defined on
the convex consumption domain, without arbitrary values outside it. The bridge
theorems identify these domain-internal definitions with Mathlib's `ConcaveOn`,
`StrictConcaveOn` and `QuasiconcaveOn` for ambient functions restricted to the domain.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition 2.7a:** Jensen's concavity inequality. -/
def ConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1,
    a * u x + (1 - a) * u y ≤ u (Mix hS x y a ha)

/-- **Definition 2.7b:** strict Jensen inequality for distinct endpoints and interior weights. -/
def StrictlyConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    a * u x + (1 - a) * u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- **Definition 2.7c:** a mixture is no worse than the lower-valued endpoint. -/
def QuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, min (u x) (u y) ≤ u (Mix hS x y a ha)

/-- **Definition 2.7d:** quasi-concavity and strict improvement over a strictly worse endpoint. -/
def SemiStrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  QuasiConcaveUtility hS u ∧ ∀ x y, u y < u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- **Definition 2.7e:** distinct weakly ordered endpoints give a strict improvement. -/
def StrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- The domain-internal concavity definition is Mathlib concavity for restricted functions. -/
theorem concaveUtility_iff_concaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    ConcaveUtility hS (fun x => f x.val) ↔ ConcaveOn ℝ S f := by
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- The corresponding bridge for strict concavity. -/
theorem strictlyConcaveUtility_iff_strictConcaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    StrictlyConcaveUtility hS (fun x => f x.val) ↔ StrictConcaveOn ℝ S f := by
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy hne a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hne (congrArg Subtype.val he))
      a ⟨ha, by linarith⟩
  · intro h x y hne a ha
    exact h.2 x.property y.property (fun he => hne (Subtype.ext he))
      ha.1 (sub_pos.mpr ha.2) (by ring)

/-- The minimum formulation agrees with Mathlib's upper-contour definition. -/
theorem quasiConcaveUtility_iff_quasiconcaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConcaveUtility hS (fun x => f x.val) ↔ QuasiconcaveOn ℝ S f := by
  rw [quasiconcaveOn_iff_min_le]
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- Concavity implies quasi-concavity by comparing the weighted average with its smaller term. -/
theorem concaveUtility_quasi {hS : Convex ℝ S} {u : S → ℝ}
    (hc : ConcaveUtility hS u) : QuasiConcaveUtility hS u := by
  intro x y a ha
  calc
    min (u x) (u y) = a * min (u x) (u y) + (1 - a) * min (u x) (u y) := by ring
    _ ≤ a * u x + (1 - a) * u y := add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left _ _) ha.1)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (sub_nonneg.mpr ha.2))
    _ ≤ u (Mix hS x y a ha) := hc x y a ha

/-- Concavity also gives the semi-strict improvement used in later counterexamples. -/
theorem concaveUtility_semiStrict {hS : Convex ℝ S} {u : S → ℝ}
    (hc : ConcaveUtility hS u) : SemiStrictlyQuasiConcaveUtility hS u := by
  refine ⟨concaveUtility_quasi hc, fun x y hyx a ha => ?_⟩
  have hg := mul_pos ha.1 (sub_pos.mpr hyx)
  have hm := hc x y a ⟨ha.1.le, ha.2.le⟩
  nlinarith

/-- Strict concavity implies strict quasi-concavity. -/
theorem strictlyConcaveUtility_strictQuasi {hS : Convex ℝ S} {u : S → ℝ}
    (hc : StrictlyConcaveUtility hS u) : StrictlyQuasiConcaveUtility hS u := by
  intro x y hne hyx a ha
  have hg := mul_nonneg ha.1.le (sub_nonneg.mpr hyx)
  have hm := hc x y hne a ha
  nlinarith

/-- **Proposition 2.8b**, quasi-concavity iff preference convexity. -/
theorem proposition_2_8b_quasi {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) : QuasiConcaveUtility hS u ↔ ConvexPreference hS r := by
  constructor
  · intro h x y hxy a ha
    apply (hu _ y).mpr
    have hyx := (hu x y).mp hxy
    simpa only [min_eq_right hyx] using h x y a ha
  · intro h x y a ha
    rcases le_total (u y) (u x) with hyx | hxy
    · rw [min_eq_right hyx]
      exact (hu _ y).mp (h x y ((hu x y).mpr hyx) a ha)
    · rw [min_eq_left hxy, mix_swap]
      exact (hu _ x).mp (h y x ((hu y x).mpr hxy) (1 - a)
        ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩)

/-- **Proposition 2.8b**, strict quasi-concavity iff strict preference convexity. -/
theorem proposition_2_8b_strict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) :
    StrictlyQuasiConcaveUtility hS u ↔ StrictlyConvexPreference hS r := by
  constructor
  · intro h x y hne hxy a ha
    exact (strict_iff_utility_lt hu _ y).mpr (h x y hne ((hu x y).mp hxy) a ha)
  · intro h x y hne hyx a ha
    exact (strict_iff_utility_lt hu _ y).mp (h x y hne ((hu x y).mpr hyx) a ha)

/-- **Proposition 2.8b**, semi-strict quasi-concavity iff semi-strict preference convexity. -/
theorem proposition_2_8b_semiStrict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) :
    SemiStrictlyQuasiConcaveUtility hS u ↔ SemiStrictlyConvexPreference hS r := by
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨(proposition_2_8b_quasi hu).mp hq, fun x y hxy a ha => ?_⟩
    exact (strict_iff_utility_lt hu _ y).mpr
      (hs x y ((strict_iff_utility_lt hu x y).mp hxy) a ha)
  · rintro ⟨hq, hs⟩
    refine ⟨(proposition_2_8b_quasi hu).mpr hq, fun x y hyx a ha => ?_⟩
    exact (strict_iff_utility_lt hu _ y).mp
      (hs x y ((strict_iff_utility_lt hu x y).mpr hyx) a ha)

/-- **Proposition 2.8a**, a concave representation gives convex preference. -/
theorem proposition_2_8a_concave {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) (hc : ConcaveUtility hS u) : ConvexPreference hS r :=
  (proposition_2_8b_quasi hu).mp (concaveUtility_quasi hc)

/-- **Proposition 2.8a**, the strict version. -/
theorem proposition_2_8a_strict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) (hc : StrictlyConcaveUtility hS u) :
    StrictlyConvexPreference hS r :=
  (proposition_2_8b_strict hu).mp (strictlyConcaveUtility_strictQuasi hc)

/-- The conclusion on p. 35: increasing ordinal rescaling preserves quasi-concavity. -/
theorem quasiConcave_strictMono_transform {hS : Convex ℝ S} {u : S → ℝ}
    (hq : QuasiConcaveUtility hS u) {f : ℝ → ℝ} (hf : StrictMono f) :
    QuasiConcaveUtility hS (f ∘ u) := by
  intro x y a ha
  change min (f (u x)) (f (u y)) ≤ f (u (Mix hS x y a ha))
  rw [← hf.monotone.map_min]
  exact hf.monotone (hq x y a ha)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Monotonicity without continuity

Kreps I, Problem 2.6, p. 46. Lexicographic comparison with reversed second-coordinate
ties is strictly monotone when every coordinate increases, and locally insatiable,
but is neither weakly monotone nor continuous. This completes the distinction between
the unconditional implications and the equivalence requiring continuous preferences.
-/

namespace Kreps.PreferenceProperties

/-- A convenient two-good bundle with explicitly nonnegative coordinates. -/
def PairBundle (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : NonnegativeOrthant 2 :=
  ⟨fun j => if j = 0 then a else b, fun j => by dsimp; split_ifs <;> assumption⟩

/-- Prefer more of the first good; when it ties, prefer less of the second good. -/
def ReverseTiePreference (x y : NonnegativeOrthant 2) : Prop :=
  y.val 0 < x.val 0 ∨ (x.val 0 = y.val 0 ∧ x.val 1 ≤ y.val 1)

/-- The reversed-tie lexicographic relation is still a complete transitive preference. -/
theorem reverseTie_rational : Rational ReverseTiePreference := by
  constructor
  · intro x y
    by_cases he : x.val 0 = y.val 0
    · rcases le_total (x.val 1) (y.val 1) with h | h
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr (Or.inr ⟨he.symm, h⟩)
    · rcases lt_or_gt_of_ne he with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
  · intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxy, hxy'⟩
    · rcases hyz with hyz | ⟨hyz, _⟩
      · exact Or.inl (hyz.trans hxy)
      · exact Or.inl (by linarith)
    · rcases hyz with hyz | ⟨hyz, hyz'⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨hxy.trans hyz, hxy'.trans hyz'⟩

/-- Increasing every coordinate improves the first coordinate and so strictly improves rank. -/
theorem reverseTie_strictAllIncrease : StrictAllIncreasePreference ReverseTiePreference := by
  intro x y hxy
  refine ⟨Or.inl (hxy 0), ?_⟩
  rintro (h | ⟨he, _⟩)
  · exact (not_lt_of_gt (hxy 0)) h
  · have h := hxy 0
    linarith

/-- Increasing only the second coordinate can make a bundle strictly worse. -/
theorem reverseTie_not_monotone : ¬MonotonePreference ReverseTiePreference := by
  intro h
  have hm := h (PairBundle 0 1 (by norm_num) (by norm_num))
    (PairBundle 0 0 (by norm_num) (by norm_num)) (by
      intro j
      fin_cases j <;> norm_num [PairBundle])
  norm_num [ReverseTiePreference, PairBundle] at hm

/-- Despite that failure, there are arbitrarily nearby strict improvements. -/
theorem reverseTie_locallyInsatiable : LocallyInsatiable ReverseTiePreference :=
  strictAllIncrease_locallyInsatiable reverseTie_strictAllIncrease

/-- Continuity is exactly what this counterexample lacks in the equivalence of Problem 2.6. -/
theorem reverseTie_not_continuous : ¬ContinuousPreference ReverseTiePreference :=
  fun hc => reverseTie_not_monotone
    (continuous_strictAllIncrease_monotone reverseTie_rational hc reverseTie_strictAllIncrease)

/-- **Problem 2.6**, the counterexample when continuity is removed. -/
theorem problem_2_6_without_continuity :
    Rational ReverseTiePreference ∧ StrictAllIncreasePreference ReverseTiePreference ∧
    LocallyInsatiable ReverseTiePreference ∧ ¬MonotonePreference ReverseTiePreference ∧
    ¬ContinuousPreference ReverseTiePreference :=
  ⟨reverseTie_rational, reverseTie_strictAllIncrease, reverseTie_locallyInsatiable,
    reverseTie_not_monotone, reverseTie_not_continuous⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local improvements from convexity

Kreps I, Problem 2.3, p. 46. Global insatiability and semi-strict convexity give
local insatiability on a convex consumption domain. The proof makes an arbitrarily
small movement toward a better point. No continuity assumption is used.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- Distance along a mixture is its weight times the distance between the endpoints. -/
theorem mix_dist (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    dist (Mix hS y x a ha) x = a * dist y x := by
  change dist (a • y.val + (1 - a) • x.val) x.val = a * dist y.val x.val
  rw [dist_eq_norm, dist_eq_norm]
  have he : a • y.val + (1 - a) • x.val - x.val = a • (y.val - x.val) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]

/-- **Problem 2.3**, the positive implication, for any convex normed-space domain. -/
theorem problem_2_3_implication {hS : Convex ℝ S} {r : S → S → Prop}
    (hg : GloballyInsatiable r) (hs : SemiStrictlyConvexPreference hS r) :
    LocallyInsatiable r := by
  intro x ε hε
  obtain ⟨y, hy⟩ := hg x
  let a := min (1 / 2 : ℝ) (ε / (dist y x + 1))
  have hd : 0 < dist y x + 1 := by positivity
  have ha0 : 0 < a := lt_min (by norm_num) (div_pos hε hd)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ha : a ∈ Set.Icc 0 1 := ⟨ha0.le, ha1.le⟩
  refine ⟨Mix hS y x a ha, ?_, hs.2 y x hy a ⟨ha0, ha1⟩⟩
  rw [mix_dist]
  have hbound : a * (dist y x + 1) ≤ ε :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  nlinarith

/-- Strict convexity is a sufficient special case. -/
theorem strictlyConvex_global_local {hS : Convex ℝ S} {r : S → S → Prop}
    (hc : Complete r) (hg : GloballyInsatiable r) (hs : StrictlyConvexPreference hS r) :
    LocallyInsatiable r :=
  problem_2_3_implication hg (strictlyConvex_semiStrict hc hs)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuous utility and intermediate indifference

Kreps I, the forward direction of Proposition 2.9, the compact-choice consequence
on p. 35, and Lemma 2.10, pp. 36, 38. The connected-image lemma proves the path
crossing result without assuming a continuous numerical representation. It is an
ingredient of that representation construction, not a use of the desired conclusion.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- **Proposition 2.9**, forward direction, from a continuous representation. -/
theorem proposition_2_9_forward {u : X → ℝ} (hu : Represents u r) (hc : Continuous u) :
    ContinuousPreference r := by
  have he : r = UtilityPref u := by
    funext x y
    exact propext (hu x y)
  rw [he]
  exact continuousPreference_of_continuous_utility hc

/-- The extreme-value proof of nonempty compact-menu choice described on p. 35. -/
theorem compact_choice_of_continuous_utility {u : X → ℝ} (hu : Represents u r)
    (hc : Continuous u) {A : Set X} (hA : IsCompact A) (hne : A.Nonempty) :
    (PrefChoice r A).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hA.exists_isMaxOn hne hc.continuousOn
  exact ⟨x, hx, fun y hy => (hu x y).mpr (hmax hy)⟩

/-- A connected continuous image crosses every weakly bracketed indifference class. -/
theorem indifference_on_connected_image {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] (hr : Rational r) (hc : ContinuousPreference r)
    (f : T → X) (hf : Continuous f) (x : X) {a b : T}
    (ha : r (f a) x) (hb : r x (f b)) : ∃ t, Indifferent r (f t) x := by
  by_contra hn
  push Not at hn
  let U := f ⁻¹' StrictlyBetterThan r x
  let V := f ⁻¹' StrictlyWorseThan r x
  have ho := continuousPreference_openStrictContours hc
  have hU : IsOpen U := (ho x).1.preimage hf
  have hV : IsOpen V := (ho x).2.preimage hf
  have ha' : a ∈ U := ⟨ha, fun h => hn a ⟨ha, h⟩⟩
  have hb' : b ∈ V := ⟨hb, fun h => hn b ⟨h, hb⟩⟩
  have hcover : Set.univ ⊆ U ∪ V := by
    intro t _
    rcases hr.1 (f t) x with h | h
    · exact Or.inl ⟨h, fun h' => hn t ⟨h, h'⟩⟩
    · exact Or.inr ⟨h, fun h' => hn t ⟨h', h⟩⟩
  obtain ⟨t, _, htU, htV⟩ := isPreconnected_univ U V hU hV hcover
    ⟨a, Set.mem_univ a, ha'⟩ ⟨b, Set.mem_univ b, hb'⟩
  exact htU.2 htV.1

/-- **Lemma 2.10:** a continuous path between weak preference bounds meets the middle class. -/
theorem lemma_2_10 (hr : Rational r) (hc : ContinuousPreference r)
    (f : UnitSegment → X) (hf : Continuous f) (x : X)
    (h0 : r (f ⟨0, by norm_num⟩) x) (h1 : r x (f ⟨1, by norm_num⟩)) :
    ∃ t, Indifferent r (f t) x := by
  let : PreconnectedSpace UnitSegment := isPreconnected_iff_preconnectedSpace.mp
    (convex_Icc (0 : ℝ) 1).isPreconnected
  exact indifference_on_connected_image hr hc f hf x h0 h1

/-- Section 2.4: monotonicity converts coordinate bounds into the bounds in Lemma 2.10. -/
theorem monotone_path_crossing {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (f : UnitSegment → NonnegativeOrthant k) (hf : Continuous f) (x : NonnegativeOrthant k)
    (h0 : x ≤ f ⟨0, by norm_num⟩) (h1 : f ⟨1, by norm_num⟩ ≤ x) :
    ∃ t, Indifferent r (f t) x :=
  lemma_2_10 hr hc f hf x (hm _ _ h0) (hm _ _ h1)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Commodity-index blocks and leftover goods

Kreps I, the notation preceding Definition 2.11, p. 40. Each commodity is
assigned to a selected block or to the leftover bundle. Every family of disjoint
commodity subsets admits such an assignment. Grouping is a genuine equivalence
with the original orthant, and block replacement changes exactly its assigned goods.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k n : ℕ}

/-- The nonnegative quantities of goods assigned to a selected block. -/
abbrev AssignedBlock (owner : Fin k → Option (Fin n)) (i : Fin n) :=
  {j : Fin k // owner j = some i} → ℝ≥0

/-- The goods belonging to none of the selected blocks. -/
abbrev LeftoverBlock (owner : Fin k → Option (Fin n)) :=
  {j : Fin k // owner j = none} → ℝ≥0

/-- Read each selected block and the leftover quantities from a full bundle. -/
def GroupCommodities (owner : Fin k → Option (Fin n)) (x : Fin k → ℝ≥0) :
    BlockBundle (AssignedBlock owner) (LeftoverBlock owner) :=
  ((fun _ j => x j.val), fun j => x j.val)

/-- Recover a commodity quantity from its uniquely assigned block. -/
def UngroupCommodities (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (j : Fin k) : ℝ≥0 :=
  match h : owner j with
  | none => x.2 ⟨j, h⟩
  | some i => x.1 i ⟨j, h⟩

/-- Recover a quantity from a known selected block. -/
theorem ungroupCommodities_some (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (j : Fin k) (hj : owner j = some i) :
    UngroupCommodities owner x j = x.1 i ⟨j, hj⟩ := by
  unfold UngroupCommodities
  split
  · rename_i hn
    have hf := hn.symm.trans hj
    cases hf
  · rename_i l hl
    have he : l = i := Option.some.inj (hl.symm.trans hj)
    subst l
    rfl

/-- Recover a quantity known to lie in the leftover bundle. -/
theorem ungroupCommodities_none (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner))
    (j : Fin k) (hj : owner j = none) :
    UngroupCommodities owner x j = x.2 ⟨j, hj⟩ := by
  unfold UngroupCommodities
  split
  · rfl
  · rename_i i hi
    have hf := hi.symm.trans hj
    cases hf

/-- Grouping and recovering leave every commodity quantity unchanged. -/
theorem ungroup_groupCommodities (owner : Fin k → Option (Fin n)) (x : Fin k → ℝ≥0) :
    UngroupCommodities owner (GroupCommodities owner x) = x := by
  funext j
  unfold UngroupCommodities
  split <;> rfl

/-- Recovering and regrouping preserve all selected blocks and all leftover goods. -/
theorem group_ungroupCommodities (owner : Fin k → Option (Fin n))
    (x : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) :
    GroupCommodities owner (UngroupCommodities owner x) = x := by
  apply Prod.ext
  · funext i j
    exact ungroupCommodities_some owner x i j.val j.property
  · funext j
    exact ungroupCommodities_none owner x j.val j.property

/-- The commodity grouping is a bijective change of coordinates. -/
def commodityGroupingEquiv (owner : Fin k → Option (Fin n)) :
    (Fin k → ℝ≥0) ≃ BlockBundle (AssignedBlock owner) (LeftoverBlock owner) where
  toFun := GroupCommodities owner
  invFun := UngroupCommodities owner
  left_inv := ungroup_groupCommodities owner
  right_inv := group_ungroupCommodities owner

/-- Coordinatewise nonnegative reals are exactly the chapter's nonnegative orthant. -/
def orthantNNRealEquiv (k : ℕ) : NonnegativeOrthant k ≃ (Fin k → ℝ≥0) where
  toFun x j := .mk (x.val j) (x.property j)
  invFun x := ⟨fun j => (x j : ℝ), fun j => (x j).property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    funext j
    exact NNReal.coe_injective rfl

/-- Group the original orthant into selected commodity blocks and their complement. -/
def orthantGrouping (owner : Fin k → Option (Fin n)) :
    NonnegativeOrthant k ≃ BlockBundle (AssignedBlock owner) (LeftoverBlock owner) :=
  (orthantNNRealEquiv k).trans (commodityGroupingEquiv owner)

/-- A grouped block coordinate is precisely the original commodity coordinate. -/
theorem orthantGrouping_block (owner : Fin k → Option (Fin n)) (x : NonnegativeOrthant k)
    (i : Fin n) (j : {j : Fin k // owner j = some i}) :
    (((orthantGrouping owner x).1 i j) : ℝ) = x.val j.val := rfl

/-- The same coordinate identity holds for leftover goods. -/
theorem orthantGrouping_leftover (owner : Fin k → Option (Fin n)) (x : NonnegativeOrthant k)
    (j : {j : Fin k // owner j = none}) :
    (((orthantGrouping owner x).2 j) : ℝ) = x.val j.val := rfl

/-- Replacing a block changes its assigned commodity to the specified new quantity. -/
theorem ungroup_replace_in_block (owner : Fin k → Option (Fin n))
    (s : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (a : AssignedBlock owner i) (j : Fin k) (hj : owner j = some i) :
    UngroupCommodities owner (ReplaceBlock s i a) j = a ⟨j, hj⟩ := by
  rw [ungroupCommodities_some owner (ReplaceBlock s i a) i j hj]
  simp [ReplaceBlock]

/-- Replacing a block leaves every unassigned commodity unchanged. -/
theorem ungroup_replace_outside (owner : Fin k → Option (Fin n))
    (s : BlockBundle (AssignedBlock owner) (LeftoverBlock owner)) (i : Fin n)
    (a : AssignedBlock owner i) (j : Fin k) (hj : owner j ≠ some i) :
    UngroupCommodities owner (ReplaceBlock s i a) j = UngroupCommodities owner s j := by
  cases h : owner j with
  | none =>
    rw [ungroupCommodities_none owner (ReplaceBlock s i a) j h,
      ungroupCommodities_none owner s j h]
    rfl
  | some l =>
    have hli : l ≠ i := by
      intro he
      subst l
      exact hj h
    rw [ungroupCommodities_some owner (ReplaceBlock s i a) l j h,
      ungroupCommodities_some owner s l j h]
    simp [ReplaceBlock, Function.update_of_ne hli]

/-- Two distinct selected blocks cannot contain the same commodity. -/
theorem assigned_blocks_disjoint (owner : Fin k → Option (Fin n))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint {a | owner a = some i} {a | owner a = some j} := by
  apply Set.disjoint_left.mpr
  intro a hai haj
  exact hij (Option.some.inj (hai.symm.trans haj))

/-- Leftovers are exactly the complement of the union of selected blocks. -/
theorem assigned_leftover_iff (owner : Fin k → Option (Fin n)) (j : Fin k) :
    owner j = none ↔ ∀ i, owner j ≠ some i := by
  cases h : owner j <;> simp

/-- Every disjoint family of subsets has an assignment, including an explicit leftover class. -/
theorem exists_commodity_assignment (J : Fin n → Set (Fin k))
    (hd : ∀ i j, i ≠ j → Disjoint (J i) (J j)) :
    ∃ owner : Fin k → Option (Fin n),
      (∀ i j, owner j = some i ↔ j ∈ J i) ∧
      ∀ j, owner j = none ↔ ∀ i, j ∉ J i := by
  classical
  let owner := fun j => if h : ∃ i, j ∈ J i then some (Classical.choose h) else none
  have hblocks (i : Fin n) (j : Fin k) : owner j = some i ↔ j ∈ J i := by
    by_cases h : ∃ i, j ∈ J i
    · have hs := Classical.choose_spec h
      have he : owner j = some (Classical.choose h) := by simp [owner, h]
      rw [he, Option.some.injEq]
      constructor
      · intro hi
        exact hi ▸ hs
      · intro hji
        by_contra hne
        exact Set.disjoint_left.mp (hd _ _ hne) hs hji
    · have hji : j ∉ J i := fun hji => h ⟨i, hji⟩
      simp [owner, h, hji]
  refine ⟨owner, hblocks, ?_⟩
  intro j
  rw [assigned_leftover_iff]
  constructor
  · intro h i hi
    exact h i ((hblocks i j).mpr hi)
  · intro h i hi
    exact h i ((hblocks i j).mp hi)

/-- **Proposition 2.12** transported to the original commodity orthant. -/
theorem proposition_2_12_orthant (owner : Fin k → Option (Fin n))
    {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hu : Represents u r) :
    WeaklySeparable (fun x y => r ((orthantGrouping owner).symm x)
      ((orthantGrouping owner).symm y)) ↔
    WeakSeparabilityRepresentation (fun x => u ((orthantGrouping owner).symm x)) :=
  proposition_2_12 (fun x y => hu ((orthantGrouping owner).symm x)
    ((orthantGrouping owner).symm y))

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A continuous connect-the-dots curve

Kreps I, Problem 2.14(a), p. 48. Interpolate linearly between consecutive integer
points in a convex domain. The affine formulas agree at every integer junction;
local finiteness of the closed unit intervals gives continuity on the whole line.
A sequence indexed by natural numbers is extended constantly to negative indices.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- Linear interpolation between each consecutive pair of integer-indexed points. -/
noncomputable def PolygonalCurve (hS : Convex ℝ S) (q : ℤ → S) (t : ℝ) : S :=
  Mix hS (q (⌊t⌋ + 1)) (q ⌊t⌋) (Int.fract t)
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- At an integer, interpolation returns the prescribed point. -/
theorem polygonalCurve_int (hS : Convex ℝ S) (q : ℤ → S) (n : ℤ) :
    PolygonalCurve hS q n = q n := by
  apply Subtype.ext
  simp [PolygonalCurve, Mix]

/-- Each closed unit interval carries one affine segment, including both endpoints. -/
theorem polygonalCurve_formula (hS : Convex ℝ S) (q : ℤ → S) (n : ℤ)
    {t : ℝ} (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    (PolygonalCurve hS q t).val =
      (t - n) • (q (n + 1)).val + (1 - (t - n)) • (q n).val := by
  by_cases hn : t < (n : ℝ) + 1
  · have hf : ⌊t⌋ = n := Int.floor_eq_iff.mpr ⟨ht.1, hn⟩
    simp only [PolygonalCurve, Mix, Int.fract, hf]
  · have he : t = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith [ht.2]
    rw [he, polygonalCurve_int]
    simp

/-- The integer unit intervals form a locally finite closed cover of the real line. -/
theorem integer_unit_intervals_locallyFinite :
    LocallyFinite (fun n : ℤ => Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
  locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
    (Filter.tendsto_atBot_add_const_right _ 1
      (tendsto_intCast_atBot_iff.mpr Filter.tendsto_id))

/-- Affine continuity on the closed unit intervals glues to a continuous curve. -/
theorem polygonalCurve_continuous (hS : Convex ℝ S) (q : ℤ → S) :
    Continuous (PolygonalCurve hS q) := by
  have hcover : (⋃ n : ℤ, Set.Icc (n : ℝ) ((n : ℝ) + 1)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact Set.mem_iUnion.mpr ⟨⌊t⌋, Int.floor_le t, (Int.lt_floor_add_one t).le⟩
  have hval : Continuous (fun t => (PolygonalCurve hS q t).val) := by
    apply integer_unit_intervals_locallyFinite.continuous hcover (fun _ => isClosed_Icc)
    intro n
    have hp : Continuous (fun t : ℝ =>
        (t - n) • (q (n + 1)).val + (1 - (t - n)) • (q n).val) := by fun_prop
    apply hp.continuousOn.congr
    intro t ht
    exact polygonalCurve_formula hS q n ht
  exact hval.subtype_mk _

/-- The image of a polygonal curve is connected in the sense needed for the crossing lemma. -/
theorem polygonalCurve_range_preconnected (hS : Convex ℝ S) (q : ℤ → S) :
    IsPreconnected (Set.range (PolygonalCurve hS q)) :=
  isPreconnected_range (polygonalCurve_continuous hS q)

/-- A natural-number sequence gives a curve constant before zero and joining all its points. -/
noncomputable def SequenceCurve (hS : Convex ℝ S) (q : ℕ → S) : ℝ → S :=
  PolygonalCurve hS (fun n => q n.toNat)

/-- Every prescribed sequence point lies on the curve at its natural-number parameter. -/
theorem sequenceCurve_nat (hS : Convex ℝ S) (q : ℕ → S) (n : ℕ) :
    SequenceCurve hS q n = q n := by
  simpa only [SequenceCurve, Int.cast_natCast, Int.toNat_natCast] using
    polygonalCurve_int hS (fun m => q m.toNat) n

/-- The countable connect-the-dots construction is continuous. -/
theorem sequenceCurve_continuous (hS : Convex ℝ S) (q : ℕ → S) :
    Continuous (SequenceCurve hS q) := polygonalCurve_continuous hS _

/-- Every point in the prescribed sequence belongs to the curve image. -/
theorem sequenceCurve_contains_range (hS : Convex ℝ S) (q : ℕ → S) :
    Set.range q ⊆ Set.range (SequenceCurve hS q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, sequenceCurve_nat hS q n⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuous block scores

Preparation for Kreps I, Proposition 2.14. Continuous representations on a
connected space have interval ranges. Equivalent representations therefore
induce an order homeomorphism between their attained ranges. For a weakly
separable preference, this proves continuity of each coordinate of the exact
baseline aggregator, without requiring a continuous choice of representatives.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {r : X → X → Prop} {u v : X → ℝ}

/-- Equivalent utilities identify their attained ranges by an order isomorphism. -/
noncomputable def UtilityRangeOrderIso (hu : Represents u r) (hv : Represents v r) :
    Set.range u ≃o Set.range v where
  toFun q := ⟨UtilityTransform u v q.val, by
    obtain ⟨x, hx⟩ := q.property
    rw [← hx, utilityTransform_apply hu hv]
    exact ⟨x, rfl⟩⟩
  invFun q := ⟨UtilityTransform v u q.val, by
    obtain ⟨x, hx⟩ := q.property
    rw [← hx, utilityTransform_apply hv hu]
    exact ⟨x, rfl⟩⟩
  left_inv := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change UtilityTransform v u (UtilityTransform u v (u x)) = u x
    rw [utilityTransform_apply hu hv, utilityTransform_apply hv hu]
  right_inv := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change UtilityTransform u v (UtilityTransform v u (v x)) = v x
    rw [utilityTransform_apply hv hu, utilityTransform_apply hu hv]
  map_rel_iff' := by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    change UtilityTransform u v (u x) ≤ UtilityTransform u v (u y) ↔ u x ≤ u y
    rw [utilityTransform_apply hu hv, utilityTransform_apply hu hv]
    exact (hv y x).symm.trans (hu y x)

/-- On connected continuous utility ranges, the ordinal change of scale is continuous. -/
theorem utilityTransform_continuous_range [TopologicalSpace X] [PreconnectedSpace X]
    (hu : Represents u r) (hv : Represents v r) (huc : Continuous u) (hvc : Continuous v) :
    Continuous (fun q : Set.range u => UtilityTransform u v q.val) := by
  let : Set.OrdConnected (Set.range u) := (isPreconnected_range huc).ordConnected
  let : Set.OrdConnected (Set.range v) := (isPreconnected_range hvc).ordConnected
  exact continuous_subtype_val.comp (UtilityRangeOrderIso hu hv).continuous

variable {I : Type*} [DecidableEq I] {B : I → Type*} {L : Type*}

/-- Replacing a single block depends continuously on the replacement. -/
theorem replaceBlock_continuous [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    (s : BlockBundle B L) (i : I) : Continuous (ReplaceBlock s i) :=
  (continuous_const.update i continuous_id).prodMk continuous_const

/-- Continuous overall utility gives continuous baseline subutilities. -/
theorem baselineSubutility_continuous [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} (hu : Continuous u) (s : BlockBundle B L) (i : I) :
    Continuous (BaselineSubutility u s i) := hu.comp (replaceBlock_continuous s i)

/-- Connected commodity blocks yield interval-valued continuous baseline scores. -/
theorem baselineSubutility_ordConnected [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} (hu : Continuous u) (s : BlockBundle B L) (i : I)
    [PreconnectedSpace (B i)] : Set.OrdConnected (Set.range (BaselineSubutility u s i)) :=
  (isPreconnected_range (baselineSubutility_continuous hu s i)).ordConnected

/-- Separability identifies utility in every surrounding bundle with the baseline preference. -/
theorem baselineSubutility_represents_context {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ s : BlockBundle B L) (i : I) :
    Represents (BaselineSubutility u s i)
      (fun a b => r (ReplaceBlock s₀ i a) (ReplaceBlock s₀ i b)) := by
  intro a b
  exact (hs i a b s₀ s).trans (hu _ _)

/-- Changing the surrounding goods changes a connected block's scale continuously. -/
theorem baselineSubutility_transform_continuous
    [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (hc : Continuous u)
    (s₀ s : BlockBundle B L) (i : I) [PreconnectedSpace (B i)] :
    Continuous (fun q : Set.range (BaselineSubutility u s₀ i) =>
      UtilityTransform (BaselineSubutility u s₀ i) (BaselineSubutility u s i) q.val) :=
  utilityTransform_continuous_range
    (baselineSubutility_represents_context hu hs s₀ s₀ i)
    (baselineSubutility_represents_context hu hs s₀ s i)
    (baselineSubutility_continuous hc s₀ i) (baselineSubutility_continuous hc s i)

/-- Choosing representatives commutes with changing a single score coordinate. -/
theorem scoreRepresentatives_update (w : ∀ i, B i → ℝ) (q : ∀ i, Set.range (w i))
    (i : I) (t : Set.range (w i)) :
    (fun j => ScoreRepresentative w j (Function.update q i t j)) =
      Function.update (fun j => ScoreRepresentative w j (q j)) i
        (ScoreRepresentative w i t) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

/-- Each coordinate of the exact weak-separability aggregator is continuous. -/
theorem subutilityAggregator_coordinate_continuous
    [∀ i, TopologicalSpace (B i)] [TopologicalSpace L]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (hc : Continuous u)
    (s₀ : BlockBundle B L) (q : ∀ i, Set.range (BaselineSubutility u s₀ i))
    (l : L) (i : I) [PreconnectedSpace (B i)] :
    Continuous (fun t => SubutilityAggregator u (BaselineSubutility u s₀)
      (Function.update q i t, l)) := by
  let w := BaselineSubutility u s₀
  let s : BlockBundle B L := ((fun j => ScoreRepresentative w j (q j)), l)
  have hf := baselineSubutility_represents_context hu hs s₀ s₀ i
  have hg := baselineSubutility_represents_context hu hs s₀ s i
  convert baselineSubutility_transform_continuous hu hs hc s₀ s i using 1
  funext t
  change u ((fun j => ScoreRepresentative w j (Function.update q i t j)), l) = _
  rw [scoreRepresentatives_update]
  change BaselineSubutility u s i (ScoreRepresentative w i t) =
    UtilityTransform (w i) (BaselineSubutility u s i) t.val
  rw [← scoreRepresentative_spec w i t]
  exact (utilityTransform_apply hf hg (ScoreRepresentative w i t)).symm

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Nonattainment and insatiability counterexamples

Kreps I, Problems 2.2-2.3, p. 46. The scalar half-line is the one-good orthant.
A utility increasing up to an unattained peak and decreasing after a downward jump
gives strictly convex preferences with empty choice on [0,1]. A utility with an
initial flat portion is globally insatiable and convex, but not locally insatiable.
-/

namespace Kreps.PreferenceProperties

/-- The one-good nonnegative consumption domain. -/
abbrev OneGood : Type := Set.Ici (0 : ℝ)

/-- An increasing left branch with a downward jump, followed by a decreasing right branch. -/
noncomputable def NonattainingUtility (x : OneGood) : ℝ :=
  if x.val < 1 then x.val else -x.val

/-- This discontinuous utility is nevertheless strictly quasi-concave. -/
theorem nonattainingUtility_strictQuasi :
    StrictlyQuasiConcaveUtility (convex_Ici (0 : ℝ)) NonattainingUtility := by
  intro x y hne horder a ha
  have hx0 : 0 ≤ x.val := x.property
  have hy0 : 0 ≤ y.val := y.property
  have hne' : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  let m := a * x.val + (1 - a) * y.val
  change (if y.val < 1 then y.val else -y.val) ≤
    (if x.val < 1 then x.val else -x.val) at horder
  change (if y.val < 1 then y.val else -y.val) < (if m < 1 then m else -m)
  rcases lt_or_gt_of_ne hne' with hxy | hyx
  · have hmlo : x.val < m := by
      dsimp [m]
      nlinarith [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hxy)]
    have hmhi : m < y.val := by
      dsimp [m]
      nlinarith [mul_pos ha.1 (sub_pos.mpr hxy)]
    split_ifs at horder ⊢ <;> linarith
  · have hmlo : y.val < m := by
      dsimp [m]
      nlinarith [mul_pos ha.1 (sub_pos.mpr hyx)]
    have hmhi : m < x.val := by
      dsimp [m]
      nlinarith [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hyx)]
    split_ifs at horder ⊢ <;> linarith

/-- The corresponding preference satisfies the book's strict convexity definition. -/
theorem nonattainingPreference_strictConvex :
    StrictlyConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref NonattainingUtility) :=
  (proposition_2_8b_strict (fun _ _ => Iff.rfl)).mp nonattainingUtility_strictQuasi

/-- The compact convex menu for Problem 2.2. -/
def UnitMenu : Set OneGood := {x | x.val ≤ 1}

/-- The menu is nonempty. -/
theorem unitMenu_nonempty : UnitMenu.Nonempty := ⟨⟨0, by norm_num⟩, by norm_num [UnitMenu]⟩

/-- Its ambient image is exactly the closed unit interval. -/
theorem unitMenu_image : Subtype.val '' UnitMenu = Set.Icc (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · intro ht
    exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩

/-- The compactness is in the relative topology of the one-good orthant. -/
theorem unitMenu_compact : IsCompact UnitMenu := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, unitMenu_image]
  exact isCompact_Icc

/-- The same menu is convex, independently of the preference. -/
theorem unitMenu_convex : ConvexMenu (convex_Ici (0 : ℝ)) UnitMenu := by
  rw [convexMenu_iff, unitMenu_image]
  exact convex_Icc 0 1

/-- Every menu member is beaten by another member, so the best set is empty. -/
theorem nonattainingUtility_empty : UtilityChoice NonattainingUtility UnitMenu = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx1 : x.val ≤ 1 := hx.1
  by_cases hlt : x.val < 1
  · let y : OneGood := ⟨(x.val + 1) / 2,
      show 0 ≤ (x.val + 1) / 2 from
        div_nonneg (add_nonneg x.property zero_le_one) (by norm_num)⟩
    have hy : y ∈ UnitMenu := by change (x.val + 1) / 2 ≤ 1; linarith
    have horder := hx.2 y hy
    have hy1 : y.val < 1 := by dsimp [y]; linarith
    change NonattainingUtility y ≤ NonattainingUtility x at horder
    simp only [NonattainingUtility, ite_eq_left hlt, ite_eq_left hy1] at horder
    dsimp [y] at horder
    linarith
  · have he : x.val = 1 := le_antisymm hx1 (le_of_not_gt hlt)
    have horder := hx.2 ⟨0, by norm_num⟩ (by norm_num [UnitMenu])
    norm_num [UtilityPref, NonattainingUtility, he] at horder

/-- **Problem 2.2:** strict convexity does not give existence, even on a compact convex menu. -/
theorem problem_2_2 :
    Rational (UtilityPref NonattainingUtility) ∧
    StrictlyConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref NonattainingUtility) ∧
    UnitMenu.Nonempty ∧ ConvexMenu (convex_Ici (0 : ℝ)) UnitMenu ∧ IsCompact UnitMenu ∧
    UtilityChoice NonattainingUtility UnitMenu = ∅ :=
  ⟨proposition_1_3a _, nonattainingPreference_strictConvex, unitMenu_nonempty,
    unitMenu_convex, unitMenu_compact, nonattainingUtility_empty⟩

/-- An initially flat utility that is unbounded above. -/
noncomputable def FlatUtility (x : OneGood) : ℝ := max 0 (x.val - 1)

/-- The flat utility is nondecreasing. -/
theorem flatUtility_monotone : Monotone FlatUtility := by
  intro x y hxy
  have h : x.val ≤ y.val := hxy
  exact max_le_max le_rfl (sub_le_sub_right h 1)

/-- On a one-dimensional interval, a nondecreasing utility is quasi-concave. -/
theorem flatUtility_quasi : QuasiConcaveUtility (convex_Ici (0 : ℝ)) FlatUtility := by
  apply (quasiConcaveUtility_iff_quasiconcaveOn (convex_Ici (0 : ℝ))
    (fun x : ℝ => max 0 (x - 1))).mpr
  exact (show MonotoneOn (fun x : ℝ => max 0 (x - 1)) (Set.Ici 0) from
    fun _ _ _ _ hxy => max_le_max le_rfl (sub_le_sub_right hxy 1)).quasiconcaveOn
      (convex_Ici 0)

/-- More than two additional units always give a strict improvement over the flat part. -/
theorem flatUtility_globallyInsatiable : GloballyInsatiable (UtilityPref FlatUtility) := by
  intro x
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨x.val + 2, add_nonneg hx0 (by norm_num)⟩
  have hlt : FlatUtility x < FlatUtility y := by
    dsimp [FlatUtility, y]
    rw [max_eq_right (by linarith : 0 ≤ x.val + 2 - 1)]
    exact max_lt (by linarith) (by linarith)
  exact ⟨y, hlt.le, not_le_of_gt hlt⟩

/-- At zero, a sufficiently small ball contains no strict improvement. -/
theorem flatUtility_not_locallyInsatiable : ¬LocallyInsatiable (UtilityPref FlatUtility) := by
  intro h
  obtain ⟨y, hy, hs⟩ := h ⟨0, by norm_num⟩ (1 / 2) (by norm_num)
  have hy0 : 0 ≤ y.val := y.property
  change dist y.val (0 : ℝ) ≤ 1 / 2 at hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0] at hy
  have he : FlatUtility y = 0 := max_eq_left (by linarith)
  apply hs.2
  change FlatUtility y ≤ FlatUtility ⟨0, by norm_num⟩
  rw [he]
  norm_num [FlatUtility]

/-- **Problem 2.3:** convexity alone does not replace semi-strict convexity. -/
theorem problem_2_3_counterexample :
    Rational (UtilityPref FlatUtility) ∧ GloballyInsatiable (UtilityPref FlatUtility) ∧
    ConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref FlatUtility) ∧
    ¬LocallyInsatiable (UtilityPref FlatUtility) :=
  ⟨proposition_1_3a _, flatUtility_globallyInsatiable,
    (proposition_2_8b_quasi (fun _ _ => Iff.rfl)).mp flatUtility_quasi,
    flatUtility_not_locallyInsatiable⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Every indifference class meets the diagonal

Kreps I, the diagonal construction in Steps 2-3, pp. 37-38. The book brackets
a bundle between the diagonal bundles formed from its minimum and maximum
coordinates. Lemma 2.10 supplies an indifferent diagonal bundle. Positive dimension
is explicit because those coordinate extrema require a nonempty set of goods.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ}

/-- The diagonal bundle with the same nonnegative amount of every commodity. -/
def Diagonal (a : Set.Ici (0 : ℝ)) : NonnegativeOrthant k :=
  ⟨fun _ => a.val, fun _ => a.property⟩

/-- The diagonal parametrization is continuous. -/
theorem diagonal_continuous : Continuous (Diagonal (k := k)) :=
  (continuous_pi fun _ => continuous_subtype_val).subtype_mk _

/-- The smallest coordinate, in the positive-dimensional setting of the construction. -/
noncomputable def MinCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x.val

/-- The largest coordinate. -/
noncomputable def MaxCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x.val

/-- A nonnegative bundle has nonnegative minimum coordinate. -/
theorem minCoordinate_nonneg (hk : 0 < k) (x : NonnegativeOrthant k) :
    0 ≤ MinCoordinate hk x := by
  unfold MinCoordinate
  exact Finset.le_inf' _ _ (fun j _ => x.property j)

/-- Each coordinate lies above the minimum. -/
theorem minCoordinate_le (hk : 0 < k) (x : NonnegativeOrthant k) (j : Fin k) :
    MinCoordinate hk x ≤ x.val j := Finset.inf'_le _ (Finset.mem_univ j)

/-- Each coordinate lies below the maximum. -/
theorem le_maxCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) (j : Fin k) :
    x.val j ≤ MaxCoordinate hk x := Finset.le_sup' _ (Finset.mem_univ j)

/-- A nonnegative bundle has nonnegative maximum coordinate. -/
theorem maxCoordinate_nonneg (hk : 0 < k) (x : NonnegativeOrthant k) :
    0 ≤ MaxCoordinate hk x :=
  (x.property ⟨0, hk⟩).trans (le_maxCoordinate hk x ⟨0, hk⟩)

/-- Step 2: every bundle is indifferent to a point on the diagonal. -/
theorem diagonal_indifference_exists (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    ∃ a : Set.Ici (0 : ℝ), Indifferent r (Diagonal a) x := by
  let lo := MinCoordinate hk x
  let hi := MaxCoordinate hk x
  have hlo : 0 ≤ lo := minCoordinate_nonneg hk x
  have hhi : 0 ≤ hi := maxCoordinate_nonneg hk x
  let f (t : UnitSegment) : NonnegativeOrthant k :=
    ⟨fun _ => t.val * lo + (1 - t.val) * hi,
      fun _ => add_nonneg (mul_nonneg t.property.1 hlo)
        (mul_nonneg (sub_nonneg.mpr t.property.2) hhi)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const)
  have h0 : r (f ⟨0, by norm_num⟩) x := by
    apply hm
    intro j
    simpa [f] using le_maxCoordinate hk x j
  have h1 : r x (f ⟨1, by norm_num⟩) := by
    apply hm
    intro j
    simpa [f] using minCoordinate_le hk x j
  obtain ⟨t, ht⟩ := lemma_2_10 hr hc f hf x h0 h1
  exact ⟨⟨t.val * lo + (1 - t.val) * hi,
    add_nonneg (mul_nonneg t.property.1 hlo)
      (mul_nonneg (sub_nonneg.mpr t.property.2) hhi)⟩, ht⟩

/-- Step 3: the diagonal's numerical coordinate represents its preference order. -/
theorem diagonal_weak_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : MonotonePreference r) (hs : StrictAllIncreasePreference r)
    (a b : Set.Ici (0 : ℝ)) : r (Diagonal a) (Diagonal b) ↔ b.val ≤ a.val := by
  constructor
  · intro hab
    by_contra hnot
    exact (hs (Diagonal b) (Diagonal a) (fun _ => lt_of_not_ge hnot)).2 hab
  · intro hba
    exact hm _ _ (fun _ => hba)

/-- Equal diagonal ranks mean equal coordinates, including the boundary at zero. -/
theorem diagonal_indifferent_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : MonotonePreference r) (hs : StrictAllIncreasePreference r)
    (a b : Set.Ici (0 : ℝ)) : Indifferent r (Diagonal a) (Diagonal b) ↔ a = b := by
  change (r (Diagonal a) (Diagonal b) ∧ r (Diagonal b) (Diagonal a)) ↔ a = b
  rw [diagonal_weak_iff hm hs, diagonal_weak_iff hm hs]
  exact ⟨fun h => Subtype.ext (le_antisymm h.2 h.1), fun h => by cases h; exact ⟨le_rfl, le_rfl⟩⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The mathematical assertions in indifference-curve diagrams

Kreps I, Section 2.4, pp. 38-39. Local insatiability excludes a ball inside
an indifference class; strict monotonicity makes two-good curves decreasing;
strict convexity makes interior mixtures of distinct indifferent bundles better.
The path-crossing assertion is `monotone_path_crossing` in `ContinuousUtility`.
No smoothness assertion follows from these assumptions.
-/

namespace Kreps.PreferenceProperties

/-- The indifference class denoted I(x) in the chapter. -/
def IndifferenceClass {X : Type*} (r : X → X → Prop) (x : X) : Set X :=
  {y | Indifferent r y x}

/-- Local insatiability prevents any positive-radius ball from lying in one class. -/
theorem indifferenceClass_no_ball {X : Type*} [PseudoMetricSpace X] {r : X → X → Prop}
    (hr : Rational r) (hl : LocallyInsatiable r) (x z : X) {ε : ℝ} (hε : 0 < ε) :
    ¬Metric.ball z ε ⊆ IndifferenceClass r x := by
  intro hsub
  have hz : Indifferent r z x := hsub (by simpa using hε)
  obtain ⟨y, hy, hbetter⟩ := locallyInsatiable_iff_open.mp hl z ε hε
  have hyx : Indifferent r y x := hsub hy
  exact hbetter.2 (hr.2 z x y hz.1 hyx.2)

/-- Thus every indifference class has empty relative interior. -/
theorem indifferenceClass_interior_empty {X : Type*} [PseudoMetricSpace X]
    {r : X → X → Prop} (hr : Rational r) (hl : LocallyInsatiable r) (x : X) :
    interior (IndifferenceClass r x) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  exact indifferenceClass_no_ball hr hl x z hε (fun _ h => interior_subset (hb h))

/-- For two goods, strictly more of the first requires less of the second along a class. -/
theorem indifferenceCurve_decreasing
    {r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop}
    (hs : StrictlyMonotonePreference r) {x y : NonnegativeOrthant 2}
    (hi : Indifferent r y x) (hfirst : x.val 0 < y.val 0) : y.val 1 < x.val 1 := by
  by_contra hnot
  have hxy : x ≤ y := by
    intro j
    fin_cases j
    · exact hfirst.le
    · exact le_of_not_gt hnot
  have hne : y ≠ x := by
    intro he
    have h := congrArg (fun z : NonnegativeOrthant 2 => z.val 0) he
    linarith
  exact (hs y x hxy hne).2 hi.2

/-- Distinct indifferent endpoints have strictly better interior mixtures under strict convexity. -/
theorem indifference_mixture_strict {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {hS : Convex ℝ S} {r : S → S → Prop}
    (hs : StrictlyConvexPreference hS r) {x y : S} (hne : x ≠ y)
    (hi : Indifferent r x y) (a : ℝ) (ha : a ∈ Set.Ioo 0 1) :
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y :=
  hs x y hne hi.1 a ha

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuity and local insatiability do not imply coordinatewise path crossing

Kreps I, Problem 2.7, p. 46. The utility x₁ - x₂ is continuous and locally
insatiable. The diagonal path from (4,4) to (1,1) passes from strictly above
to strictly below (3,2) in both coordinates, but has constant utility zero
and therefore never meets that bundle's indifference class of utility one.
-/

namespace Kreps.PreferenceProperties

/-- The first good helps while the second hurts. -/
def NetUtility (x : NonnegativeOrthant 2) : ℝ := x.val 0 - x.val 1

/-- This utility is continuous on the whole orthant. -/
theorem netUtility_continuous : Continuous NetUtility :=
  ((continuous_apply 0).comp continuous_subtype_val).sub
    ((continuous_apply 1).comp continuous_subtype_val)

/-- Increasing just the first good gives an arbitrarily nearby strict improvement. -/
theorem netPreference_locallyInsatiable : LocallyInsatiable (UtilityPref NetUtility) := by
  intro x ε hε
  let y := PairBundle (x.val 0 + ε) (x.val 1)
    (add_nonneg (x.property 0) hε.le) (x.property 1)
  have hd : dist y x ≤ ε := by
    change dist (fun j : Fin 2 => if j = 0 then x.val 0 + ε else x.val 1) x.val ≤ ε
    apply (dist_pi_le_iff hε.le).mpr
    intro j
    fin_cases j
    · simp [abs_of_pos hε]
    · simpa using hε.le
  have hlt : NetUtility x < NetUtility y := by
    change x.val 0 - x.val 1 < (x.val 0 + ε) - x.val 1
    linarith
  exact ⟨y, hd, hlt.le, not_le_of_gt hlt⟩

/-- A continuous diagonal path whose endpoints lie on opposite coordinate sides of the target. -/
def AvoidingPath (t : UnitSegment) : NonnegativeOrthant 2 :=
  ⟨fun _ => 4 - 3 * t.val, fun _ => by
    change 0 ≤ 4 - 3 * t.val
    have ht : t.val ≤ 1 := t.property.2
    linarith⟩

/-- The path has no jumps. -/
theorem avoidingPath_continuous : Continuous AvoidingPath :=
  (continuous_pi fun _ =>
    continuous_const.sub (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The coordinatewise intermediate bundle has utility one. -/
def PathMiddle : NonnegativeOrthant 2 := PairBundle 3 2 (by norm_num) (by norm_num)

/-- Every commodity falls past its target level along the path. -/
theorem avoidingPath_coordinate_bounds :
    (∀ j, PathMiddle.val j < (AvoidingPath ⟨0, by norm_num⟩).val j) ∧
    (∀ j, (AvoidingPath ⟨1, by norm_num⟩).val j < PathMiddle.val j) := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [PathMiddle, PairBundle, AvoidingPath]

/-- Yet no path point is indifferent to the target. -/
theorem avoidingPath_no_indifference :
    ¬∃ t, Indifferent (UtilityPref NetUtility) (AvoidingPath t) PathMiddle := by
  rintro ⟨t, ht⟩
  norm_num [Indifferent, UtilityPref, NetUtility, AvoidingPath, PathMiddle, PairBundle] at ht

/-- **Problem 2.7:** the counterexample also satisfies local insatiability. -/
theorem problem_2_7 :
    Rational (UtilityPref NetUtility) ∧ ContinuousPreference (UtilityPref NetUtility) ∧
    LocallyInsatiable (UtilityPref NetUtility) ∧ Continuous AvoidingPath ∧
    (∀ j, PathMiddle.val j < (AvoidingPath ⟨0, by norm_num⟩).val j) ∧
    (∀ j, (AvoidingPath ⟨1, by norm_num⟩).val j < PathMiddle.val j) ∧
    ¬∃ t, Indifferent (UtilityPref NetUtility) (AvoidingPath t) PathMiddle :=
  ⟨proposition_1_3a _, continuousPreference_of_continuous_utility netUtility_continuous,
    netPreference_locallyInsatiable, avoidingPath_continuous, avoidingPath_coordinate_bounds.1,
    avoidingPath_coordinate_bounds.2, avoidingPath_no_indifference⟩

/-- The failed hypothesis is monotonicity, as the path-crossing theorem also shows. -/
theorem netPreference_not_monotone : ¬MonotonePreference (UtilityPref NetUtility) := by
  intro hm
  apply avoidingPath_no_indifference
  exact monotone_path_crossing (proposition_1_3a _)
    (continuousPreference_of_continuous_utility netUtility_continuous) hm
    AvoidingPath avoidingPath_continuous PathMiddle
    (fun j => (avoidingPath_coordinate_bounds.1 j).le)
    (fun j => (avoidingPath_coordinate_bounds.2 j).le)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Countable dense ranks for the general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. The general proof here uses Cantor's
isomorphism theorem on the interior ranks of a countable dense subset. It handles
attained and unattained extrema without assuming monotonicity. Problem 2.14's
particular recursive assignment is a separate source-map obligation.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- Every strict numerical gap contains a rank from the chosen subset. -/
def StrictRankSeparator (v : X → ℝ) (D : Set X) : Prop :=
  ∀ x y, v x < v y → ∃ d ∈ D, v x < v d ∧ v d < v y

/-- A dense subset strictly separates represented continuous preferences on a connected space. -/
theorem dense_strictRankSeparator [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) {D : Set X} (hD : Dense D) : StrictRankSeparator v D := by
  intro x y hxy
  obtain ⟨z, hyz, hzx⟩ := exists_strict_between hr hc
    ((strict_iff_utility_lt hv y x).mpr hxy)
  have ho := continuousPreference_openStrictContours hc
  obtain ⟨d, hd, hdx, hyd⟩ := hD.exists_mem_open ((ho x).1.inter (ho y).2) ⟨z, hzx, hyz⟩
  exact ⟨d, hd, (strict_iff_utility_lt hv d x).mp hdx,
    (strict_iff_utility_lt hv y d).mp hyd⟩

/-- Remove any globally best and worst ranks from the chosen countable set. -/
def InteriorRankSet (v : X → ℝ) (D : Set X) : Set ℝ :=
  {a | a ∈ v '' D ∧ (∃ x, v x < a) ∧ ∃ y, a < v y}

/-- Every interior rank is the utility of an actual bundle. -/
theorem interiorRank_witness {v : X → ℝ} {D : Set X} (a : InteriorRankSet v D) :
    ∃ x, v x = a.val := by
  obtain ⟨x, _, hx⟩ := a.property.1
  exact ⟨x, hx⟩

/-- Every strict comparison brackets an interior rank, including near global endpoints. -/
theorem interiorRank_between {v : X → ℝ} {D : Set X} (hs : StrictRankSeparator v D)
    {x y : X} (hxy : v x < v y) :
    ∃ a : InteriorRankSet v D, v x < a.val ∧ a.val < v y := by
  obtain ⟨d, hd, hxd, hdy⟩ := hs x y hxy
  exact ⟨⟨v d, ⟨d, hd, rfl⟩, ⟨x, hxd⟩, ⟨y, hdy⟩⟩, hxd, hdy⟩

/-- The rank set remains countable after excluding endpoints. -/
theorem interiorRankSet_countable {v : X → ℝ} {D : Set X} (hD : D.Countable) :
    (InteriorRankSet v D).Countable :=
  (hD.image v).mono (fun _ h => h.1)

/-- The bounded rational scale used to fill every numerical gap. -/
abbrev RationalUnit : Type := Set.Ioo (0 : ℚ) 1

/-- A nonconstant preference's interior countable ranks have exactly the order type of (0,1) ∩ ℚ. -/
theorem interiorRanks_orderIso {v : X → ℝ} {D : Set X} (hD : D.Countable)
    (hs : StrictRankSeparator v D) (hn : ∃ x y, v x < v y) :
    Nonempty (InteriorRankSet v D ≃o RationalUnit) := by
  let A : Type := InteriorRankSet v D
  let : Countable A := (interiorRankSet_countable hD).to_subtype
  let : Nonempty A := by
    obtain ⟨x, y, hxy⟩ := hn
    obtain ⟨a, _⟩ := interiorRank_between hs hxy
    exact ⟨a⟩
  let : DenselyOrdered A := ⟨by
    intro a b hab
    obtain ⟨x, hx⟩ := interiorRank_witness a
    obtain ⟨y, hy⟩ := interiorRank_witness b
    have hxy : v x < v y := by rw [hx, hy]; exact hab
    obtain ⟨c, hxc, hcy⟩ := interiorRank_between hs hxy
    rw [hx] at hxc
    rw [hy] at hcy
    exact ⟨c, hxc, hcy⟩⟩
  let : NoMinOrder A := ⟨by
    intro a
    obtain ⟨x, hxa⟩ := a.property.2.1
    obtain ⟨y, hy⟩ := interiorRank_witness a
    obtain ⟨b, _, hby⟩ := interiorRank_between hs (hy.symm ▸ hxa)
    rw [hy] at hby
    exact ⟨b, hby⟩⟩
  let : NoMaxOrder A := ⟨by
    intro a
    obtain ⟨y, hay⟩ := a.property.2.2
    obtain ⟨x, hx⟩ := interiorRank_witness a
    obtain ⟨b, hxb, _⟩ := interiorRank_between hs (hx.symm ▸ hay)
    rw [hx] at hxb
    exact ⟨b, hxb⟩⟩
  let : Nonempty RationalUnit := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
  exact Order.iso_of_countable_dense A RationalUnit

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strong separability and additive utility

Kreps I, Definition 2.13 and the additive-to-strong direction of Proposition 2.14,
p. 42. Strong separability applies to every union of blocks, and nontriviality
does not depend on the other goods. The converse existence theorem with three
nontrivial blocks is proved in `PrimitiveAdditiveExistence`, with the original
commodity-partition specialization in `CommodityPartitionAdditiveExistence`.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*}

/-- **Definition 2.13:** comparisons on every union of blocks ignore its complement. -/
def StronglySeparable [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∀ (S : Finset I) a b z t, r (S.piecewise a z) (S.piecewise b z) ↔
    r (S.piecewise a t) (S.piecewise b t)

/-- A block is nontrivial when some two of its bundles can be strictly ranked. -/
def NontrivialBlock [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) (i : I) : Prop :=
  ∃ a b z, Strict r (Function.update z i a) (Function.update z i b)

/-- The substantive three-block hypothesis in **Proposition 2.14**. -/
def ThreeNontrivialBlocks [DecidableEq I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∃ i j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
    NontrivialBlock r i ∧ NontrivialBlock r j ∧ NontrivialBlock r l

/-- Strong separability includes each individual block's weak separability. -/
theorem stronglySeparable_weakly [DecidableEq I]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hs : StronglySeparable r) :
    WeaklySeparable (fun x y : BlockBundle B Unit => r x.1 y.1) := by
  intro i a b z t
  simpa [ReplaceBlock, Finset.piecewise_singleton] using
    hs {i} (Function.update z.1 i a) (Function.update z.1 i b) z.1 t.1

/-- The same pair witnesses block nontriviality under every surrounding bundle. -/
theorem nontrivialBlock_iff_every_context [DecidableEq I] [Nonempty (∀ i, B i)]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hs : StronglySeparable r) (i : I) :
    NontrivialBlock r i ↔
      ∃ a b, ∀ z, Strict r (Function.update z i a) (Function.update z i b) := by
  constructor
  · rintro ⟨a, b, z₀, hz⟩
    refine ⟨a, b, fun z => ?_⟩
    exact (weaklySeparable_strict (stronglySeparable_weakly hs) i a b (z₀, ()) (z, ())).mp hz
  · rintro ⟨a, b, hz⟩
    obtain ⟨z₀⟩ := ‹Nonempty (∀ i, B i)›
    exact ⟨a, b, z₀, hz z₀⟩

/-- Three distinct nontrivial blocks require at least three block indices. -/
theorem threeNontrivialBlocks_card [DecidableEq I] [Fintype I]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (h : ThreeNontrivialBlocks r) :
    3 ≤ Fintype.card I := by
  obtain ⟨i, j, l, hij, hil, hjl, _⟩ := h
  have hc : ({i, j, l} : Finset I).card = 3 := by simp [hij, hil, hjl]
  calc
    3 = ({i, j, l} : Finset I).card := hc.symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card I := Finset.card_univ

/-- Additive utility sums the individual block subutilities. -/
def AdditiveUtility [Fintype I] (w : ∀ i, B i → ℝ) (x : ∀ i, B i) : ℝ :=
  ∑ i, w i (x i)

/-- A preference admits an additive representation over the specified blocks. -/
def AdditivelyRepresentable [Fintype I] (r : (∀ i, B i) → (∀ i, B i) → Prop) : Prop :=
  ∃ w : ∀ i, B i → ℝ, Represents (AdditiveUtility w) r

/-- A union's utility contribution separates from the unchanged complementary blocks. -/
theorem additiveUtility_piecewise [Fintype I] [DecidableEq I]
    (w : ∀ i, B i → ℝ) (S : Finset I) (a z : ∀ i, B i) :
    AdditiveUtility w (S.piecewise a z) =
      (∑ i ∈ S, w i (a i)) + ∑ i ∈ Sᶜ, w i (z i) := by
  unfold AdditiveUtility
  rw [← Finset.sum_add_sum_compl S]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.piecewise_eq_of_mem _ _ _ hi]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp hi)]

/-- **Proposition 2.14**, converse: every additive representation is strongly separable. -/
theorem proposition_2_14_additive [Fintype I] [DecidableEq I]
    {w : ∀ i, B i → ℝ} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hu : Represents (AdditiveUtility w) r) : StronglySeparable r := by
  intro S a b z t
  rw [hu, hu]
  simp only [additiveUtility_piecewise, add_le_add_iff_right]

/-- Summing continuous subutilities gives a continuous utility on the product domain. -/
theorem additiveUtility_continuous [Fintype I] [∀ i, TopologicalSpace (B i)]
    {w : ∀ i, B i → ℝ} (hw : ∀ i, Continuous (w i)) : Continuous (AdditiveUtility w) :=
  continuous_finsetSum Finset.univ (fun i _ => (hw i).comp (continuous_apply i))

/-- Continuous additive subutilities therefore also give continuous preferences. -/
theorem continuousPreference_of_additive [Fintype I] [∀ i, TopologicalSpace (B i)]
    {w : ∀ i, B i → ℝ} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hu : Represents (AdditiveUtility w) r) (hw : ∀ i, Continuous (w i)) :
    ContinuousPreference r :=
  proposition_2_9_forward hu (additiveUtility_continuous hw)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Extending utility from a curve that meets every indifference class

Kreps I, Problem 2.14c, p. 48. A continuous representation on a connected curve
extends to the whole domain by indifference. The extension has exactly the same
range; its continuity follows from open strict contours and an interval-valued
range. These results also support the homogeneous representation in Proposition 2.19.
-/

namespace Kreps.PreferenceProperties

variable {X Y : Type*} {r : X → X → Prop}

/-- Give each bundle the value of a selected indifferent point on the reference curve. -/
noncomputable def LiftedUtility (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x) (x : X) : ℝ :=
  v (Classical.choose (hcover x))

/-- The chosen indifferent points preserve every original preference comparison. -/
theorem liftedUtility_represents (hr : Rational r) (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) :
    Represents (LiftedUtility f v hcover) r := by
  intro x y
  have hx := Classical.choose_spec (hcover x)
  have hy := Classical.choose_spec (hcover y)
  constructor
  · intro hxy
    exact (hv _ _).mp (hr.2 _ x _ hx.1 (hr.2 x y _ hxy hy.2))
  · intro hxy
    have h := (hv _ _).mpr hxy
    exact hr.2 x _ y hx.2 (hr.2 _ _ y h hy.1)

/-- The extension agrees with the specified values on the reference curve. -/
theorem liftedUtility_agrees (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (y : Y) :
    LiftedUtility f v hcover (f y) = v y := by
  have h := Classical.choose_spec (hcover (f y))
  exact le_antisymm ((hv _ _).mp h.2) ((hv _ _).mp h.1)

/-- Extending by indifference adds no utility values and loses none. -/
theorem liftedUtility_range (f : Y → X) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) :
    Set.range (LiftedUtility f v hcover) = Set.range v := by
  apply Set.Subset.antisymm
  · rintro a ⟨x, hx⟩
    exact ⟨Classical.choose (hcover x), hx⟩
  · rintro a ⟨y, hy⟩
    exact ⟨f y, (liftedUtility_agrees f v hcover hv y).trans hy⟩

/-- An interval-valued representation of a continuous preference must itself be continuous. -/
theorem continuous_of_ordConnected_range [TopologicalSpace X] {u : X → ℝ}
    (hu : Represents u r) (hc : ContinuousPreference r)
    (hRange : Set.OrdConnected (Set.range u)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  by_cases ha : a ∈ Set.range u
  · obtain ⟨z, hz⟩ := ha
    have hgt : u ⁻¹' Set.Ioi a = StrictlyBetterThan r z := by
      ext x
      change a < u x ↔ Strict r x z
      rw [strict_iff_utility_lt hu, hz]
    have hlt : u ⁻¹' Set.Iio a = StrictlyWorseThan r z := by
      ext x
      change u x < a ↔ Strict r z x
      rw [strict_iff_utility_lt hu, hz]
    exact ⟨hgt ▸ (ho z).1, hlt ▸ (ho z).2⟩
  · constructor
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change a < u x at hx
      have hall (y : X) : a < u y := by
        by_contra hy
        exact ha (hRange.out ⟨y, rfl⟩ ⟨x, rfl⟩ ⟨le_of_not_gt hy, hx.le⟩)
      exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · apply isOpen_iff_mem_nhds.mpr
      intro x hx
      change u x < a at hx
      have hall (y : X) : u y < a := by
        by_contra hy
        exact ha (hRange.out ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨hx.le, le_of_not_gt hy⟩)
      exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)

/-- A continuous representation on a connected reference domain extends continuously. -/
theorem liftedUtility_continuous [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace Y] (hr : Rational r) (hc : ContinuousPreference r)
    (f : Y → X) (v : Y → ℝ) (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (hvc : Continuous v) :
    Continuous (LiftedUtility f v hcover) := by
  apply continuous_of_ordConnected_range (liftedUtility_represents hr f v hcover hv) hc
  rw [liftedUtility_range f v hcover hv]
  exact (isPreconnected_range hvc).ordConnected

/-- **Problem 2.14c:** extend the curve's continuous representation to the entire orthant. -/
theorem problem_2_14c {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (Z : Set (NonnegativeOrthant k)) (hZ : IsPreconnected Z)
    (v : Z → ℝ) (hv : Represents v (fun a b => r a.val b.val)) (hvc : Continuous v)
    (hcover : ∀ x, ∃ z : Z, Indifferent r z.val x) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧
      ∀ z : Z, u z.val = v z := by
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp hZ
  exact ⟨LiftedUtility Subtype.val v hcover,
    liftedUtility_represents hr Subtype.val v hcover hv,
    liftedUtility_continuous hr hc Subtype.val v hcover hv hvc,
    liftedUtility_agrees Subtype.val v hcover hv⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Product utility on the two-good orthant

Elementary mixture inequalities used in the exact counterexamples of Kreps I,
Problem 2.8. The domain includes its axes; no interior-only assumption is hidden
in the weak quasi-concavity result.
-/

namespace Kreps.PreferenceProperties

/-- The product of the two nonnegative commodity quantities. -/
def TwoGoodProduct (x : NonnegativeOrthant 2) : ℝ := x.val 0 * x.val 1

/-- Along oppositely ordered coordinates the product exceeds its chord. -/
theorem product_mix_ge_average_of_cross (x₀ x₁ y₀ y₁ a : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hcross : (x₀ - y₀) * (x₁ - y₁) ≤ 0) :
    a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) ≤
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have ht : 0 ≤ a * (1 - a) := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have hneg := mul_nonpos_of_nonneg_of_nonpos ht hcross
  nlinarith

/-- Nonnegative two-coordinate products are quasi-concave under convex mixing. -/
theorem product_mix_ge_min (x₀ x₁ y₀ y₁ a : ℝ)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (ha : a ∈ Set.Icc 0 1) :
    min (x₀ * x₁) (y₀ * y₁) ≤
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
  have hmean : min (x₀ * x₁) (y₀ * y₁) ≤
      a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) := by
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (min_le_left (x₀ * x₁) (y₀ * y₁))),
      mul_nonneg hb (sub_nonneg.mpr (min_le_right (x₀ * x₁) (y₀ * y₁)))]
  by_cases h₀ : x₀ ≤ y₀
  · by_cases h₁ : x₁ ≤ y₁
    · apply (min_le_left _ _).trans
      exact mul_le_mul
        (show x₀ ≤ a * x₀ + (1 - a) * y₀ by
          nlinarith [mul_nonneg hb (sub_nonneg.mpr h₀)])
        (show x₁ ≤ a * x₁ + (1 - a) * y₁ by
          nlinarith [mul_nonneg hb (sub_nonneg.mpr h₁)]) hx₁
        (add_nonneg (mul_nonneg ha.1 hx₀) (mul_nonneg hb hy₀))
    · apply hmean.trans (product_mix_ge_average_of_cross x₀ x₁ y₀ y₁ a ha _)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h₀)
        (sub_nonneg.mpr (le_of_not_ge h₁))
  · by_cases h₁ : y₁ ≤ x₁
    · apply (min_le_right _ _).trans
      exact mul_le_mul
        (show y₀ ≤ a * x₀ + (1 - a) * y₀ by
          nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (le_of_not_ge h₀))])
        (show y₁ ≤ a * x₁ + (1 - a) * y₁ by
          nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr h₁)]) hy₁
        (add_nonneg (mul_nonneg ha.1 hx₀) (mul_nonneg hb hy₀))
    · apply hmean.trans (product_mix_ge_average_of_cross x₀ x₁ y₀ y₁ a ha _)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_not_ge h₀))
        (sub_nonpos.mpr (le_of_not_ge h₁))

/-- Product utility is continuous on the entire nonnegative orthant. -/
theorem twoGoodProduct_continuous : Continuous TwoGoodProduct :=
  ((continuous_apply 0).comp continuous_subtype_val).mul
    ((continuous_apply 1).comp continuous_subtype_val)

/-- Quasi-concavity includes zero-product boundary bundles. -/
theorem twoGoodProduct_quasiConcave :
    QuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) TwoGoodProduct := by
  intro x y a ha
  exact product_mix_ge_min (x.val 0) (x.val 1) (y.val 0) (y.val 1) a
    (x.property 0) (x.property 1) (y.property 0) (y.property 1) ha

/-- Strictly oppositely ordered coordinates give a strict chord inequality. -/
theorem product_mix_gt_average_of_cross (x₀ x₁ y₀ y₁ a : ℝ)
    (ha : a ∈ Set.Ioo 0 1) (hcross : (x₀ - y₀) * (x₁ - y₁) < 0) :
    a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) <
      (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have ht : 0 < a * (1 - a) := mul_pos ha.1 (sub_pos.mpr ha.2)
  have hneg := mul_neg_of_pos_of_neg ht hcross
  nlinarith

/-- Distinct positive-product bundles improve strictly over the lower-product endpoint. -/
theorem product_mix_gt_lower (x₀ x₁ y₀ y₁ a : ℝ)
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 < y₀) (hy₁ : 0 < y₁)
    (hprod : y₀ * y₁ ≤ x₀ * x₁) (hne : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (ha : a ∈ Set.Ioo 0 1) :
    y₀ * y₁ < (a * x₀ + (1 - a) * y₀) * (a * x₁ + (1 - a) * y₁) := by
  have hmean : y₀ * y₁ ≤ a * (x₀ * x₁) + (1 - a) * (y₀ * y₁) := by
    nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr hprod)]
  rcases lt_trichotomy x₀ y₀ with h₀ | h₀ | h₀
  · have h₁ : y₁ < x₁ := by
      by_contra h
      have hle := mul_le_mul_of_nonneg_left (le_of_not_gt h) hx₀
      have hlt := mul_lt_mul_of_pos_right h₀ hy₁
      exact not_lt_of_ge hprod (hle.trans_lt hlt)
    exact hmean.trans_lt (product_mix_gt_average_of_cross x₀ x₁ y₀ y₁ a ha
      (mul_neg_of_neg_of_pos (sub_neg.mpr h₀) (sub_pos.mpr h₁)))
  · have hn₁ : x₁ ≠ y₁ := hne.resolve_left (not_ne_iff.mpr h₀)
    have h₁ : y₁ < x₁ := by
      rw [h₀] at hprod
      exact lt_of_le_of_ne ((mul_le_mul_iff_right₀ hy₀).mp hprod) (Ne.symm hn₁)
    have hm₀ : a * x₀ + (1 - a) * y₀ = y₀ := by rw [h₀]; ring
    have hm₁ : y₁ < a * x₁ + (1 - a) * y₁ := by
      nlinarith [mul_pos ha.1 (sub_pos.mpr h₁)]
    rw [hm₀]
    exact mul_lt_mul_of_pos_left hm₁ hy₀
  · by_cases h₁ : x₁ < y₁
    · exact hmean.trans_lt (product_mix_gt_average_of_cross x₀ x₁ y₀ y₁ a ha
        (mul_neg_of_pos_of_neg (sub_pos.mpr h₀) (sub_neg.mpr h₁)))
    · have hm₀ : y₀ < a * x₀ + (1 - a) * y₀ := by
        nlinarith [mul_pos ha.1 (sub_pos.mpr h₀)]
      have hm₁ : y₁ ≤ a * x₁ + (1 - a) * y₁ := by
        nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr (le_of_not_gt h₁))]
      exact (mul_lt_mul_of_pos_right hm₀ hy₁).trans_le
        (mul_le_mul_of_nonneg_left hm₁ (hy₀.trans hm₀).le)

/-- Positive product is equivalent to positive quantities on the nonnegative orthant. -/
theorem twoGoodProduct_pos_iff (x : NonnegativeOrthant 2) :
    0 < TwoGoodProduct x ↔ 0 < x.val 0 ∧ 0 < x.val 1 := by
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hp | hn
    · exact hp
    · exact False.elim (not_lt_of_ge (x.property 0) hn.1)
  · rintro ⟨h₀, h₁⟩
    exact mul_pos h₀ h₁

/-- At positive rank, distinct weakly better bundles yield a strict product improvement. -/
theorem twoGoodProduct_mix_strict {x y : NonnegativeOrthant 2}
    (hy : 0 < TwoGoodProduct y) (hxy : TwoGoodProduct y ≤ TwoGoodProduct x) (hne : x ≠ y)
    {a : ℝ} (ha : a ∈ Set.Ioo 0 1) :
    TwoGoodProduct y < TwoGoodProduct
      (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ⟨ha.1.le, ha.2.le⟩) := by
  have hcoords : x.val 0 ≠ y.val 0 ∨ x.val 1 ≠ y.val 1 := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  have hyp := (twoGoodProduct_pos_iff y).mp hy
  exact product_mix_gt_lower (x.val 0) (x.val 1) (y.val 0) (y.val 1) a
    (x.property 0) hyp.1 hyp.2 hxy hcoords ha

/-- An interior mixture with a positive-product endpoint has positive product. -/
theorem twoGoodProduct_mix_pos {x y : NonnegativeOrthant 2}
    (hx : 0 < TwoGoodProduct x) {a : ℝ} (ha : a ∈ Set.Ioo 0 1) :
    0 < TwoGoodProduct (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ⟨ha.1.le, ha.2.le⟩) := by
  have hxp := (twoGoodProduct_pos_iff x).mp hx
  apply mul_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos ha.1 hxp.1)
      (mul_nonneg (sub_pos.mpr ha.2).le (y.property 0))
  · exact add_pos_of_pos_of_nonneg (mul_pos ha.1 hxp.2)
      (mul_nonneg (sub_pos.mpr ha.2).le (y.property 1))

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 3: concave and convex functions

Kreps I, Definition A3.16, Proposition A3.17 and Proposition A3.23, pp. 461–466.
The weighted affine-composition statements explicitly require the affine arguments
to remain in the original domain. This makes the book's implicit domain convention
precise. Continuity is asserted on the interior, as in the text.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {S : Set E} {T : Set F} {f : E → ℝ}

/-- **Proposition A3.17a:** an affine function is convex and concave. -/
theorem proposition_A3_17a (hS : Convex ℝ S) (g : E →ᵃ[ℝ] ℝ) :
    ConvexOn ℝ S g ∧ ConcaveOn ℝ S g := by
  constructor
  · exact ⟨hS, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).le⟩
  · exact ⟨hS, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).ge⟩

/-- **Proposition A3.17b:** the pointwise minimum of a finite nonempty family is concave. -/
theorem proposition_A3_17b_min (t : Finset ι) (ht : t.Nonempty) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConcaveOn ℝ S (g i)) : ConcaveOn ℝ S (t.inf' ht g) :=
  Finset.inf'_induction ht g (fun _ hf _ hh => hf.inf hh) hg

/-- **Proposition A3.17c:** the pointwise maximum of a finite nonempty family is convex. -/
theorem proposition_A3_17c_max (t : Finset ι) (ht : t.Nonempty) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConvexOn ℝ S (g i)) : ConvexOn ℝ S (t.sup' ht g) :=
  Finset.sup'_induction ht g (fun _ hf _ hh => hf.sup hh) hg

/-- Finite sums of concave functions are concave, including the empty sum. -/
theorem concaveOn_finite_sum (hS : Convex ℝ S) (t : Finset ι) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConcaveOn ℝ S (g i)) : ConcaveOn ℝ S (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using concaveOn_const (0 : ℝ) hS
  | @insert i t hi ih =>
      have hgi := hg i (Finset.mem_insert_self i t)
      have hgt := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      convert hgi.add hgt using 1
      ext x
      exact Finset.sum_insert hi

/-- Finite sums of convex functions are convex, including the empty sum. -/
theorem convexOn_finite_sum (hS : Convex ℝ S) (t : Finset ι) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConvexOn ℝ S (g i)) : ConvexOn ℝ S (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using convexOn_const (0 : ℝ) hS
  | @insert i t hi ih =>
      have hgi := hg i (Finset.mem_insert_self i t)
      have hgt := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      convert hgi.add hgt using 1
      ext x
      exact Finset.sum_insert hi

/-- **Proposition A3.17b:** nonnegative weighted sums after affine changes of argument. -/
theorem proposition_A3_17b_sum (hS : Convex ℝ S) (t : Finset ι) (w : ι → ℝ)
    (g : ι → F → ℝ) (A : ι → E →ᵃ[ℝ] F) (hw : ∀ i ∈ t, 0 ≤ w i)
    (hg : ∀ i ∈ t, ConcaveOn ℝ T (g i)) (hA : ∀ i ∈ t, Set.MapsTo (A i) S T) :
    ConcaveOn ℝ S (fun x => ∑ i ∈ t, w i * g i (A i x)) := by
  apply concaveOn_finite_sum hS t
  intro i hi
  exact (((hg i hi).comp_affineMap (A i)).subset (hA i hi) hS).smul (hw i hi)

/-- **Proposition A3.17c:** the corresponding convex weighted affine-composition rule. -/
theorem proposition_A3_17c_sum (hS : Convex ℝ S) (t : Finset ι) (w : ι → ℝ)
    (g : ι → F → ℝ) (A : ι → E →ᵃ[ℝ] F) (hw : ∀ i ∈ t, 0 ≤ w i)
    (hg : ∀ i ∈ t, ConvexOn ℝ T (g i)) (hA : ∀ i ∈ t, Set.MapsTo (A i) S T) :
    ConvexOn ℝ S (fun x => ∑ i ∈ t, w i * g i (A i x)) := by
  apply convexOn_finite_sum hS t
  intro i hi
  exact (((hg i hi).comp_affineMap (A i)).subset (hA i hi) hS).smul (hw i hi)

/-- **Proposition A3.17d:** upper contour sets of a concave function are convex. -/
theorem proposition_A3_17d (hf : ConcaveOn ℝ S f) (r : ℝ) :
    Convex ℝ {x ∈ S | r ≤ f x} := hf.convex_ge r

/-- **Proposition A3.17e:** lower contour sets of a convex function are convex. -/
theorem proposition_A3_17e (hf : ConvexOn ℝ S f) (r : ℝ) :
    Convex ℝ {x ∈ S | f x ≤ r} := hf.convex_le r

/-- **Proposition A3.17f:** concavity is convexity of the negative. -/
theorem proposition_A3_17f : ConcaveOn ℝ S f ↔ ConvexOn ℝ S (-f) :=
  neg_convexOn_iff.symm

/-- **Proposition A3.23:** concavity is equivalent to convexity of the hypograph. -/
theorem proposition_A3_23 : ConcaveOn ℝ S f ↔
    Convex ℝ {p : E × ℝ | p.1 ∈ S ∧ p.2 ≤ f p.1} := concaveOn_iff_convex_hypograph

/-- The epigraph version mentioned following Proposition A3.25. -/
theorem convexOn_iff_convex_epigraph_appendix : ConvexOn ℝ S f ↔
    Convex ℝ {p : E × ℝ | p.1 ∈ S ∧ f p.1 ≤ p.2} := convexOn_iff_convex_epigraph

/-- **Proposition A3.17g:** finite-dimensional concavity implies continuity on the interior. -/
theorem proposition_A3_17g_concave {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D : Set G} {g : G → ℝ} (hg : ConcaveOn ℝ D g) :
    ContinuousOn g (interior D) := hg.continuousOn_interior

/-- **Proposition A3.17g:** the corresponding continuity statement for convex functions. -/
theorem proposition_A3_17g_convex {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D : Set G} {g : G → ℝ} (hg : ConvexOn ℝ D g) :
    ContinuousOn g (interior D) := hg.continuousOn_interior

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix 3: quasi-concavity and maximizers

Kreps I, Definition A3.18 and Propositions A3.19–A3.22, pp. 464–465.
The utility definitions are shared with Chapter 2. Maximizers are expressed using
universal comparisons, which handles empty sets and unbounded utilities without
assigning a real-valued supremum to an unbounded set.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition A3.18d:** a mixture does not exceed the larger endpoint utility. -/
def QuasiConvexUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, u (Mix hS x y a ha) ≤ max (u x) (u y)

/-- **Definition A3.18e:** distinct ordered endpoints give a strict decrease. -/
def StrictlyQuasiConvexUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) < u x

/-- **Proposition A3.19:** quasi-concavity is convexity of every upper contour. -/
theorem proposition_A3_19 (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConcaveUtility hS (fun x => f x.val) ↔ ∀ r, Convex ℝ {x ∈ S | r ≤ f x} :=
  quasiConcaveUtility_iff_quasiconcaveOn hS f

/-- **Proposition A3.19**, footnote: quasi-convexity is convexity of every lower contour. -/
theorem proposition_A3_19_quasiConvex (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConvexUtility hS (fun x => f x.val) ↔ ∀ r, Convex ℝ {x ∈ S | f x ≤ r} := by
  change QuasiConvexUtility hS (fun x => f x.val) ↔ QuasiconvexOn ℝ S f
  rw [quasiconvexOn_iff_le_max]
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- **Proposition A3.20:** every nondecreasing transformation preserves quasi-concavity. -/
theorem proposition_A3_20 {hS : Convex ℝ S} {u : S → ℝ} {g : ℝ → ℝ}
    (hu : QuasiConcaveUtility hS u) (hg : Monotone g) :
    QuasiConcaveUtility hS (g ∘ u) := by
  intro x y a ha
  change min (g (u x)) (g (u y)) ≤ g (u (Mix hS x y a ha))
  rw [← hg.map_min]
  exact hg (hu x y a ha)

/-- **Proposition A3.20:** strictly increasing transformations preserve strict quasi-concavity. -/
theorem proposition_A3_20_strict {hS : Convex ℝ S} {u : S → ℝ} {g : ℝ → ℝ}
    (hu : StrictlyQuasiConcaveUtility hS u) (hg : StrictMono g) :
    StrictlyQuasiConcaveUtility hS (g ∘ u) := by
  intro x y hne hyx a ha
  exact hg (hu x y hne (hg.le_iff_le.mp hyx) a ha)

/-- **Proposition A3.21:** the maximizers on a convex menu form a convex set. -/
theorem proposition_A3_21 {hS : Convex ℝ S} {u : S → ℝ}
    (hu : QuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    ConvexMenu hS (UtilityChoice u A) := by
  intro x hx y hy a ha
  refine ⟨hA x hx.1 y hy.1 a ha, fun z hz => ?_⟩
  exact (le_min (hx.2 z hz) (hy.2 z hz)).trans (hu x y a ha)

/-- **Proposition A3.21:** strict quasi-concavity gives at most one maximizer. -/
theorem proposition_A3_21_unique {hS : Convex ℝ S} {u : S → ℝ}
    (hu : StrictlyQuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    (UtilityChoice u A).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := hu x y hne (hx.2 y hy.1) (1 / 2) (by constructor <;> norm_num)
  exact (not_lt_of_ge (hy.2 _
    (hA x hx.1 y hy.1 (1 / 2) (by constructor <;> norm_num)))) hm

/-- The maximizer convexity assertion in the ambient-vector-space formulation. -/
theorem proposition_A3_21_ambient {hS : Convex ℝ S} {u : S → ℝ}
    (hu : QuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    Convex ℝ (Subtype.val '' UtilityChoice u A) :=
  (convexMenu_iff hS _).mp (proposition_A3_21 hu hA)

/-- **Proposition A3.22:** concavity implies semi-strict quasi-concavity. -/
theorem proposition_A3_22_concave {hS : Convex ℝ S} {u : S → ℝ}
    (hu : ConcaveUtility hS u) : SemiStrictlyQuasiConcaveUtility hS u :=
  concaveUtility_semiStrict hu

/-- **Proposition A3.22:** strict concavity implies strict quasi-concavity. -/
theorem proposition_A3_22_strict {hS : Convex ℝ S} {u : S → ℝ}
    (hu : StrictlyConcaveUtility hS u) : StrictlyQuasiConcaveUtility hS u :=
  strictlyConcaveUtility_strictQuasi hu

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Calibrating overlapping additive charts

Preparation for Kreps I, Proposition 2.14. The affine uniqueness theorem is
transported from numerical score intervals back to arbitrary connected ordered
coordinate domains. Fixing one nonzero increment in a companion coordinate
then forces overlap transitions to be translations, synchronizing the units
of the two coordinate scales.
-/

namespace Kreps.PreferenceProperties

/-- Two strictly increasing coordinate scales represent the same coordinate order. -/
theorem strictMono_coordinate_represents {A : Type*} [LinearOrder A]
    {w v : A → ℝ} (hw : StrictMono w) (hv : StrictMono v) :
    Represents v (UtilityPref w) := by
  intro x y
  exact hw.le_iff_le.trans hv.le_iff_le.symm

/-- Equivalent additive charts on two connected ordered blocks have one positive affine slope. -/
theorem pair_chart_positive_affine_unique {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d) :
    ∃ slope β γ : ℝ, 0 < slope ∧ (∀ x, v x = slope * w x + β) ∧
      ∀ y, v' y = slope * w' y + γ := by
  have hwr : Represents w (UtilityPref w) := fun _ _ => Iff.rfl
  have hvr := strictMono_coordinate_represents hwm hvm
  have hwr' : Represents w' (UtilityPref w') := fun _ _ => Iff.rfl
  have hvr' := strictMono_coordinate_represents hwm' hvm'
  have hpc : PreservesPairSumEquality (UtilityTransform w v) (UtilityTransform w' v')
      (Set.range w) (Set.range w') := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ he
    simpa only [utilityTransform_apply hwr hvr, utilityTransform_apply hwr' hvr']
      using hp x x' y y' he
  have hfc : ContinuousOn (UtilityTransform w v) (Set.range w) :=
    continuousOn_iff_continuous_domRestrict.mpr (utilityTransform_continuous_range hwr hvr hw hv)
  have hgc : ContinuousOn (UtilityTransform w' v') (Set.range w') :=
    continuousOn_iff_continuous_domRestrict.mpr
      (utilityTransform_continuous_range hwr' hvr' hw' hv')
  obtain ⟨slope, β, γ, hslope, hf, hg⟩ := pair_additive_positive_affine_unique hpc
    (isPreconnected_range hw).ordConnected (isPreconnected_range hw').ordConnected hfc hgc
    (utilityTransform_strictMonoOn hwr hvr) ⟨a, rfl⟩ ⟨b, rfl⟩ (hwm hab)
    ⟨c, rfl⟩ ⟨d, rfl⟩ (hwm' hcd)
  refine ⟨slope, β, γ, hslope, fun x => ?_, fun y => ?_⟩
  · simpa only [utilityTransform_apply hwr hvr] using hf (w x) ⟨x, rfl⟩
  · simpa only [utilityTransform_apply hwr' hvr'] using hg (w' y) ⟨y, rfl⟩

/-- Equal companion increments force the common affine slope to be one. -/
theorem common_affine_slope_eq_one {A B : Type*} {w v : A → ℝ} {w' v' : B → ℝ}
    {slope β γ : ℝ} (hv : ∀ x, v x = slope * w x + β) (hv' : ∀ y, v' y = slope * w' y + γ)
    {c d : B} (hcd : w' c < w' d) (hunit : v' d - v' c = w' d - w' c) :
    slope = 1 ∧ (∀ x, v x = w x + β) ∧ ∀ y, v' y = w' y + γ := by
  have hc := hv' c
  have hd := hv' d
  have hslope : slope = 1 := by nlinarith
  exact ⟨hslope, fun x => by simpa only [hslope, one_mul] using hv x,
    fun y => by simpa only [hslope, one_mul] using hv' y⟩

/-- Calibrating one companion increment leaves only coordinate translations on an overlap. -/
theorem pair_chart_translation_of_companion_increment {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d)
    (hunit : v' d - v' c = w' d - w' c) :
    ∃ β γ : ℝ, (∀ x, v x = w x + β) ∧ ∀ y, v' y = w' y + γ := by
  obtain ⟨slope, β, γ, _, hf, hg⟩ := pair_chart_positive_affine_unique hw hv hw' hv'
    hwm hvm hwm' hvm' hp hab hcd
  have h := common_affine_slope_eq_one hf hg (hwm' hcd) hunit
  exact ⟨β, γ, h.2⟩

/-- Matching a companion at two levels fixes its offset too; one target baseline fixes the rest. -/
theorem pair_chart_identity_of_companion_and_baseline {A B : Type*}
    [LinearOrder A] [LinearOrder B] [TopologicalSpace A] [TopologicalSpace B]
    [PreconnectedSpace A] [PreconnectedSpace B]
    {w v : A → ℝ} {w' v' : B → ℝ}
    (hw : Continuous w) (hv : Continuous v) (hw' : Continuous w') (hv' : Continuous v')
    (hwm : StrictMono w) (hvm : StrictMono v) (hwm' : StrictMono w') (hvm' : StrictMono v')
    (hp : ∀ x x' y y', w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b : A} {c d : B} (hab : a < b) (hcd : c < d)
    (hc : v' c = w' c) (hd : v' d = w' d) (ha : v a = w a) :
    (∀ x, v x = w x) ∧ ∀ y, v' y = w' y := by
  obtain ⟨β, γ, hf, hg⟩ := pair_chart_translation_of_companion_increment hw hv hw' hv'
    hwm hvm hwm' hvm' hp hab hcd (by rw [hc, hd])
  have hβ : β = 0 := by have h := hf a; linarith
  have hγ : γ = 0 := by have h := hg c; linarith
  exact ⟨fun x => by simpa only [hβ, add_zero] using hf x,
    fun y => by simpa only [hγ, add_zero] using hg y⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Ordinal rescaling can destroy concavity or continuity

Kreps I, p. 35 and Problem 2.5a-b, p. 46. Identity on the one-good orthant is
concave and continuous. A piecewise linear increasing transformation destroys
concavity; the jump transformation from Chapter 1 destroys continuity.
-/

namespace Kreps.PreferenceProperties

/-- A strictly increasing transformation whose slope rises at one. -/
noncomputable def ConvexWarp (t : ℝ) : ℝ := if t ≤ 1 then t else 2 * t - 1

/-- Both slopes are positive and the two branches meet at the breakpoint. -/
theorem convexWarp_strictMono : StrictMono ConvexWarp := by
  intro x y hxy
  unfold ConvexWarp
  split_ifs <;> linarith

/-- Identity satisfies Jensen's inequality with equality. -/
theorem identityUtility_concave :
    ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => x.val) := by
  intro x y a ha
  exact le_rfl

/-- The transformed midpoint is strictly below the average transformed endpoint values. -/
theorem convexWarp_not_concave :
    ¬ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => ConvexWarp x.val) := by
  intro h
  have hm := h ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ (1 / 2) (by constructor <;> norm_num)
  norm_num [ConvexWarp, Mix, smul_eq_mul] at hm

/-- **Problem 2.5a:** concavity is not invariant under strictly increasing rescaling. -/
theorem problem_2_5a :
    ConcaveUtility (convex_Ici (0 : ℝ)) (fun x : OneGood => x.val) ∧
    StrictMono ConvexWarp ∧
    ¬ConcaveUtility (convex_Ici (0 : ℝ)) (ConvexWarp ∘ fun x : OneGood => x.val) :=
  ⟨identityUtility_concave, convexWarp_strictMono, convexWarp_not_concave⟩

/-- A jump at the interior point one prevents continuity on the half-line. -/
theorem jumpUtility_not_continuous :
    ¬Continuous (fun x : OneGood => JumpUtility x.val) := by
  intro h
  have hc : ContinuousAt (fun x : OneGood => JumpUtility x.val) ⟨1, by norm_num⟩ :=
    h.continuousAt
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  let x : OneGood := ⟨1 + δ / 2, show 0 ≤ 1 + δ / 2 from by positivity⟩
  have hx : dist x (⟨1, by norm_num⟩ : OneGood) < δ := by
    change dist (1 + δ / 2) (1 : ℝ) < δ
    rw [Real.dist_eq, show 1 + δ / 2 - 1 = δ / 2 by ring,
      abs_of_pos (by positivity)]
    linarith
  have hx1 : 1 < x.val := by change 1 < 1 + δ / 2; linarith
  have hj : JumpUtility x.val = x.val + 1 := by
    simp only [JumpUtility, ite_eq_right (not_le.mpr hx1)]
  have h1 : JumpUtility 1 = 1 := by norm_num [JumpUtility]
  have hbound := hb hx
  change dist (JumpUtility x.val) (JumpUtility 1) < 1 / 2 at hbound
  rw [hj, h1, Real.dist_eq, abs_of_pos (by linarith : 0 < x.val + 1 - 1)] at hbound
  linarith

/-- **Problem 2.5b:** continuity is not invariant under strictly increasing rescaling. -/
theorem problem_2_5b :
    Continuous (fun x : OneGood => x.val) ∧ StrictMono JumpUtility ∧
    ¬Continuous (JumpUtility ∘ fun x : OneGood => x.val) :=
  ⟨continuous_subtype_val, jumpUtility_strictMono, jumpUtility_not_continuous⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The diagonal continuous representation

Kreps I, Steps 3-5 of the construction on pp. 37-38. Each bundle has a unique
indifferent diagonal coordinate. That coordinate represents the preference and
is continuous. The continuity proof uses open strict contours and the exact
nonnegative range, including its zero endpoint. The extra monotonicity assumptions
remain explicit; this module does not claim the general converse of Proposition 2.9.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- Step 4: two indifferent diagonal representatives of a bundle have the same coordinate. -/
theorem diagonal_indifference_unique (hr : Rational r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) {x : NonnegativeOrthant k}
    {a b : Set.Ici (0 : ℝ)} (ha : Indifferent r (Diagonal a) x)
    (hb : Indifferent r (Diagonal b) x) : a = b := by
  apply (diagonal_indifferent_iff hm hs a b).mp
  exact ⟨hr.2 _ x _ ha.1 hb.2, hr.2 _ x _ hb.1 ha.2⟩

/-- The existence and uniqueness needed to define the diagonal utility. -/
theorem diagonal_indifference_existsUnique (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) (x : NonnegativeOrthant k) :
    ∃! a : Set.Ici (0 : ℝ), Indifferent r (Diagonal a) x := by
  obtain ⟨a, ha⟩ := diagonal_indifference_exists hk hr hc hm x
  exact ⟨a, ha, fun b hb => diagonal_indifference_unique hr hm hs hb ha⟩

/-- Select the diagonal coordinate; the uniqueness theorem makes it canonical under strictness. -/
noncomputable def DiagonalCoordinate (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (x : NonnegativeOrthant k) : Set.Ici (0 : ℝ) :=
  Classical.choose (diagonal_indifference_exists hk hr hc hm x)

/-- The selected coordinate has precisely the required indifference property. -/
theorem diagonalCoordinate_spec (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    Indifferent r (Diagonal (DiagonalCoordinate hk hr hc hm x)) x :=
  Classical.choose_spec (diagonal_indifference_exists hk hr hc hm x)

/-- Step 4's real-valued utility: the location of the indifferent diagonal bundle. -/
noncomputable def DiagonalUtility (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (x : NonnegativeOrthant k) : ℝ := (DiagonalCoordinate hk hr hc hm x).val

/-- The diagonal scale is nonnegative even when some goods have zero consumption. -/
theorem diagonalUtility_nonneg (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    0 ≤ DiagonalUtility hk hr hc hm x := (DiagonalCoordinate hk hr hc hm x).property

/-- Step 5's ordinal representation assertion. -/
theorem diagonalUtility_represents (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) : Represents (DiagonalUtility hk hr hc hm) r := by
  intro x y
  have hx := diagonalCoordinate_spec hk hr hc hm x
  have hy := diagonalCoordinate_spec hk hr hc hm y
  constructor
  · intro hxy
    have hdiag := hr.2 _ x _ hx.1 (hr.2 x y _ hxy hy.2)
    exact (diagonal_weak_iff hm hs _ _).mp hdiag
  · intro hxy
    have hdiag := (diagonal_weak_iff hm hs
      (DiagonalCoordinate hk hr hc hm x) (DiagonalCoordinate hk hr hc hm y)).mpr hxy
    exact hr.2 x _ y hx.2 (hr.2 _ _ y hdiag hy.1)

/-- On the diagonal itself, utility is exactly the common commodity quantity. -/
theorem diagonalUtility_diagonal (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) (a : Set.Ici (0 : ℝ)) :
    DiagonalUtility hk hr hc hm (Diagonal a) = a.val := by
  have he := (diagonal_indifferent_iff hm hs _ a).mp
    (diagonalCoordinate_spec hk hr hc hm (Diagonal a))
  exact congrArg Subtype.val he

/-- An exact nonnegative utility range converts continuous strict contours into continuity. -/
theorem continuous_of_full_nonnegative_range {X : Type*} [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r)
    (hc : ContinuousPreference r) (hn : ∀ x, 0 ≤ u x)
    (hfull : ∀ a : ℝ, 0 ≤ a → ∃ x, u x = a) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  by_cases ha : 0 ≤ a
  · obtain ⟨z, hz⟩ := hfull a ha
    have hgt : u ⁻¹' Set.Ioi a = StrictlyBetterThan r z := by
      ext x
      change a < u x ↔ Strict r x z
      rw [strict_iff_utility_lt hu, hz]
    have hlt : u ⁻¹' Set.Iio a = StrictlyWorseThan r z := by
      ext x
      change u x < a ↔ Strict r z x
      rw [strict_iff_utility_lt hu, hz]
    exact ⟨hgt ▸ (ho z).1, hlt ▸ (ho z).2⟩
  · have hgt : u ⁻¹' Set.Ioi a = Set.univ := by
      ext x
      change (a < u x) ↔ True
      exact iff_true_intro (lt_of_lt_of_le (lt_of_not_ge ha) (hn x))
    have hlt : u ⁻¹' Set.Iio a = ∅ := by
      ext x
      change (u x < a) ↔ False
      exact iff_false_intro (not_lt_of_ge ((le_of_lt (lt_of_not_ge ha)).trans (hn x)))
    exact ⟨hgt ▸ isOpen_univ, hlt ▸ isOpen_empty⟩

/-- Step 5's continuity assertion, including the zero endpoint of the diagonal. -/
theorem diagonalUtility_continuous (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) : Continuous (DiagonalUtility hk hr hc hm) := by
  apply continuous_of_full_nonnegative_range (diagonalUtility_represents hk hr hc hm hs) hc
    (diagonalUtility_nonneg hk hr hc hm)
  intro a ha
  exact ⟨Diagonal ⟨a, ha⟩, diagonalUtility_diagonal hk hr hc hm hs ⟨a, ha⟩⟩

/-- **Proposition 2.9 with the extra assumptions**, proved by all five diagonal steps. -/
theorem proposition_2_9_monotone (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  ⟨DiagonalUtility hk hr hc hm, diagonalUtility_represents hk hr hc hm hs,
    diagonalUtility_continuous hk hr hc hm hs⟩

/-- Footnote 6, p. 36: weak monotonicity follows from the other assumptions. -/
theorem continuous_representation_strictAllIncrease (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StrictAllIncreasePreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  proposition_2_9_monotone hk hr hc (continuous_strictAllIncrease_monotone hr hc hs) hs

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A bounded utility from dense rational ranks

The construction supporting the general Proposition 2.9 assigns each bundle
the supremum of its lower rational ranks. Adding zero makes every cut nonempty;
the rational scale lies in (0,1), so all cuts are bounded, even at extreme ranks.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} {v : X → ℝ} {D : Set X}

/-- A countable interior rank's rational value, viewed as a real number. -/
def RationalRankValue (e : InteriorRankSet v D ≃o RationalUnit)
    (a : InteriorRankSet v D) : ℝ := (e a).val

/-- All rational ranks are strictly between zero and one. -/
theorem rationalRankValue_bounds (e : InteriorRankSet v D ≃o RationalUnit)
    (a : InteriorRankSet v D) : 0 < RationalRankValue e a ∧ RationalRankValue e a < 1 := by
  have h := (e a).property
  change 0 < ((e a).val : ℝ) ∧ ((e a).val : ℝ) < 1
  exact_mod_cast h

/-- The real-valued rank scale preserves every strict comparison. -/
theorem rationalRankValue_strictMono (e : InteriorRankSet v D ≃o RationalUnit) :
    StrictMono (RationalRankValue e) := by
  intro a b hab
  have hq : (e a).val < (e b).val := e.strictMono hab
  change ((e a).val : ℝ) < ((e b).val : ℝ)
  exact_mod_cast hq

/-- A lower cut, with zero included to cover a possible worst bundle. -/
def RankCutSet (e : InteriorRankSet v D ≃o RationalUnit) (x : X) : Set ℝ :=
  {t | t = 0 ∨ ∃ a : InteriorRankSet v D, t = RationalRankValue e a ∧ a.val ≤ v x}

/-- Every lower cut contains zero. -/
theorem rankCutSet_nonempty (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    (RankCutSet e x).Nonempty := ⟨0, Or.inl rfl⟩

/-- One bounds every lower cut, whether or not a best bundle exists. -/
theorem rankCutSet_bddAbove (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    BddAbove (RankCutSet e x) := by
  refine ⟨1, ?_⟩
  intro t ht
  rcases ht with rfl | ⟨a, rfl, _⟩
  · exact zero_le_one
  · exact (rationalRankValue_bounds e a).2.le

/-- The supremum of the lower rational ranks is the new utility scale. -/
noncomputable def RankCutUtility (e : InteriorRankSet v D ≃o RationalUnit) (x : X) : ℝ :=
  sSup (RankCutSet e x)

/-- The completed scale never falls below zero. -/
theorem rankCutUtility_nonneg (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    0 ≤ RankCutUtility e x :=
  le_csSup (rankCutSet_bddAbove e x) (Or.inl rfl)

/-- The completed scale never exceeds one. -/
theorem rankCutUtility_le_one (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    RankCutUtility e x ≤ 1 := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  rcases ht with rfl | ⟨a, rfl, _⟩
  · exact zero_le_one
  · exact (rationalRankValue_bounds e a).2.le

/-- Larger original utility gives a larger lower cut. -/
theorem rankCutUtility_mono (e : InteriorRankSet v D ≃o RationalUnit) {x y : X}
    (hxy : v x ≤ v y) : RankCutUtility e x ≤ RankCutUtility e y := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  apply le_csSup (rankCutSet_bddAbove e y)
  rcases ht with h0 | ⟨a, ha, hax⟩
  · exact Or.inl h0
  · exact Or.inr ⟨a, ha, hax.trans hxy⟩

/-- An upper rational rank bounds the completed utility from above. -/
theorem rankCutUtility_upper (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : v x ≤ a.val) :
    RankCutUtility e x ≤ RationalRankValue e a := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  rcases ht with rfl | ⟨b, rfl, hbx⟩
  · exact (rationalRankValue_bounds e a).1.le
  · exact (rationalRankValue_strictMono e).monotone (hbx.trans hx)

/-- A lower rational rank bounds the completed utility from below. -/
theorem rankCutUtility_lower (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : a.val ≤ v x) :
    RationalRankValue e a ≤ RankCutUtility e x :=
  le_csSup (rankCutSet_bddAbove e x) (Or.inr ⟨a, rfl, hx⟩)

/-- The extension agrees exactly with every prescribed rational rank. -/
theorem rankCutUtility_at_rank (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : v x = a.val) :
    RankCutUtility e x = RationalRankValue e a :=
  le_antisymm (rankCutUtility_upper e hx.le) (rankCutUtility_lower e hx.ge)

/-- Two interior ranks between distinct preferences force a strict utility inequality. -/
theorem rankCutUtility_strict (e : InteriorRankSet v D ≃o RationalUnit)
    (hs : StrictRankSeparator v D) {x y : X} (hxy : v x < v y) :
    RankCutUtility e x < RankCutUtility e y := by
  obtain ⟨a, hxa, hay⟩ := interiorRank_between hs hxy
  obtain ⟨z, hz⟩ := interiorRank_witness a
  have hzy : v z < v y := by rw [hz]; exact hay
  obtain ⟨b, hzb, hby⟩ := interiorRank_between hs hzy
  have hab : a < b := by
    change a.val < b.val
    rwa [hz] at hzb
  exact (rankCutUtility_upper e hxa.le).trans_lt
    ((rationalRankValue_strictMono e hab).trans_le (rankCutUtility_lower e hby.le))

/-- Completing the rational scale preserves the original preference representation. -/
theorem rankCutUtility_represents (e : InteriorRankSet v D ≃o RationalUnit)
    (hs : StrictRankSeparator v D) {r : X → X → Prop} (hv : Represents v r) :
    Represents (RankCutUtility e) r := by
  intro x y
  constructor
  · intro hxy
    exact rankCutUtility_mono e ((hv x y).mp hxy)
  · intro hxy
    by_contra hn
    have hlt : v x < v y := lt_of_not_ge (fun h => hn ((hv x y).mpr h))
    exact (not_lt_of_ge hxy) (rankCutUtility_strict e hs hlt)

/-- Every rational point strictly between zero and one is attained by the new utility. -/
theorem rankCutUtility_attains_rationals (e : InteriorRankSet v D ≃o RationalUnit)
    (q : RationalUnit) : ∃ x, RankCutUtility e x = (q.val : ℝ) := by
  let a := e.symm q
  obtain ⟨x, hx⟩ := interiorRank_witness a
  refine ⟨x, ?_⟩
  calc
    RankCutUtility e x = RationalRankValue e a := rankCutUtility_at_rank e hx
    _ = (q.val : ℝ) := by simp [RationalRankValue, a]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The open and unbounded menu examples

Kreps I, introductory examples in Problem 2.2, p. 46. Strictly monotone preference
on the nonnegative half-line has no best point on `(1,5)` or `(3,∞)`, although both
menus are nonempty and convex. The compact-menu counterexample is proved separately
in `ConvexityExamples`.
-/

namespace Kreps.PreferenceProperties

/-- A relatively open bounded interval in the one-good consumption domain. -/
def OpenIntervalMenu (a b : ℝ) : Set OneGood := {x | a < x.val ∧ x.val < b}

/-- An open upper ray in the one-good consumption domain. -/
def UpperRayMenu (a : ℝ) : Set OneGood := {x | a < x.val}

/-- The bounded interval menu is convex, including when it is empty. -/
theorem openIntervalMenu_convex (a b : ℝ) :
    ConvexMenu (convex_Ici (0 : ℝ)) (OpenIntervalMenu a b) := by
  intro x hx y hy t ht
  exact (convex_Ioo a b) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)

/-- The upper-ray menu is convex. -/
theorem upperRayMenu_convex (a : ℝ) :
    ConvexMenu (convex_Ici (0 : ℝ)) (UpperRayMenu a) := by
  intro x hx y hy t ht
  exact (convex_Ioi a) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)

/-- Moving halfway toward the excluded upper endpoint beats every point of an open interval. -/
theorem strictlyMonotone_openInterval_empty {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) (a b : ℝ) : PrefChoice r (OpenIntervalMenu a b) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxb : x.val < b := hx.1.2
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨(x.val + b) / 2, show 0 ≤ (x.val + b) / 2 from by linarith⟩
  have hyx : x < y := by change x.val < (x.val + b) / 2; linarith
  have hy : y ∈ OpenIntervalMenu a b := by
    change a < (x.val + b) / 2 ∧ (x.val + b) / 2 < b
    have hax : a < x.val := hx.1.1
    constructor <;> linarith
  exact (hm y x hyx.le (ne_of_gt hyx)).2 (hx.2 y hy)

/-- Adding one unit beats every point of the unbounded upper-ray menu. -/
theorem strictlyMonotone_upperRay_empty {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) (a : ℝ) : PrefChoice r (UpperRayMenu a) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨x.val + 1, show 0 ≤ x.val + 1 from by linarith⟩
  have hyx : x < y := by change x.val < x.val + 1; linarith
  have hy : y ∈ UpperRayMenu a := by
    change a < x.val + 1
    have hax : a < x.val := hx.1
    linarith
  exact (hm y x hyx.le (ne_of_gt hyx)).2 (hx.2 y hy)

/-- **Problem 2.2**, introductory examples: both nonempty convex menus have empty best sets. -/
theorem problem_2_2_intervals {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) :
    (OpenIntervalMenu 1 5).Nonempty ∧ ConvexMenu (convex_Ici (0 : ℝ)) (OpenIntervalMenu 1 5) ∧
      PrefChoice r (OpenIntervalMenu 1 5) = ∅ ∧ (UpperRayMenu 3).Nonempty ∧
      ConvexMenu (convex_Ici (0 : ℝ)) (UpperRayMenu 3) ∧ PrefChoice r (UpperRayMenu 3) = ∅ := by
  refine ⟨⟨⟨3, by norm_num⟩, by norm_num [OpenIntervalMenu]⟩,
    openIntervalMenu_convex 1 5, strictlyMonotone_openInterval_empty hm 1 5,
    ⟨⟨4, by norm_num⟩, by norm_num [UpperRayMenu]⟩,
    upperRayMenu_convex 3, strictlyMonotone_upperRay_empty hm 3⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The plateau-product counterexample

Kreps I, Problem 2.8a, first utility. The scalar product is unchanged below four,
constant at four between four and eight, and reduced by four above eight.
Its preference is convex and continuous, but fails semi-strict convexity and
therefore admits no concave numerical representation.
-/

namespace Kreps.PreferenceProperties

/-- The continuous nondecreasing scalar transformation defining the first example. -/
noncomputable def ProductPlateau (s : ℝ) : ℝ := min s 4 + max (s - 8) 0

/-- The first branch in the book's displayed formula. -/
theorem productPlateau_below {s : ℝ} (hs : s ≤ 4) : ProductPlateau s = s := by
  have ht : s - 8 ≤ 0 := by linarith
  simp [ProductPlateau, min_eq_left hs, max_eq_right ht]

/-- The middle, flat branch includes both endpoints consistently. -/
theorem productPlateau_middle {s : ℝ} (hs : 4 ≤ s) (ht : s ≤ 8) :
    ProductPlateau s = 4 := by
  simp [ProductPlateau, min_eq_right hs, max_eq_right (sub_nonpos.mpr ht)]

/-- The upper branch in the book's displayed formula. -/
theorem productPlateau_above {s : ℝ} (hs : 8 ≤ s) : ProductPlateau s = s - 4 := by
  have ht : 4 ≤ s := by linarith
  rw [ProductPlateau, min_eq_right ht, max_eq_left (sub_nonneg.mpr hs)]
  ring

/-- Flattening the interval `[4,8]` preserves weak ordering of products. -/
theorem productPlateau_monotone : Monotone ProductPlateau := by
  intro a b hab
  exact add_le_add (min_le_min hab le_rfl) (max_le_max (sub_le_sub_right hab 8) le_rfl)

/-- The two corners do not create a discontinuity. -/
theorem productPlateau_continuous : Continuous ProductPlateau :=
  (continuous_id.min continuous_const).add
    ((continuous_id.sub continuous_const).max continuous_const)

/-- The exact utility `u₁` in Problem 2.8a. -/
noncomputable def PlateauProductUtility (x : NonnegativeOrthant 2) : ℝ :=
  ProductPlateau (TwoGoodProduct x)

/-- The first utility is continuous, despite having a flat range of product levels. -/
theorem plateauProductUtility_continuous : Continuous PlateauProductUtility :=
  productPlateau_continuous.comp twoGoodProduct_continuous

/-- Weakly increasing transformations preserve the product's quasi-concavity. -/
theorem plateauProductUtility_quasiConcave :
    QuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) PlateauProductUtility := by
  intro x y a ha
  change min (ProductPlateau (TwoGoodProduct x)) (ProductPlateau (TwoGoodProduct y)) ≤ _
  rw [← productPlateau_monotone.map_min]
  exact productPlateau_monotone (twoGoodProduct_quasiConcave x y a ha)

/-- A better endpoint can mix into the plateau of the worse endpoint. -/
theorem plateauProductUtility_not_semiStrict :
    ¬ SemiStrictlyQuasiConcaveUtility (convex_Ici (0 : Fin 2 → ℝ))
      PlateauProductUtility := by
  intro h
  let x := PairBundle 3 3 (by norm_num) (by norm_num)
  let y := PairBundle 2 2 (by norm_num) (by norm_num)
  have hxy : PlateauProductUtility y < PlateauProductUtility x := by
    norm_num [x, y, PlateauProductUtility, ProductPlateau, TwoGoodProduct, PairBundle]
  have hm := h.2 x y hxy (1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num [x, y, PlateauProductUtility, ProductPlateau, TwoGoodProduct, PairBundle, Mix] at hm

/-- The first example's preference is not semi-strictly convex. -/
theorem plateauProductPreference_not_semiStrict :
    ¬ SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref PlateauProductUtility) := by
  intro h
  exact plateauProductUtility_not_semiStrict
    ((proposition_2_8b_semiStrict (fun _ _ => Iff.rfl)).mpr h)

/-- The failure is ordinal: no concave function can represent these preferences. -/
theorem plateauProductPreference_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref PlateauProductUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hc⟩
  exact plateauProductPreference_not_semiStrict
    ((proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc))

/-- **Problem 2.8a, first example:** convex and continuous, but not semi-strictly convex. -/
theorem problem_2_8a_first :
    Rational (UtilityPref PlateauProductUtility) ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref PlateauProductUtility) ∧
      ContinuousPreference (UtilityPref PlateauProductUtility) ∧
      ¬ SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
        (UtilityPref PlateauProductUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref PlateauProductUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _,
    (proposition_2_8b_quasi (fun _ _ => Iff.rfl)).mp plateauProductUtility_quasiConcave,
    continuousPreference_of_continuous_utility plateauProductUtility_continuous,
    plateauProductPreference_not_semiStrict, plateauProductPreference_no_concave_representation⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The split product-level counterexample

Kreps I, Problem 2.8a, second utility. The level with product four is split into
two ranks according to the relative sizes of the two commodities. Preferences
are semi-strictly convex but discontinuous. The obstruction to every concave
representation is proved separately in `SplitProductNoConcavity`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The exact utility `u₂`, with the lower half of the product-four level valued at four. -/
noncomputable def SplitProductUtility (x : NonnegativeOrthant 2) : ℝ :=
  if TwoGoodProduct x < 4 then TwoGoodProduct x
  else if TwoGoodProduct x = 4 then if x.val 1 ≤ x.val 0 then 4 else 5
  else TwoGoodProduct x + 1

/-- Below the split level, the second utility is the commodity product. -/
theorem splitProductUtility_below {x : NonnegativeOrthant 2} (hx : TwoGoodProduct x < 4) :
    SplitProductUtility x = TwoGoodProduct x := by
  simp [SplitProductUtility, hx]

/-- On the lower half of the split level, utility equals four. -/
theorem splitProductUtility_at_lower {x : NonnegativeOrthant 2}
    (hx : TwoGoodProduct x = 4) (hc : x.val 1 ≤ x.val 0) : SplitProductUtility x = 4 := by
  simp [SplitProductUtility, hx, hc]

/-- On the upper half of the split level, utility equals five. -/
theorem splitProductUtility_at_upper {x : NonnegativeOrthant 2}
    (hx : TwoGoodProduct x = 4) (hc : x.val 0 < x.val 1) : SplitProductUtility x = 5 := by
  simp [SplitProductUtility, hx, not_le_of_gt hc]

/-- Above the split level, utility is the product plus one. -/
theorem splitProductUtility_above {x : NonnegativeOrthant 2} (hx : 4 < TwoGoodProduct x) :
    SplitProductUtility x = TwoGoodProduct x + 1 := by
  simp [SplitProductUtility, not_lt_of_ge hx.le, ne_of_gt hx]

/-- Zero-product bundles all have zero utility. -/
theorem splitProductUtility_zero {x : NonnegativeOrthant 2} (hx : TwoGoodProduct x = 0) :
    SplitProductUtility x = 0 := by
  simp [SplitProductUtility, hx]

/-- The second utility is nonnegative everywhere. -/
theorem splitProductUtility_nonneg (x : NonnegativeOrthant 2) : 0 ≤ SplitProductUtility x := by
  have hp : 0 ≤ TwoGoodProduct x := mul_nonneg (x.property 0) (x.property 1)
  unfold SplitProductUtility
  split_ifs <;> linarith

/-- Strictly increasing the product strictly improves utility, including across the split level. -/
theorem splitProductUtility_strict_of_product_lt {x y : NonnegativeOrthant 2}
    (hxy : TwoGoodProduct x < TwoGoodProduct y) :
    SplitProductUtility x < SplitProductUtility y := by
  unfold SplitProductUtility
  split_ifs <;> linarith

/-- A higher utility rank cannot have a lower commodity product. -/
theorem splitProductUtility_product_le {x y : NonnegativeOrthant 2}
    (hxy : SplitProductUtility y ≤ SplitProductUtility x) :
    TwoGoodProduct y ≤ TwoGoodProduct x := by
  by_contra h
  exact not_lt_of_ge hxy (splitProductUtility_strict_of_product_lt (lt_of_not_ge h))

/-- All upper preference contours of the second utility are convex. -/
theorem splitProductPreference_convex :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref SplitProductUtility) := by
  intro x y hxy a ha
  by_cases h0 : a = 0
  · subst a
    rw [mix_zero]
    exact le_rfl
  by_cases h1 : a = 1
  · subst a
    rw [mix_one]
    exact hxy
  by_cases he : x = y
  · subst x
    rw [mix_self]
    exact le_rfl
  have hai : a ∈ Set.Ioo 0 1 :=
    ⟨lt_of_le_of_ne ha.1 (Ne.symm h0), lt_of_le_of_ne ha.2 h1⟩
  by_cases hy : TwoGoodProduct y = 0
  · change SplitProductUtility y ≤ _
    rw [splitProductUtility_zero hy]
    exact splitProductUtility_nonneg _
  · have hyp : 0 < TwoGoodProduct y :=
      lt_of_le_of_ne (mul_nonneg (y.property 0) (y.property 1)) (Ne.symm hy)
    exact (splitProductUtility_strict_of_product_lt
      (twoGoodProduct_mix_strict hyp (splitProductUtility_product_le hxy) he hai)).le

/-- Strictly ordered endpoints give a strict improvement under every interior mixture. -/
theorem splitProductPreference_semiStrict :
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref SplitProductUtility) := by
  refine ⟨splitProductPreference_convex, ?_⟩
  intro x y hxy a ha
  have hu : Represents SplitProductUtility (UtilityPref SplitProductUtility) := fun _ _ => Iff.rfl
  have hstrict := (strict_iff_utility_lt hu x y).mp hxy
  have hne : x ≠ y := by intro he; subst x; exact lt_irrefl _ hstrict
  apply (strict_iff_utility_lt hu _ y).mpr
  apply splitProductUtility_strict_of_product_lt
  by_cases hy : TwoGoodProduct y = 0
  · have hx : TwoGoodProduct x ≠ 0 := by
      intro hx
      rw [splitProductUtility_zero hx, splitProductUtility_zero hy] at hstrict
      exact lt_irrefl _ hstrict
    have hxp : 0 < TwoGoodProduct x :=
      lt_of_le_of_ne (mul_nonneg (x.property 0) (x.property 1)) (Ne.symm hx)
    rw [hy]
    exact twoGoodProduct_mix_pos hxp ha
  · have hyp : 0 < TwoGoodProduct y :=
      lt_of_le_of_ne (mul_nonneg (y.property 0) (y.property 1)) (Ne.symm hy)
    exact twoGoodProduct_mix_strict hyp (splitProductUtility_product_le hstrict.le) hne ha

/-- A sequence above the split level converges to its lower-rank midpoint. -/
noncomputable def SplitProductApproach (n : ℕ) : NonnegativeOrthant 2 :=
  PairBundle (2 + (1 / 2 : ℝ) ^ n) 2 (by positivity) (by norm_num)

/-- The bundles approaching `(2,2)` have utility strictly above the rank-five bundle `(1,4)`. -/
theorem splitProductApproach_rank (n : ℕ) :
    UtilityPref SplitProductUtility (SplitProductApproach n)
      (PairBundle 1 4 (by norm_num) (by norm_num)) := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hprod : 4 < TwoGoodProduct (SplitProductApproach n) := by
    dsimp [TwoGoodProduct, SplitProductApproach, PairBundle]
    norm_num
    linarith
  change SplitProductUtility _ ≤ SplitProductUtility _
  rw [splitProductUtility_above hprod]
  norm_num [SplitProductUtility, TwoGoodProduct, PairBundle, SplitProductApproach]
  linarith

/-- The sequence converges in the full orthant topology. -/
theorem splitProductApproach_tendsto :
    Filter.Tendsto SplitProductApproach Filter.atTop
      (𝓝 (PairBundle 2 2 (by norm_num) (by norm_num))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · change Filter.Tendsto (fun n : ℕ => 2 + (1 / 2 : ℝ) ^ n) _ (𝓝 (2 : ℝ))
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  · exact tendsto_const_nhds

/-- An upper contour fails to contain the limit of a converging sequence of its members. -/
theorem splitProductPreference_not_continuous :
    ¬ ContinuousPreference (UtilityPref SplitProductUtility) := by
  intro hc
  have hclosed := ((proposition_1_14c (proposition_1_3a SplitProductUtility)).mp hc
    (PairBundle 1 4 (by norm_num) (by norm_num))).2
  have hmem := hclosed.mem_of_tendsto splitProductApproach_tendsto
    (Filter.Eventually.of_forall splitProductApproach_rank)
  norm_num [NoWorseThan, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle] at hmem

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Density of the recursively assigned values

Kreps I, Problem 2.14(e), p. 49. The first point inserted between two adjacent
assigned ranks receives their midpoint. If the original sampled order has a rank
strictly between any two distinct ranks, this midpoint rule rules out gaps in the
closure of the numerical range.
-/

namespace Kreps.PreferenceProperties

/-- An order-dense enumeration remains order-dense after the recursive reassignment. -/
theorem recursiveRank_has_between (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j)
    {i j : ℕ} (hij : RecursiveRank v i < RecursiveRank v j) :
    ∃ k, RecursiveRank v i < RecursiveRank v k ∧ RecursiveRank v k < RecursiveRank v j := by
  obtain ⟨k, hik, hkj⟩ := hd i j ((recursiveRank_lt_iff v i j).mp hij)
  exact ⟨k, (recursiveRank_lt_iff v i k).mpr hik, (recursiveRank_lt_iff v k j).mpr hkj⟩

/-- The first insertion into a gap of a finite prefix must be the gap's midpoint. -/
theorem recursiveRank_first_between (v : ℕ → ℝ) (i j N : ℕ) (hiN : i ≤ N) (hjN : j ≤ N)
    (hgap : ∀ k ≤ N, ¬ (RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j))
    (hne : ∃ k, RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j) :
    ∃ k, RecursiveRank v k = (RecursiveRank v i + RecursiveRank v j) / 2 := by
  classical
  let n := Nat.find hne
  have hn : RecursiveRank v i < RecursiveRank v n ∧ RecursiveRank v n < RecursiveRank v j :=
    Nat.find_spec hne
  have hprior : ∀ k < n, ¬ (RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j) := fun _ hk => Nat.find_min hne hk
  have hNn : N < n := by
    by_contra h
    exact hgap n (Nat.le_of_not_gt h) hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  let vp : Fin (m + 1) → ℝ := fun k => v k
  let up : Fin (m + 1) → ℝ := fun k => RecursiveRank v k
  let i' : Fin (m + 1) := ⟨i, by omega⟩
  let j' : Fin (m + 1) := ⟨j, by omega⟩
  have he : RecursiveRank v n = InsertedRank vp up (v n) := by
    simpa only [hm] using recursiveRank_succ v m
  have hil : vp i' < v n := (recursiveRank_lt_iff v i n).mp hn.1
  have hjh : v n < vp j' := (recursiveRank_lt_iff v n j).mp hn.2
  have hnt : ¬ ∃ k, vp k = v n := by
    rintro ⟨k, hk⟩
    have heq : RecursiveRank v k = RecursiveRank v n := (recursiveRank_eq_iff v k n).mpr hk
    exact hprior k (by have := k.isLt; omega) (by simpa only [heq] using hn)
  have hmax : sSup (PreviousLowerRanks vp up (v n)) = RecursiveRank v i := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨i', hil, rfl⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    by_contra h
    have hleft : RecursiveRank v i < RecursiveRank v k := lt_of_not_ge h
    have hright : RecursiveRank v k < RecursiveRank v n :=
      (recursiveRank_lt_iff v k n).mpr hk
    exact hprior k (by have := k.isLt; omega) ⟨hleft, hright.trans hn.2⟩
  have hmin : sInf (PreviousUpperRanks vp up (v n)) = RecursiveRank v j := by
    apply IsLeast.csInf_eq
    refine ⟨⟨j', hjh, rfl⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    by_contra h
    have hright : RecursiveRank v k < RecursiveRank v j := lt_of_not_ge h
    have hleft : RecursiveRank v n < RecursiveRank v k :=
      (recursiveRank_lt_iff v n k).mpr hk
    exact hprior k (by have := k.isLt; omega) ⟨hn.1.trans hleft, hright⟩
  refine ⟨n, ?_⟩
  rw [he, insertedRank_between hnt ⟨i', hil⟩ ⟨j', hjh⟩, hmax, hmin]

/-- No open interval between assigned values can be missing from their closure. -/
theorem recursiveRank_between_mem_closure (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j)
    {i j : ℕ} {r : ℝ} (hi : RecursiveRank v i < r) (hj : r < RecursiveRank v j) :
    r ∈ closure (Set.range (RecursiveRank v)) := by
  classical
  let u := RecursiveRank v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  by_contra hmissing
  have hdist : ∀ n, ε ≤ |u n - r| := by
    intro n
    have h := not_lt.mpr (le_of_not_gt (fun hn =>
      hmissing ⟨u n, Set.mem_range_self n, hn⟩))
    simpa only [Real.dist_eq, abs_sub_comm, not_lt] using h
  have hne : ∀ n, u n ≠ r := by
    intro n hn
    have h := hdist n
    rw [hn, sub_self, abs_zero] at h
    linarith
  let L : Set ℝ := Set.range u ∩ Set.Iio r
  let H : Set ℝ := Set.range u ∩ Set.Ioi r
  have hLn : L.Nonempty := ⟨u i, Set.mem_range_self i, hi⟩
  have hHn : H.Nonempty := ⟨u j, Set.mem_range_self j, hj⟩
  have hLb : BddAbove L := ⟨r, fun _ hz => hz.2.le⟩
  have hHb : BddBelow H := ⟨r, fun _ hz => hz.2.le⟩
  let l := sSup L
  let h := sInf H
  have hll : l ≤ r - ε := by
    apply csSup_le hLn
    rintro y ⟨⟨n, rfl⟩, hn⟩
    have h := hdist n
    rw [abs_of_neg (sub_neg.mpr hn)] at h
    linarith
  have hhh : r + ε ≤ h := by
    apply le_csInf hHn
    rintro y ⟨⟨n, rfl⟩, hn⟩
    have h := hdist n
    rw [abs_of_pos (sub_pos.mpr hn)] at h
    linarith
  have hlh : l < h := by linarith
  let δ := (h - l) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨a, haL, haNear⟩ := exists_lt_of_lt_csSup hLn (show l - δ < l by linarith)
  obtain ⟨b, hbH, hbNear⟩ := exists_lt_of_csInf_lt hHn (show h < h + δ by linarith)
  obtain ⟨ia, hia⟩ := haL.1
  obtain ⟨ib, hib⟩ := hbH.1
  let N := max ia ib
  let up : Fin (N + 1) → ℝ := fun k => u k
  let LP : Set ℝ := up '' {k | up k < r}
  let HP : Set ℝ := up '' {k | r < up k}
  let ia' : Fin (N + 1) := ⟨ia, Nat.lt_succ_of_le (le_max_left ia ib)⟩
  let ib' : Fin (N + 1) := ⟨ib, Nat.lt_succ_of_le (le_max_right ia ib)⟩
  have hialow : up ia' < r := by
    change u ia < r
    rw [hia]
    exact haL.2
  have hibhigh : r < up ib' := by
    change r < u ib
    rw [hib]
    exact hbH.2
  have hLPn : LP.Nonempty := ⟨a, ia', hialow, hia⟩
  have hHPn : HP.Nonempty := ⟨b, ib', hibhigh, hib⟩
  have hLPf : LP.Finite := (Set.toFinite _).image up
  have hHPf : HP.Finite := (Set.toFinite _).image up
  obtain ⟨ip, hip, heip⟩ := hLPn.csSup_mem hLPf
  obtain ⟨jp, hjp, hejp⟩ := hHPn.csInf_mem hHPf
  have hipNear : l - δ < up ip := by
    have haLe' : a ≤ sSup LP := le_csSup hLPf.bddAbove ⟨ia', hialow, hia⟩
    rw [← heip] at haLe'
    exact haNear.trans_le haLe'
  have hjpNear : up jp < h + δ := by
    have hbLe : sInf HP ≤ b := csInf_le hHPf.bddBelow ⟨ib', hibhigh, hib⟩
    rw [← hejp] at hbLe
    exact hbLe.trans_lt hbNear
  have hipBound : up ip ≤ l := le_csSup hLb ⟨Set.mem_range_self ip.val, hip⟩
  have hjpBound : h ≤ up jp := csInf_le hHb ⟨Set.mem_range_self jp.val, hjp⟩
  have hgap : ∀ k ≤ N, ¬ (u ip < u k ∧ u k < u jp) := by
    intro k hk hbetween
    let k' : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    rcases lt_or_gt_of_ne (hne k) with hkr | hrk
    · have hkLe : up k' ≤ sSup LP := le_csSup hLPf.bddAbove ⟨k', hkr, rfl⟩
      rw [← heip] at hkLe
      exact not_lt_of_ge hkLe hbetween.1
    · have hkLe : sInf HP ≤ up k' := csInf_le hHPf.bddBelow ⟨k', hrk, rfl⟩
      rw [← hejp] at hkLe
      exact not_lt_of_ge hkLe hbetween.2
  have hbetween := recursiveRank_has_between v hd (show u ip < u jp from hip.trans hjp)
  obtain ⟨k, hk⟩ := recursiveRank_first_between v ip jp N
    (Nat.le_of_lt_succ ip.isLt) (Nat.le_of_lt_succ jp.isLt) hgap hbetween
  have hmidlo : l < u k := by
    change u k = (up ip + up jp) / 2 at hk
    dsimp [δ] at hipNear hjpNear
    linarith
  have hmidhi : u k < h := by
    change u k = (up ip + up jp) / 2 at hk
    dsimp [δ] at hipNear hjpNear
    linarith
  rcases lt_or_gt_of_ne (hne k) with hkr | hrk
  · have hkLe : u k ≤ l := le_csSup hLb ⟨Set.mem_range_self k, hkr⟩
    exact not_lt_of_ge hkLe hmidlo
  · have hkLe : h ≤ u k := csInf_le hHb ⟨Set.mem_range_self k, hrk⟩
    exact not_lt_of_ge hkLe hmidhi

/-- The smallest interval containing all values of the recursive assignment. -/
def RecursiveRankInterval (v : ℕ → ℝ) : Set ℝ :=
  {t | ∃ i j, RecursiveRank v i ≤ t ∧ t ≤ RecursiveRank v j}

/-- Every assigned value belongs to the containing interval. -/
theorem recursiveRank_range_subset_interval (v : ℕ → ℝ) :
    Set.range (RecursiveRank v) ⊆ RecursiveRankInterval v := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, n, le_rfl, le_rfl⟩

/-- The containing set really is an interval. -/
theorem recursiveRankInterval_ordConnected (v : ℕ → ℝ) :
    Set.OrdConnected (RecursiveRankInterval v) := by
  constructor
  rintro x ⟨i, _, hix, _⟩ y ⟨_, j, _, hyj⟩ z ⟨hxz, hzy⟩
  exact ⟨i, j, hix.trans hxz, hzy.trans hyj⟩

/-- Every interval containing all assigned values contains this interval. -/
theorem recursiveRankInterval_minimal (v : ℕ → ℝ) {S : Set ℝ}
    (hS : Set.OrdConnected S) (hrange : Set.range (RecursiveRank v) ⊆ S) :
    RecursiveRankInterval v ⊆ S := by
  rintro t ⟨i, j, hit, htj⟩
  exact hS.out (hrange (Set.mem_range_self i)) (hrange (Set.mem_range_self j)) ⟨hit, htj⟩

/-- The closure of the assigned values contains every point of their smallest interval. -/
theorem recursiveRankInterval_subset_closure (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j) :
    RecursiveRankInterval v ⊆ closure (Set.range (RecursiveRank v)) := by
  rintro t ⟨i, j, hit, htj⟩
  rcases hit.eq_or_lt with he | hi
  · exact he ▸ subset_closure (Set.mem_range_self i)
  rcases htj.eq_or_lt with he | hj
  · exact he.symm ▸ subset_closure (Set.mem_range_self j)
  exact recursiveRank_between_mem_closure v hd hi hj

/-- Relative density of the recursively assigned values in their smallest containing interval. -/
theorem recursiveRank_dense_in_interval (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j) :
    DenseRange (Set.inclusion (recursiveRank_range_subset_interval v)) :=
  (denseRange_inclusion_iff _).mpr (recursiveRankInterval_subset_closure v hd)

/-- **Problem 2.14(e):** the assigned values are dense in their smallest containing interval. -/
theorem problem_2_14e {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) (q : ℕ → X) (hq : DenseRange q) :
    DenseRange (Set.inclusion (recursiveRank_range_subset_interval (v ∘ q))) := by
  apply recursiveRank_dense_in_interval
  intro i j hij
  obtain ⟨x, ⟨k, rfl⟩, hik, hkj⟩ := dense_strictRankSeparator hr hc hv hq (q i) (q j) hij
  exact ⟨k, hik, hkj⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The ratio-and-sum utility in Problem 2.8b

Below the line where total consumption equals one, utility is a fractional-linear
function. Above that line it is the sum of consumption. These formulas agree on
the dividing line. The axis and mixture identities here support the proof that
no concave function represents the resulting preferences.
-/

namespace Kreps.PreferenceProperties

/-- The exact utility `u₃` in Problem 2.8b. -/
noncomputable def RatioSumUtility (x : NonnegativeOrthant 2) : ℝ :=
  if x.val 0 + x.val 1 ≤ 1 then 2 * (1 + x.val 1) / (2 - x.val 0) - 1
  else x.val 0 + x.val 1

/-- The nonnegative second-commodity axis, extended by clamping negative parameters to zero. -/
noncomputable def RatioAxisBundle (t : ℝ) : NonnegativeOrthant 2 :=
  PairBundle 0 (max t 0) (by norm_num) (le_max_right _ _)

/-- Along the nonnegative axis, the displayed utility equals its quantity parameter. -/
theorem ratioSumUtility_axis {t : ℝ} (ht : 0 ≤ t) :
    RatioSumUtility (RatioAxisBundle t) = t := by
  simp only [RatioSumUtility, RatioAxisBundle, PairBundle, max_eq_left ht]
  norm_num

/-- The axis parametrization respects nonnegative convex mixtures. -/
theorem ratioAxisBundle_mix {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {a : ℝ} (ha : a ∈ Set.Icc 0 1) :
    Mix (convex_Ici (0 : Fin 2 → ℝ)) (RatioAxisBundle s) (RatioAxisBundle t) a ha =
      RatioAxisBundle (a * s + (1 - a) * t) := by
  have hm : 0 ≤ a * s + (1 - a) * t :=
    add_nonneg (mul_nonneg ha.1 hs) (mul_nonneg (sub_nonneg.mpr ha.2) ht)
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [Mix, RatioAxisBundle, PairBundle, max_eq_left hs, max_eq_left ht,
    max_eq_left hm]

/-- Restricting a concave utility to the axis gives an ordinary concave real function. -/
theorem concaveUtility_ratioAxis {u : NonnegativeOrthant 2 → ℝ}
    (hu : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u) :
    ConcaveOn ℝ (Set.Ici 0) (fun t => u (RatioAxisBundle t)) := by
  refine ⟨convex_Ici _, ?_⟩
  intro s hs t ht a b ha hb hab
  have he : b = 1 - a := by linarith
  subst b
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
  have hj := hu (RatioAxisBundle s) (RatioAxisBundle t) a ha'
  rw [ratioAxisBundle_mix hs ht ha'] at hj
  exact hj

/-- The ordinary concave secant bound controls increments to the right of rank one half. -/
theorem concaveUtility_ratioAxis_bound {u : NonnegativeOrthant 2 → ℝ}
    (hu : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u) {δ : ℝ} (hδ : 0 < δ) :
    u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2)) ≤
      2 * δ * (u (RatioAxisBundle (1 / 2)) - u (RatioAxisBundle 0)) := by
  have hs := (concaveUtility_ratioAxis hu).slope_anti_adjacent
    (x := 0) (y := 1 / 2) (z := 1 / 2 + δ) (by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) + δ by linarith)
    (by norm_num) (by linarith)
  have hs' : (u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2))) / δ ≤
      2 * (u (RatioAxisBundle (1 / 2)) - u (RatioAxisBundle 0)) := by
    convert hs using 1 <;> ring
  have hmul := (div_le_iff₀ hδ).mp hs'
  nlinarith

/-- A higher-rank bundle on a shorter ray from the common center of the lower indifference lines. -/
noncomputable def RatioRayBundle (δ : ℝ) (hδ : 0 ≤ δ) : NonnegativeOrthant 2 :=
  PairBundle (1 / 2) (1 / 8 + (3 / 4) * δ) (by norm_num) (by positivity)

/-- The shorter-ray bundle has rank one half plus its increment. -/
theorem ratioSumUtility_ray {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    RatioSumUtility (RatioRayBundle δ hδ) = 1 / 2 + δ := by
  have hs : (1 / 2 : ℝ) + (1 / 8 + (3 / 4) * δ) ≤ 1 := by linarith
  norm_num [RatioSumUtility, RatioRayBundle, PairBundle, hs]
  ring

/-- Equal physical weights contract the rank increment by three sevenths. -/
theorem ratioSumUtility_ray_mix {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    RatioSumUtility (Mix (convex_Ici (0 : Fin 2 → ℝ))
      (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ) (1 / 2) ⟨by norm_num, by norm_num⟩) =
      1 / 2 + (3 / 7) * δ := by
  have hs : (1 / 2 : ℝ) * (1 / 2) +
      (1 / 2 * (1 / 2) + 1 / 2 * (1 / 8 + 3 / 4 * δ)) ≤ 1 := by linarith
  norm_num [RatioSumUtility, RatioAxisBundle, RatioRayBundle, PairBundle, Mix]
  norm_num at hs
  rw [ite_eq_left hs]
  ring

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strong separability and third-factor cancellation

Preparation for Kreps I, Proposition 2.14. Debreu's 1959 discussion paper,
pp. 12-13, derives the local Thomsen hexagon by compensating in a third block.
The cancellation below is proved from strong separability, not assumed as an axiom.
Connectedness and continuity supply the compensator locally. The cardinal-scale
construction and its global extension culminate in `proposition_2_14_exists`
in `PrimitiveAdditiveExistence`.

Source: https://cowles.yale.edu/sites/default/files/2022-08/d0076.pdf
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
  {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- Independence of the complement of a block allows its common value to be changed. -/
theorem stronglySeparable_complement_iff [Finite I] (hs : StronglySeparable r)
    (i : I) (x y : ∀ i, B i) (a b : B i) :
    r (Function.update x i a) (Function.update y i a) ↔
      r (Function.update x i b) (Function.update y i b) := by
  let : Fintype I := Fintype.ofFinite I
  simpa only [Finset.piecewise_erase_univ, Function.update_self] using
    hs (Finset.univ.erase i) x y (Function.update x i a) (Function.update x i b)

/-- When two bundles have the same block, changing that common block preserves comparison. -/
theorem stronglySeparable_common_update_iff [Finite I] (hs : StronglySeparable r)
    {i : I} {x y : ∀ i, B i} (hxy : x i = y i) (a : B i) :
    r x y ↔ r (Function.update x i a) (Function.update y i a) := by
  have hy : Function.update y i (x i) = y := by
    rw [hxy, Function.update_eq_self]
  simpa only [Function.update_eq_self, hy] using
    stronglySeparable_complement_iff hs i x y (x i) a

/-- A three-coordinate slice through a reference bundle. -/
def ThreeCoordinateBundle (z : ∀ i, B i) (i j l : I)
    (a : B i) (b : B j) (c : B l) : ∀ i, B i :=
  Function.update (Function.update (Function.update z i a) j b) l c

/-- Replacing the first selected coordinate stays in the same three-coordinate slice. -/
theorem threeCoordinateBundle_update_first (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (a a' : B i) (b : B j) (c : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) i a' =
      ThreeCoordinateBundle z i j l a' b c := by
  unfold ThreeCoordinateBundle
  rw [Function.update_comm hil.symm, Function.update_comm hij.symm, Function.update_idem]

/-- Replacing the second selected coordinate stays in the same slice. -/
theorem threeCoordinateBundle_update_second (z : ∀ i, B i) {i j l : I}
    (hjl : j ≠ l) (a : B i) (b b' : B j) (c : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) j b' =
      ThreeCoordinateBundle z i j l a b' c := by
  unfold ThreeCoordinateBundle
  rw [Function.update_comm hjl.symm, Function.update_idem]

/-- Replacing the third selected coordinate stays in the same slice. -/
theorem threeCoordinateBundle_update_third (z : ∀ i, B i) (i j l : I)
    (a : B i) (b : B j) (c c' : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) l c' =
      ThreeCoordinateBundle z i j l a b c' := by
  simp only [ThreeCoordinateBundle, Function.update_idem]

/-- Independence of each pair of factors from the remaining factor. -/
def ThreeFactorIndependent {A B C : Type*}
    (r : (A × B × C) → (A × B × C) → Prop) : Prop :=
  (∀ a a' b b' c c', r (a, b, c) (a, b', c') ↔ r (a', b, c) (a', b', c')) ∧
  (∀ b b' a a' c c', r (a, b, c) (a', b, c') ↔ r (a, b', c) (a', b', c')) ∧
  (∀ c c' a a' b b', r (a, b, c) (a', b', c) ↔ r (a, b, c') (a', b', c'))

/-- Strong separability supplies all three independence properties on every distinct-block slice. -/
theorem stronglySeparable_threeFactor [Finite I] (hs : StronglySeparable r)
    (z : ∀ i, B i) {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ThreeFactorIndependent (fun p q : B i × B j × B l =>
      r (ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2)
        (ThreeCoordinateBundle z i j l q.1 q.2.1 q.2.2)) := by
  constructor
  · intro a a' b b' c c'
    have he : ThreeCoordinateBundle z i j l a b c i =
        ThreeCoordinateBundle z i j l a b' c' i := by
      simp [ThreeCoordinateBundle, hij, hil]
    simpa only [threeCoordinateBundle_update_first z hij hil] using
      stronglySeparable_common_update_iff hs he a'
  constructor
  · intro b b' a a' c c'
    have he : ThreeCoordinateBundle z i j l a b c j =
        ThreeCoordinateBundle z i j l a' b c' j := by
      simp [ThreeCoordinateBundle, hjl]
    simpa only [threeCoordinateBundle_update_second z hjl] using
      stronglySeparable_common_update_iff hs he b'
  · intro c c' a a' b b'
    have he : ThreeCoordinateBundle z i j l a b c l =
        ThreeCoordinateBundle z i j l a' b' c l := by
      simp [ThreeCoordinateBundle]
    simpa only [threeCoordinateBundle_update_third] using
      stronglySeparable_common_update_iff hs he c'

/-- Transitivity of weak preference gives transitivity of indifference. -/
theorem indifferent_transitive {X : Type*} {r : X → X → Prop} (ht : TransitivePref r)
    {x y z : X} (hxy : Indifferent r x y) (hyz : Indifferent r y z) : Indifferent r x z :=
  ⟨ht x y z hxy.1 hyz.1, ht z y x hyz.2 hxy.2⟩

/-- The first-factor independence condition transports both directions of indifference. -/
theorem threeFactor_first_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (a a' : A) (b b' : B) (c c' : C) :
    Indifferent r (a, b, c) (a, b', c') ↔ Indifferent r (a', b, c) (a', b', c') :=
  and_congr (hi.1 a a' b b' c c') (hi.1 a a' b' b c' c)

/-- The second-factor independence condition transports indifference. -/
theorem threeFactor_second_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (b b' : B) (a a' : A) (c c' : C) :
    Indifferent r (a, b, c) (a', b, c') ↔ Indifferent r (a, b', c) (a', b', c') :=
  and_congr (hi.2.1 b b' a a' c c') (hi.2.1 b b' a' a c' c)

/-- The third-factor independence condition transports indifference. -/
theorem threeFactor_third_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (c c' : C) (a a' : A) (b b' : B) :
    Indifferent r (a, b, c) (a', b', c) ↔ Indifferent r (a, b, c') (a', b', c') :=
  and_congr (hi.2.2 c c' a a' b b') (hi.2.2 c c' a' a b' b)

/-- Debreu's third-factor hexagon: a compensating third coordinate closes the indifference chain. -/
theorem third_factor_hexagon {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (ht : TransitivePref r)
    (hi : ThreeFactorIndependent r) (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B) (c c' : C)
    (hab : Indifferent r (a₂, b₁, c) (a₁, b₂, c))
    (hcd : Indifferent r (a₃, b₁, c) (a₁, b₃, c))
    (hp : Indifferent r (a₁, b₁, c') (a₂, b₁, c)) :
    Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  have hpb := indifferent_transitive ht hp hab
  have hqe := (threeFactor_first_indifferent hi a₁ a₃ b₁ b₂ c' c).mp hpb
  have hrf := (threeFactor_second_indifferent hi b₁ b₃ a₁ a₂ c' c).mp hp
  have hqr := (threeFactor_third_indifferent hi c c' a₃ a₁ b₁ b₃).mp hcd
  exact indifferent_transitive ht ⟨hqe.2, hqe.1⟩ (indifferent_transitive ht hqr hrf)

/-- An interior rank in a connected third factor can compensate every sufficiently nearby pair. -/
theorem third_factor_local_compensation {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (a : A) (b : B) (c cLow cHigh : C)
    (hlo : Strict r (a, b, c) (a, b, cLow)) (hhi : Strict r (a, b, cHigh) (a, b, c)) :
    ∃ U : Set (A × B), IsOpen U ∧ (a, b) ∈ U ∧
      ∀ p ∈ U, ∃ d, Indifferent r (a, b, d) (p.1, p.2, c) := by
  let f : A × B → A × B × C := fun p => (p.1, p.2, c)
  have hf : Continuous f := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let U := f ⁻¹' (StrictlyBetterThan r (a, b, cLow) ∩ StrictlyWorseThan r (a, b, cHigh))
  have ho := continuousPreference_openStrictContours hc
  refine ⟨U, ((ho (a, b, cLow)).1.inter (ho (a, b, cHigh)).2).preimage hf,
    ⟨hlo, hhi⟩, ?_⟩
  intro p hp
  exact indifference_on_connected_image hr hc (fun d => (a, b, d))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (p.1, p.2, c) hp.2.1 hp.1.1

/-- Continuity and the third-factor bracket turn the algebraic hexagon into local cancellation. -/
theorem third_factor_local_hexagon {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hi : ThreeFactorIndependent r)
    (a₁ : A) (b₁ : B) (c cLow cHigh : C)
    (hlo : Strict r (a₁, b₁, c) (a₁, b₁, cLow))
    (hhi : Strict r (a₁, b₁, cHigh) (a₁, b₁, c)) :
    ∃ U : Set (A × B), IsOpen U ∧ (a₁, b₁) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, b₁) ∈ U →
        Indifferent r (a₂, b₁, c) (a₁, b₂, c) →
        Indifferent r (a₃, b₁, c) (a₁, b₃, c) →
        Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨U, hU, hp, hcomp⟩ := third_factor_local_compensation hr hc a₁ b₁ c cLow cHigh hlo hhi
  refine ⟨U, hU, hp, ?_⟩
  intro a₂ a₃ b₂ b₃ hmem hab hcd
  obtain ⟨c', hc'⟩ := hcomp (a₂, b₁) hmem
  exact third_factor_hexagon hr.2 hi a₁ a₂ a₃ b₁ b₂ b₃ c c' hab hcd hc'

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Reduction to continuous increasing utility on real intervals

Preparation for Kreps I, Proposition 2.14. The baseline construction turns
connected commodity blocks into real intervals and preserves strong
separability. Its aggregator is jointly continuous and strictly increasing.
Every baseline axis is normalized to the same original utility scale.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}

/-- The utility score of each commodity block at a common reference bundle. -/
def BaselineScores (u : (∀ i, B i) → ℝ) (z : ∀ i, B i) (i : I) (a : B i) : ℝ :=
  BaselineSubutility (fun p : BlockBundle B Unit => u p.1) (z, ()) i a

/-- The exact utility aggregator on the attained real block-score ranges. -/
noncomputable def ScoreAggregator (u : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (q : ∀ i, Set.range (BaselineScores u z i)) : ℝ :=
  SubutilityAggregator (fun p : BlockBundle B Unit => u p.1) (BaselineScores u z) (q, ())

/-- Every block's reference score equals the reference bundle's overall utility. -/
theorem baselineScores_reference (u : (∀ i, B i) → ℝ) (z : ∀ i, B i) (i : I) :
    BaselineScores u z i (z i) = u z := by
  simp only [BaselineScores, BaselineSubutility, ReplaceBlock, Function.update_eq_self]

/-- The baseline block scores are continuous. -/
theorem baselineScores_continuous [∀ i, TopologicalSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hc : Continuous u) (z : ∀ i, B i) (i : I) :
    Continuous (BaselineScores u z i) :=
  baselineSubutility_continuous (hc.comp continuous_fst) (z, ()) i

/-- Each connected commodity block is replaced by a real interval. -/
theorem baselineScores_ordConnected [∀ i, TopologicalSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hc : Continuous u) (z : ∀ i, B i) (i : I)
    [PreconnectedSpace (B i)] : Set.OrdConnected (Set.range (BaselineScores u z i)) :=
  (isPreconnected_range (baselineScores_continuous hc z i)).ordConnected

/-- Strong separability gives an exact factorization through the scalar scores. -/
theorem scoreAggregator_factors [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z x : ∀ i, B i) :
    u x = ScoreAggregator u z (BlockScores (BaselineScores u z) x) :=
  subutilityAggregator_factors (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs)
    (z, ()) (x, ())

/-- The scalar-score aggregator is strictly increasing. -/
theorem scoreAggregator_strictMono [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) : StrictMono (ScoreAggregator u z) :=
  subutilityAggregator_increasing (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs) (z, ()) ()

/-- The scalar-score aggregator is jointly continuous on its finite interval product. -/
theorem scoreAggregator_continuous [Finite I] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) :
    Continuous (ScoreAggregator u z) := by
  let : ∀ i, Set.OrdConnected (Set.range (BaselineScores u z i)) :=
    fun i => baselineScores_ordConnected hc z i
  apply finiteProductMonotone_continuous (scoreAggregator_strictMono hu hs z).monotone
  intro q i
  exact subutilityAggregator_coordinate_continuous (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs) (hc.comp continuous_fst) (z, ()) q () i

/-- Representative selection respects a partition into a set of coordinates and its complement. -/
theorem scoreRepresentatives_piecewise (w : ∀ i, B i → ℝ) (s : Finset I)
    (p q : ∀ i, Set.range (w i)) :
    (fun i => ScoreRepresentative w i (s.piecewise p q i)) =
      s.piecewise (fun i => ScoreRepresentative w i (p i))
        (fun i => ScoreRepresentative w i (q i)) := by
  funext i
  by_cases hi : i ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- Strong separability survives the reduction to scalar block scores. -/
theorem scoreAggregator_stronglySeparable {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) :
    StronglySeparable (UtilityPref (ScoreAggregator u z)) := by
  intro s a b p q
  unfold UtilityPref ScoreAggregator SubutilityAggregator
  simp only [scoreRepresentatives_piecewise]
  rw [← hu, ← hu]
  exact hs s _ _ _ _

/-- Along any reference axis, the aggregator equals the numerical score on that axis. -/
theorem scoreAggregator_reference_axis [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I)
    (t : Set.range (BaselineScores u z i)) :
    ScoreAggregator u z (Function.update (BlockScores (BaselineScores u z) z) i t) = t.val := by
  obtain ⟨a, ha⟩ := t.property
  have ht : (⟨BaselineScores u z i a, a, rfl⟩ : Set.range (BaselineScores u z i)) = t :=
    Subtype.ext ha
  have hf := scoreAggregator_factors hu hs z (Function.update z i a)
  rw [blockScores_update, ht] at hf
  exact hf.symm.trans ha

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# From pair transfers to a finite additive representation

Preparation for Kreps I, Proposition 2.14. A strictly increasing utility on a
finite interval product is represented by the coordinate sum whenever its
two-coordinate sum-preserving transfers leave utility unchanged. Convex
interpolation supplies the comparison step after the finite transfer argument.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] {S : I → Set ℝ}
variable [∀ i, Set.OrdConnected (S i)]

/-- A smaller total score can be attained at a bundle coordinatewise below the larger one. -/
theorem exists_le_bundle_with_sum (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val ≤ ∑ i, (y i).val) :
    ∃ z : ∀ i, S i, z ≤ y ∧ ∑ i, (z i).val = ∑ i, (x i).val := by
  let m : ∀ i, S i := fun i => min (x i) (y i)
  have hmx : ∑ i, (m i).val ≤ ∑ i, (x i).val :=
    Finset.sum_le_sum (fun i _ => min_le_left _ _)
  have hmy (i : I) : (m i).val ≤ (y i).val := min_le_right _ _
  by_cases he : ∑ i, (y i).val = ∑ i, (m i).val
  · exact ⟨y, le_rfl, le_antisymm (he ▸ hmx) hxy⟩
  · have hpos : 0 < (∑ i, (y i).val) - ∑ i, (m i).val := by
      have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmy i)
      exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm he))
    let θ := ((∑ i, (x i).val) - ∑ i, (m i).val) /
      ((∑ i, (y i).val) - ∑ i, (m i).val)
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hmx) hpos.le
    have hθ1 : θ ≤ 1 := (div_le_one hpos).mpr (by linarith)
    let z : ∀ i, S i := fun i => ⟨(1 - θ) * (m i).val + θ * (y i).val,
      (show Set.OrdConnected (S i) from inferInstance).out (m i).property (y i).property
        ⟨by nlinarith [hmy i], by nlinarith [hmy i]⟩⟩
    refine ⟨z, ?_, ?_⟩
    · intro i
      change (1 - θ) * (m i).val + θ * (y i).val ≤ (y i).val
      nlinarith [hmy i]
    · change (∑ i, ((1 - θ) * (m i).val + θ * (y i).val)) = _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hmul : θ * ((∑ i, (y i).val) - ∑ i, (m i).val) =
          (∑ i, (x i).val) - ∑ i, (m i).val := div_mul_cancel₀ _ hpos.ne'
      nlinarith

/-- Strict comparison of total scores gives strict utility comparison. -/
theorem pairSumInvariant_lt_of_sum_lt [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val < ∑ i, (y i).val) : F x < F y := by
  obtain ⟨z, hzy, hSum⟩ := exists_le_bundle_with_sum x y hxy.le
  have hne : z ≠ y := by
    intro h
    rw [h] at hSum
    exact hxy.ne hSum.symm
  have he := pairSumInvariant_eq_of_sum_eq hF x z hSum.symm
  rw [he]
  exact hm (lt_of_le_of_ne hzy hne)

/-- Every comparison is determined by the sum of the interval coordinates. -/
theorem pairSumInvariant_comparison [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) (x y : ∀ i, S i) :
    F x ≤ F y ↔ (∑ i, (x i).val) ≤ ∑ i, (y i).val := by
  constructor
  · intro h
    by_contra hnot
    exact (not_lt_of_ge h) (pairSumInvariant_lt_of_sum_lt hF hm y x (lt_of_not_ge hnot))
  · intro h
    rcases h.eq_or_lt with he | hl
    · exact (pairSumInvariant_eq_of_sum_eq hF x y he).le
    · exact (pairSumInvariant_lt_of_sum_lt hF hm x y hl).le

/-- Pair-transfer invariance gives the finite additive utility representation. -/
theorem pairSumInvariant_represents [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) :
    Represents (AdditiveUtility (fun i (x : S i) => x.val)) (UtilityPref F) := by
  intro x y
  exact pairSumInvariant_comparison hF hm y x

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Affine calibration on real coordinate domains

The chart calibration lemmas are expressed for ambient real functions on
interval domains. This matches the coordinate atlas used to extend the local
additive scales in Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

/-- A nonempty open real set contains a strictly ordered pair. -/
theorem open_real_set_has_pair {S : Set ℝ} (hS : IsOpen S) {x : ℝ} (hx : x ∈ S) :
    ∃ a ∈ S, ∃ b ∈ S, a < b := by
  obtain ⟨b, hxb, hb⟩ := exists_Ico_subset_of_mem_nhds (hS.mem_nhds hx) (exists_gt x)
  refine ⟨x, hx, (x + b) / 2, hb ⟨by linarith, by linarith⟩, by linarith⟩

/-- Positive affine uniqueness for ambient scales restricted to two real intervals. -/
theorem pair_chart_positive_affine_unique_on {S T : Set ℝ} (hS : S.OrdConnected)
    (hT : T.OrdConnected) {w v w' v' : ℝ → ℝ}
    (hw : ContinuousOn w S) (hv : ContinuousOn v S)
    (hw' : ContinuousOn w' T) (hv' : ContinuousOn v' T)
    (hwm : StrictMonoOn w S) (hvm : StrictMonoOn v S)
    (hwm' : StrictMonoOn w' T) (hvm' : StrictMonoOn v' T)
    (hp : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
      w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d) :
    ∃ slope β γ : ℝ, 0 < slope ∧ (∀ x ∈ S, v x = slope * w x + β) ∧
      ∀ y ∈ T, v' y = slope * w' y + γ := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hT.isPreconnected
  obtain ⟨slope, β, γ, hpos, hf, hg⟩ := pair_chart_positive_affine_unique
    (continuousOn_iff_continuous_domRestrict.mp hw) (continuousOn_iff_continuous_domRestrict.mp hv)
    (continuousOn_iff_continuous_domRestrict.mp hw')
    (continuousOn_iff_continuous_domRestrict.mp hv')
    (fun x y hxy => hwm x.property y.property hxy)
    (fun x y hxy => hvm x.property y.property hxy)
    (fun x y hxy => hwm' x.property y.property hxy)
    (fun x y hxy => hvm' x.property y.property hxy)
    (fun x x' y y' => hp x.val x.property x'.val x'.property y.val y.property y'.val y'.property)
    (show (⟨a, ha⟩ : S) < ⟨b, hb⟩ from hab) (show (⟨c, hc⟩ : T) < ⟨d, hd⟩ from hcd)
  exact ⟨slope, β, γ, hpos, fun x hx => hf ⟨x, hx⟩, fun y hy => hg ⟨y, hy⟩⟩

/-- Fixing a companion increment forces translation transitions on two real intervals. -/
theorem pair_chart_translation_on {S T : Set ℝ} (hS : S.OrdConnected)
    (hT : T.OrdConnected) {w v w' v' : ℝ → ℝ}
    (hw : ContinuousOn w S) (hv : ContinuousOn v S)
    (hw' : ContinuousOn w' T) (hv' : ContinuousOn v' T)
    (hwm : StrictMonoOn w S) (hvm : StrictMonoOn v S)
    (hwm' : StrictMonoOn w' T) (hvm' : StrictMonoOn v' T)
    (hp : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ T, ∀ y' ∈ T,
      w x + w' y = w x' + w' y' → v x + v' y = v x' + v' y')
    {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hc : c ∈ T) (hd : d ∈ T) (hcd : c < d)
    (hunit : v' d - v' c = w' d - w' c) :
    ∃ β γ : ℝ, (∀ x ∈ S, v x = w x + β) ∧ ∀ y ∈ T, v' y = w' y + γ := by
  obtain ⟨slope, β, γ, _, hf, hg⟩ := pair_chart_positive_affine_unique_on hS hT hw hv hw' hv'
    hwm hvm hwm' hvm' hp ha hb hab hc hd hcd
  have hpc := hg c hc
  have hpd := hg d hd
  have hlt := hwm' hc hd hcd
  have hscale : slope = 1 := by nlinarith
  exact ⟨β, γ, fun x hx => by simpa only [hscale, one_mul] using hf x hx,
    fun y hy => by simpa only [hscale, one_mul] using hg y hy⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive representation on full interval products

The interior of each nondegenerate score interval is dense. Continuous strictly
increasing extensions of the interior coordinate scales therefore represent the
original utility on the full product, including attained endpoints.
-/

namespace Kreps.PreferenceProperties

/-- A finite sum of strictly increasing coordinate scales is strictly increasing. -/
theorem additiveUtility_strictMono {I : Type*} [Fintype I] {B : I → Type*}
    [∀ i, LinearOrder (B i)] {g : ∀ i, B i → ℝ} (hg : ∀ i, StrictMono (g i)) :
    StrictMono (AdditiveUtility g) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := not_forall.mp (not_le_of_gt hxy)
  apply Finset.sum_lt_sum
  · intro j _
    exact (hg j).monotone (hxy.le j)
  · exact ⟨i, Finset.mem_univ i, hg i (lt_of_not_ge hi)⟩

/-- Interior additive comparisons extend to all endpoints once the scales are continuous. -/
theorem additive_comparison_of_interior {I : Type*} [Fintype I] {S : I → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hn : ∀ i, (interior (S i)).Nonempty)
    {u : (∀ i, S i) → ℝ} (hu : Continuous u) (hum : StrictMono u)
    {g : ∀ i, S i → ℝ} (hg : ∀ i, Continuous (g i)) (hgm : ∀ i, StrictMono (g i))
    (hr : ∀ x y : ∀ i, interior (S i),
      u (fun i => Set.inclusion interior_subset (x i)) ≤
        u (fun i => Set.inclusion interior_subset (y i)) ↔
      (∑ i, g i (Set.inclusion interior_subset (x i))) ≤
        ∑ i, g i (Set.inclusion interior_subset (y i))) :
    Represents (AdditiveUtility g) (UtilityPref u) := by
  let : ∀ i, Fact (S i).OrdConnected := fun i => ⟨hS i⟩
  let D : Set (∀ i, S i) := Set.pi Set.univ (fun i => {x : S i | x.val ∈ interior (S i)})
  have hD : Dense D := dense_pi Set.univ (fun i _ => interval_interior_dense (hS i) (hn i))
  have hlocal : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ AdditiveUtility g x ≤ AdditiveUtility g y := by
    intro x hx y hy
    exact hr (fun i => ⟨(x i).val, hx i (Set.mem_univ i)⟩)
      (fun i => ⟨(y i).val, hy i (Set.mem_univ i)⟩)
  have hglobal := dense_product_comparison hD hu (additiveUtility_continuous hg)
    hum (additiveUtility_strictMono hgm) hlocal
  intro x y
  exact hglobal y x

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Removing constant commodity factors

Deleting singleton factors preserves the order, topology and strong separability
of a product. Additive coordinate utilities on the remaining factors extend by
zero on every deleted factor.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*} (P : I → Prop)

/-- Insert a fixed baseline at each inactive coordinate. -/
noncomputable def ActiveCoordinateExtend (z : ∀ i, B i) (x : ∀ i : Subtype P, B i.val) :
    ∀ i, B i := by
  classical
  exact fun i => if h : P i then x ⟨i, h⟩ else z i

/-- Restrict a bundle to its active coordinates. -/
def ActiveCoordinateRestrict (x : ∀ i, B i) : ∀ i : Subtype P, B i.val := fun i => x i.val

/-- Extension leaves each active coordinate unchanged. -/
@[simp] theorem activeCoordinateExtend_active (z : ∀ i, B i)
    (x : ∀ i : Subtype P, B i.val) (i : Subtype P) :
    ActiveCoordinateExtend P z x i.val = x i := by
  simp only [ActiveCoordinateExtend, dite_eq_left i.property]

/-- Restriction recovers an extended active bundle. -/
@[simp] theorem activeCoordinateRestrict_extend (z : ∀ i, B i)
    (x : ∀ i : Subtype P, B i.val) :
    ActiveCoordinateRestrict P (ActiveCoordinateExtend P z x) = x := by
  funext i
  exact activeCoordinateExtend_active P z x i

/-- Singleton inactive factors make extension recover every original bundle. -/
@[simp] theorem activeCoordinateExtend_restrict (z x : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) :
    ActiveCoordinateExtend P z (ActiveCoordinateRestrict P x) = x := by
  classical
  funext i
  by_cases hi : P i
  · simp only [ActiveCoordinateExtend, dite_eq_left hi, ActiveCoordinateRestrict]
  · simp only [ActiveCoordinateExtend, dite_eq_right hi]
    exact (htriv i hi).elim _ _

/-- Extension by constant coordinates is continuous. -/
theorem activeCoordinateExtend_continuous [∀ i, TopologicalSpace (B i)] (z : ∀ i, B i) :
    Continuous (ActiveCoordinateExtend P z) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : P i
  · simpa only [ActiveCoordinateExtend, dite_eq_left hi] using
      continuous_apply (⟨i, hi⟩ : Subtype P)
  · simpa only [ActiveCoordinateExtend, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : ∀ j : Subtype P, B j.val => z i))

/-- Deleting singleton factors identifies the two product orders. -/
noncomputable def ActiveCoordinateOrderIso [∀ i, PartialOrder (B i)] (z : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) :
    (∀ i : Subtype P, B i.val) ≃o (∀ i, B i) where
  toFun := ActiveCoordinateExtend P z
  invFun := ActiveCoordinateRestrict P
  left_inv := activeCoordinateRestrict_extend P z
  right_inv := fun x => activeCoordinateExtend_restrict P z x htriv
  map_rel_iff' := by
    classical
    intro x y
    change (∀ i, ActiveCoordinateExtend P z x i ≤ ActiveCoordinateExtend P z y i) ↔
      (∀ i, x i ≤ y i)
    constructor
    · intro h i
      simpa only [activeCoordinateExtend_active] using h i.val
    · intro h i
      by_cases hi : P i
      · simpa only [ActiveCoordinateExtend, dite_eq_left hi] using h ⟨i, hi⟩
      · simp only [ActiveCoordinateExtend, dite_eq_right hi, le_refl]

/-- Extension commutes with replacing an arbitrary finite collection of active factors. -/
theorem activeCoordinateExtend_piecewise [DecidableEq I] (z : ∀ i, B i)
    (s : Finset (Subtype P)) (x y : ∀ i : Subtype P, B i.val) :
    ActiveCoordinateExtend P z (s.piecewise x y) =
      (s.image Subtype.val).piecewise (ActiveCoordinateExtend P z x)
        (ActiveCoordinateExtend P z y) := by
  classical
  funext i
  by_cases hi : P i
  · have hmem : i ∈ s.image Subtype.val ↔ (⟨i, hi⟩ : Subtype P) ∈ s := by
      constructor
      · intro h
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
        have hji : j = ⟨i, hi⟩ := Subtype.ext he
        simpa only [hji] using hj
      · exact Finset.mem_image_of_mem Subtype.val
    by_cases hs : (⟨i, hi⟩ : Subtype P) ∈ s
    · simp only [ActiveCoordinateExtend, dite_eq_left hi, Finset.piecewise,
        ite_eq_left hs, ite_eq_left (hmem.mpr hs)]
    · simp only [ActiveCoordinateExtend, dite_eq_left hi, Finset.piecewise,
        ite_eq_right hs, ite_eq_right (mt hmem.mp hs)]
  · have hmem : i ∉ s.image Subtype.val := by
      intro h
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp h
      exact hi (he ▸ j.property)
    simp only [ActiveCoordinateExtend, dite_eq_right hi, Finset.piecewise, ite_eq_right hmem]

/-- Strong separability restricts to the active commodity factors. -/
theorem stronglySeparable_activeCoordinates [DecidableEq I]
    {V : (∀ i, B i) → ℝ} (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) :
    StronglySeparable (UtilityPref (fun x => V (ActiveCoordinateExtend P z x))) := by
  intro s a b x y
  simp only [UtilityPref, activeCoordinateExtend_piecewise]
  exact hs (s.image Subtype.val) _ _ _ _

/-- Extend additive coordinate utilities by zero on inactive factors. -/
noncomputable def ActiveCoordinateUtility (w : ∀ i : Subtype P, B i.val → ℝ)
    (i : I) (x : B i) : ℝ := by
  classical
  exact if h : P i then w ⟨i, h⟩ x else 0

/-- Extending by zero does not change the active coordinates' utility sum. -/
theorem additiveUtility_activeCoordinates [Fintype I] [Fintype (Subtype P)]
    (w : ∀ i : Subtype P, B i.val → ℝ) (x : ∀ i, B i) :
    AdditiveUtility (ActiveCoordinateUtility P w) x =
      AdditiveUtility w (ActiveCoordinateRestrict P x) := by
  classical
  unfold AdditiveUtility
  calc
    _ = ∑ i ∈ Finset.univ.filter P, ActiveCoordinateUtility P w i (x i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hp : ¬ P i := fun hp => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      simp only [ActiveCoordinateUtility, dite_eq_right hp]
    _ = ∑ i : Subtype P, ActiveCoordinateUtility P w i.val (x i.val) :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [ActiveCoordinateUtility, dite_eq_left i.property, ActiveCoordinateRestrict]

/-- The inactive zero functions and the active continuous functions are all continuous. -/
theorem activeCoordinateUtility_continuous [∀ i, TopologicalSpace (B i)]
    {w : ∀ i : Subtype P, B i.val → ℝ} (hw : ∀ i, Continuous (w i)) (i : I) :
    Continuous (ActiveCoordinateUtility P w i) := by
  classical
  change Continuous (fun x => ActiveCoordinateUtility P w i x)
  by_cases hi : P i
  · simpa only [ActiveCoordinateUtility, dite_eq_left hi] using hw ⟨i, hi⟩
  · simpa only [ActiveCoordinateUtility, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : B i => (0 : ℝ)))

/-- Strict increase is retained, including its vacuous meaning on singleton factors. -/
theorem activeCoordinateUtility_strictMono [∀ i, PartialOrder (B i)]
    {w : ∀ i : Subtype P, B i.val → ℝ} (hw : ∀ i, StrictMono (w i))
    (htriv : ∀ i, ¬ P i → Subsingleton (B i)) (i : I) :
    StrictMono (ActiveCoordinateUtility P w i) := by
  classical
  change StrictMono (fun x => ActiveCoordinateUtility P w i x)
  by_cases hi : P i
  · simpa only [ActiveCoordinateUtility, dite_eq_left hi] using hw ⟨i, hi⟩
  · intro a b hab
    exact False.elim (hab.ne ((htriv i hi).elim a b))

/-- An active additive representation represents the full product after zero extension. -/
theorem represents_activeCoordinates [Fintype I] [Fintype (Subtype P)]
    {V : (∀ i, B i) → ℝ} (z : ∀ i, B i)
    (htriv : ∀ i, ¬ P i → Subsingleton (B i))
    {w : ∀ i : Subtype P, B i.val → ℝ}
    (hw : Represents (AdditiveUtility w)
      (UtilityPref (fun x => V (ActiveCoordinateExtend P z x)))) :
    Represents (AdditiveUtility (ActiveCoordinateUtility P w)) (UtilityPref V) := by
  intro x y
  have hh := hw (ActiveCoordinateRestrict P x) (ActiveCoordinateRestrict P y)
  simp only [UtilityPref, activeCoordinateExtend_restrict P z _ htriv] at hh
  simpa only [UtilityPref, additiveUtility_activeCoordinates] using hh

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Restricting scalar preferences to interval interiors

Nondegenerate real intervals have nonempty interiors. Coordinatewise restriction
preserves strong separability, continuity and strict monotonicity, supplying the
open-domain hypotheses used in the additive-existence construction.
-/

namespace Kreps.PreferenceProperties

/-- A nondegenerate real interval contains an interior point. -/
theorem nontrivial_interval_interior_nonempty {S : Set ℝ} [Nontrivial S]
    (hS : S.OrdConnected) : (interior S).Nonempty := by
  have hnt : S.Nontrivial := Set.nontrivial_coe_sort.mp inferInstance
  obtain ⟨a, ha, b, hb, hab⟩ := hnt.exists_lt
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (Ioo_mem_nhds hac hcb)
    (fun _ hx => hS.out ha hb ⟨hx.1.le, hx.2.le⟩)

/-- Coordinatewise maps commute with replacing a finite collection of blocks. -/
theorem coordinateMap_piecewise {I : Type*} [DecidableEq I] {A B : I → Type*}
    (f : ∀ i, A i → B i) (s : Finset I) (x y : ∀ i, A i) :
    (fun i => f i (s.piecewise x y i)) =
      s.piecewise (fun i => f i (x i)) (fun i => f i (y i)) := by
  funext i
  by_cases hi : i ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- Strong separability is preserved by arbitrary coordinatewise restriction maps. -/
theorem stronglySeparable_coordinate_pullback {I : Type*} [DecidableEq I]
    {A B : I → Type*} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hr : StronglySeparable r) (f : ∀ i, A i → B i) :
    StronglySeparable (fun x y => r (fun i => f i (x i)) (fun i => f i (y i))) := by
  intro s x y z t
  simp only [coordinateMap_piecewise]
  exact hr s _ _ _ _

/-- Include every interior coordinate in its full scalar interval. -/
def InteriorScalarInclusion {I : Type*} {S : I → Set ℝ}
    (x : ∀ i, interior (S i)) : ∀ i, S i :=
  fun i => Set.inclusion interior_subset (x i)

/-- The coordinatewise interior inclusion is continuous. -/
theorem interiorScalarInclusion_continuous {I : Type*} {S : I → Set ℝ} :
    Continuous (@InteriorScalarInclusion I S) :=
  continuous_pi (fun i => (continuous_inclusion interior_subset).comp (continuous_apply i))

/-- The coordinatewise interior inclusion preserves the strict product order. -/
theorem interiorScalarInclusion_strictMono {I : Type*} {S : I → Set ℝ} :
    StrictMono (@InteriorScalarInclusion I S) := by
  intro x y hxy
  apply lt_iff_le_not_ge.mpr
  refine ⟨fun i => hxy.le i, ?_⟩
  intro h
  exact (not_le_of_gt hxy) (fun i => h i)

/-- Strong separability survives restricting all scalar intervals to their interiors. -/
theorem interiorScalarInclusion_stronglySeparable {I : Type*} [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} (hs : StronglySeparable (UtilityPref V)) :
    StronglySeparable (UtilityPref (V ∘ InteriorScalarInclusion)) :=
  stronglySeparable_coordinate_pullback hs (fun _ => Set.inclusion interior_subset)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. Countable dense ranks and their rational
completion give a continuous utility without any monotonicity assumption.
Open strict contours prove continuity at every bundle, including extreme ranks.
The proof works on any separable connected space and is specialized below to
every finite-dimensional nonnegative orthant, including dimension zero.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- A bounded representation attaining all interior rational values has no discontinuous gaps. -/
theorem continuous_of_dense_rational_range {u : X → ℝ} (hu : Represents u r)
    (hc : ContinuousPreference r) (hb : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hq : ∀ q : ℚ, 0 < q → q < 1 → ∃ x, u x = (q : ℝ)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change a < u x at hx
    by_cases ha : a < 0
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => ha.trans_le (hb y).1)
    · obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hx
      have hq0 : (0 : ℝ) < q := (le_of_not_gt ha).trans_lt haq
      have hq1 : (q : ℝ) < 1 := hqx.trans_le (hb x).2
      obtain ⟨z, hz⟩ := hq q (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      have hxz : Strict r x z := (strict_iff_utility_lt hu x z).mpr (hz.symm ▸ hqx)
      apply Filter.mem_of_superset ((ho z).1.mem_nhds hxz)
      intro y hy
      change a < u y
      have hzy := (strict_iff_utility_lt hu y z).mp hy
      rw [hz] at hzy
      exact haq.trans hzy
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change u x < a at hx
    by_cases ha : 1 < a
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => (hb y).2.trans_lt ha)
    · obtain ⟨q, hxq, hqa⟩ := exists_rat_btwn hx
      have hq0 : (0 : ℝ) < q := (hb x).1.trans_lt hxq
      have hq1 : (q : ℝ) < 1 := hqa.trans_le (le_of_not_gt ha)
      obtain ⟨z, hz⟩ := hq q (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      have hzx : Strict r z x := (strict_iff_utility_lt hu z x).mpr (hz.symm ▸ hxq)
      apply Filter.mem_of_superset ((ho z).2.mem_nhds hzx)
      intro y hy
      change u y < a
      have hyz := (strict_iff_utility_lt hu z y).mp hy
      rw [hz] at hyz
      exact hyz.trans hqa

/-- The completed rational-rank representation is continuous, even at its possible endpoints. -/
theorem rankCutUtility_continuous {v : X → ℝ} {D : Set X}
    (e : InteriorRankSet v D ≃o RationalUnit) (hs : StrictRankSeparator v D)
    (hv : Represents v r) (hc : ContinuousPreference r) : Continuous (RankCutUtility e) := by
  apply continuous_of_dense_rational_range (rankCutUtility_represents e hs hv) hc
    (fun x => ⟨rankCutUtility_nonneg e x, rankCutUtility_le_one e x⟩)
  intro q hq0 hq1
  exact rankCutUtility_attains_rationals e ⟨q, hq0, hq1⟩

/-- General Debreu representation on a connected separable domain, with a bounded utility. -/
theorem continuous_represents_of_continuous_connected [PreconnectedSpace X]
    [TopologicalSpace.SeparableSpace X] (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : X → ℝ, Represents u r ∧ Continuous u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ 1 := by
  obtain ⟨v, hv⟩ := represents_of_continuous_connected hr hc
  by_cases hn : ∃ x y, v x < v y
  · obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense X
    have hs := dense_strictRankSeparator hr hc hv hd
    obtain ⟨e⟩ := interiorRanks_orderIso hD hs hn
    exact ⟨RankCutUtility e, rankCutUtility_represents e hs hv,
      rankCutUtility_continuous e hs hv hc,
      fun x => ⟨rankCutUtility_nonneg e x, rankCutUtility_le_one e x⟩⟩
  · refine ⟨fun _ => 0, ?_, continuous_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
    intro x y
    exact iff_of_true ((hv x y).mpr (le_of_not_gt (fun h => hn ⟨x, y, h⟩))) le_rfl

/-- **Proposition 2.9:** the full equivalence, with no monotonicity hypothesis. -/
theorem proposition_2_9 (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u := by
  constructor
  · intro hc
    let : PreconnectedSpace (NonnegativeOrthant k) :=
      isPreconnected_iff_preconnectedSpace.mp
        (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
    obtain ⟨u, hu, hc', _⟩ := continuous_represents_of_continuous_connected hr hc
    exact ⟨u, hu, hc'⟩
  · rintro ⟨u, hu, hc⟩
    exact proposition_2_9_forward hu hc

/-- The same equivalence using the common-radius metric continuity convention. -/
theorem proposition_2_9_metric (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    MetricContinuousPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  continuousPreference_iff_metric.symm.trans (proposition_2_9 k hr)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# No concave representation of the split product preference

Kreps I, Problem 2.8a, second example. A direct Jensen argument avoids assuming
continuity at the boundary of the consumption domain. Bundles just to the right
of `(2,2)` outrank `(1,4)`, although `(2,2)` is strictly worse than `(1,4)`.
Expressing `(2,2)` as a mixture of such bundles and `(1,2)` contradicts concavity.
-/

namespace Kreps.PreferenceProperties

/-- The ordinal jump at the split level prevents every concave representation. -/
theorem splitProductPreference_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref SplitProductUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hconc⟩
  let p := PairBundle 2 2 (by norm_num) (by norm_num)
  let b := PairBundle 1 2 (by norm_num) (by norm_num)
  let q := PairBundle 1 4 (by norm_num) (by norm_num)
  have hbp : u b < u p := (strict_iff_utility_lt hu p b).mp (by
    norm_num [Strict, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle, p, b])
  have hpq : u p < u q := (strict_iff_utility_lt hu q p).mp (by
    norm_num [Strict, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle, q, p])
  have hden : 0 < u q - u b := sub_pos.mpr (hbp.trans hpq)
  have hratio0 : 0 < (u p - u b) / (u q - u b) := div_pos (sub_pos.mpr hbp) hden
  have hratio1 : (u p - u b) / (u q - u b) < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  obtain ⟨t, ht, ht1⟩ := exists_between hratio1
  have ht0 : 0 < t := hratio0.trans ht
  have hquantity : 2 < (1 + t) / t := (lt_div_iff₀ ht0).mpr (by linarith)
  let z := PairBundle ((1 + t) / t) 2 (by linarith) (by norm_num)
  have hprod : 4 < TwoGoodProduct z := by
    change 4 < ((1 + t) / t) * 2
    linarith
  have hqz : UtilityPref SplitProductUtility z q := by
    change SplitProductUtility q ≤ SplitProductUtility z
    rw [splitProductUtility_above hprod]
    norm_num [q, SplitProductUtility, TwoGoodProduct, PairBundle]
    change 5 ≤ TwoGoodProduct z + 1
    linarith
  have huqz : u q ≤ u z := (hu z q).mp hqz
  have hm : Mix (convex_Ici (0 : Fin 2 → ℝ)) z b t ⟨ht0.le, ht1.le⟩ = p := by
    apply Subtype.ext
    funext j
    fin_cases j
    · change t * ((1 + t) / t) + (1 - t) * 1 = 2
      field_simp
      ring
    · change t * 2 + (1 - t) * 2 = 2
      ring
  have hj := hconc z b t ⟨ht0.le, ht1.le⟩
  rw [hm] at hj
  have htineq := (div_lt_iff₀ hden).mp ht
  have hmul := mul_le_mul_of_nonneg_left huqz ht0.le
  nlinarith

/-- **Problem 2.8a, second example:** semi-strict convexity without concave representability. -/
theorem problem_2_8a_second :
    Rational (UtilityPref SplitProductUtility) ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref SplitProductUtility) ∧
      SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
        (UtilityPref SplitProductUtility) ∧
      ¬ ContinuousPreference (UtilityPref SplitProductUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref SplitProductUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _, splitProductPreference_convex, splitProductPreference_semiStrict,
    splitProductPreference_not_continuous, splitProductPreference_no_concave_representation⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The nonexistence proof in Problem 2.8b

Indifference along rays forces a concave representation to retain at least half
an increment when its rank interval contracts by three sevenths. Iterating this
inequality contradicts the concave secant bound on the commodity axis: after
rescaling, the bound tends to zero at the geometric rate `(6/7)^n`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Equal values of the displayed utility give equal values in every representation. -/
theorem ratioSum_rep_eq_of_value_eq {u : NonnegativeOrthant 2 → ℝ}
    (hu : Represents u (UtilityPref RatioSumUtility)) {x y : NonnegativeOrthant 2}
    (he : RatioSumUtility x = RatioSumUtility y) : u x = u y := by
  apply le_antisymm
  · exact (hu y x).mp (by change RatioSumUtility x ≤ RatioSumUtility y; rw [he])
  · exact (hu x y).mp (by change RatioSumUtility y ≤ RatioSumUtility x; rw [he])

/-- Equal-weight physical mixing imposes an excessive lower bound on rank increments. -/
theorem ratioSum_concave_increment {u : NonnegativeOrthant 2 → ℝ}
    (hu : Represents u (UtilityPref RatioSumUtility))
    (hc : ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 4) :
    (1 / 2) * (u (RatioAxisBundle (1 / 2 + δ)) - u (RatioAxisBundle (1 / 2))) ≤
      u (RatioAxisBundle (1 / 2 + (3 / 7) * δ)) - u (RatioAxisBundle (1 / 2)) := by
  have hq : u (RatioRayBundle δ hδ) = u (RatioAxisBundle (1 / 2 + δ)) :=
    ratioSum_rep_eq_of_value_eq hu ((ratioSumUtility_ray hδ hδ').trans
      (ratioSumUtility_axis (by positivity)).symm)
  have hm : u (Mix (convex_Ici (0 : Fin 2 → ℝ))
      (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ) (1 / 2) ⟨by norm_num, by norm_num⟩) =
      u (RatioAxisBundle (1 / 2 + (3 / 7) * δ)) :=
    ratioSum_rep_eq_of_value_eq hu ((ratioSumUtility_ray_mix hδ hδ').trans
      (ratioSumUtility_axis (by positivity)).symm)
  have hj := hc (RatioAxisBundle (1 / 2)) (RatioRayBundle δ hδ)
    (1 / 2) ⟨by norm_num, by norm_num⟩
  have hj' := hj.trans_eq hm
  rw [hq] at hj'
  linarith

/-- **Problem 2.8b:** no concave function can represent the ratio-and-sum preference. -/
theorem problem_2_8b_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref RatioSumUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hc⟩
  let g : ℝ → ℝ := fun t => u (RatioAxisBundle t)
  let d : ℕ → ℝ := fun n => (1 / 4) * (3 / 7 : ℝ) ^ n
  have hd (n : ℕ) : 0 < d n ∧ d n ≤ 1 / 4 := by
    have hp : 0 < (3 / 7 : ℝ) ^ n := pow_pos (by norm_num) n
    have hp' : (3 / 7 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [d]
    constructor <;> nlinarith
  have hdstep (n : ℕ) : d (n + 1) = (3 / 7) * d n := by
    dsimp [d]
    rw [pow_succ]
    ring
  have hlower (n : ℕ) : (1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2)) ≤
      g (1 / 2 + d n) - g (1 / 2) := by
    induction n with
    | zero => norm_num [d]
    | succ n ih =>
      have hr := ratioSum_concave_increment hu hc (hd n).1.le (hd n).2
      change (1 / 2) * (g (1 / 2 + d n) - g (1 / 2)) ≤
        g (1 / 2 + (3 / 7) * d n) - g (1 / 2) at hr
      rw [← hdstep n] at hr
      rw [pow_succ]
      nlinarith
  have hbound (n : ℕ) : (1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2)) ≤
      (3 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
    have hup := concaveUtility_ratioAxis_bound hc (hd n).1
    change g (1 / 2 + d n) - g (1 / 2) ≤ 2 * d n * (g (1 / 2) - g 0) at hup
    have hl := hlower n
    dsimp [d] at hup
    nlinarith
  have hscaled (n : ℕ) : g (3 / 4) - g (1 / 2) ≤
      (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
    calc
      g (3 / 4) - g (1 / 2) =
          (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * (g (3 / 4) - g (1 / 2))) := by
            rw [← mul_assoc, ← mul_pow]
            norm_num
      _ ≤ (2 : ℝ) ^ n * ((3 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2)) :=
        mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (by norm_num) n)
      _ = (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
  have hlim : Filter.Tendsto
      (fun n : ℕ => (6 / 7 : ℝ) ^ n * ((g (1 / 2) - g 0) / 2)) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 6 / 7)
        (by norm_num : (6 / 7 : ℝ) < 1)).mul_const ((g (1 / 2) - g 0) / 2)
  have hle : g (3 / 4) - g (1 / 2) ≤ 0 := ge_of_tendsto' hlim hscaled
  have hstrict : Strict (UtilityPref RatioSumUtility)
      (RatioAxisBundle (3 / 4)) (RatioAxisBundle (1 / 2)) := by
    change RatioSumUtility (RatioAxisBundle (1 / 2)) ≤
        RatioSumUtility (RatioAxisBundle (3 / 4)) ∧
      ¬ RatioSumUtility (RatioAxisBundle (3 / 4)) ≤ RatioSumUtility (RatioAxisBundle (1 / 2))
    rw [ratioSumUtility_axis (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ratioSumUtility_axis (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  have hlt := (strict_iff_utility_lt hu _ _).mp hstrict
  change g (1 / 2) < g (3 / 4) at hlt
  linarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Completing an assigned scale from a dense sample

Kreps I, Problem 2.14(f)-(g). Taking the supremum of the assigned ranks weakly
below a point extends the specified scale. Including best and worst ranks in the
sample ensures finite bounds at every point. Strict separation gives representation;
density of the assigned values removes numerical gaps and gives continuity.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- Every point lies between two sampled original ranks, with equality permitted. -/
def SampleBrackets (v : X → ℝ) (q : ℕ → X) : Prop :=
  ∀ x, ∃ i j, v (q i) ≤ v x ∧ v x ≤ v (q j)

/-- The sample contains a representative of each attained extreme rank. -/
def SampleContainsExtremes (v : X → ℝ) (q : ℕ → X) : Prop :=
  (∀ x, (∀ y, v x ≤ v y) → ∃ n, v (q n) = v x) ∧
    (∀ x, (∀ y, v y ≤ v x) → ∃ n, v (q n) = v x)

/-- Strict separation and the included extreme ranks supply finite brackets everywhere. -/
theorem sampleBrackets_of_extremes {v : X → ℝ} {q : ℕ → X}
    (hs : StrictRankSeparator v (Set.range q)) (he : SampleContainsExtremes v q) :
    SampleBrackets v q := by
  intro x
  have hlo : ∃ i, v (q i) ≤ v x := by
    by_cases h : ∃ y, v y < v x
    · obtain ⟨y, hy⟩ := h
      obtain ⟨z, ⟨i, rfl⟩, _, hix⟩ := hs y x hy
      exact ⟨i, hix.le⟩
    · have hmin : ∀ y, v x ≤ v y := fun y => le_of_not_gt (fun hy => h ⟨y, hy⟩)
      obtain ⟨i, hi⟩ := he.1 x hmin
      exact ⟨i, hi.le⟩
  have hhi : ∃ j, v x ≤ v (q j) := by
    by_cases h : ∃ y, v x < v y
    · obtain ⟨y, hy⟩ := h
      obtain ⟨z, ⟨j, rfl⟩, hxj, _⟩ := hs x y hy
      exact ⟨j, hxj.le⟩
    · have hmax : ∀ y, v y ≤ v x := fun y => le_of_not_gt (fun hy => h ⟨y, hy⟩)
      obtain ⟨j, hj⟩ := he.2 x hmax
      exact ⟨j, hj.ge⟩
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  exact ⟨i, j, hi, hj⟩

/-- Assigned values of sampled points no better than the given point. -/
def SampleRankCut (v : X → ℝ) (q : ℕ → X) (u : ℕ → ℝ) (x : X) : Set ℝ :=
  u '' {n | v (q n) ≤ v x}

/-- Complete the assigned scale by taking the supremum of each lower cut. -/
noncomputable def SampleRankExtension (v : X → ℝ) (q : ℕ → X) (u : ℕ → ℝ) (x : X) : ℝ :=
  sSup (SampleRankCut v q u x)

/-- A sampled lower bracket makes every cut nonempty. -/
theorem sampleRankCut_nonempty {v : X → ℝ} {q : ℕ → X} (u : ℕ → ℝ)
    (hb : SampleBrackets v q) (x : X) : (SampleRankCut v q u x).Nonempty := by
  obtain ⟨i, _, hi, _⟩ := hb x
  exact ⟨u i, i, hi, rfl⟩

/-- A sampled upper bracket bounds every assigned lower cut. -/
theorem sampleRankCut_bddAbove {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q) (x : X) :
    BddAbove (SampleRankCut v q u x) := by
  obtain ⟨_, j, _, hj⟩ := hb x
  refine ⟨u j, ?_⟩
  rintro a ⟨i, hi, rfl⟩
  exact (hu i j).mp (hi.trans hj)

/-- A sampled rank below the point bounds its extension from below. -/
theorem sampleRankExtension_lower {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x : X} {i : ℕ} (hi : v (q i) ≤ v x) : u i ≤ SampleRankExtension v q u x :=
  le_csSup (sampleRankCut_bddAbove hu hb x) ⟨i, hi, rfl⟩

/-- A sampled rank above the point bounds its extension from above. -/
theorem sampleRankExtension_upper {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x : X} {j : ℕ} (hj : v x ≤ v (q j)) : SampleRankExtension v q u x ≤ u j := by
  apply csSup_le (sampleRankCut_nonempty u hb x)
  rintro a ⟨i, hi, rfl⟩
  exact (hu i j).mp (hi.trans hj)

/-- The extension agrees with all of the prescribed sampled values. -/
theorem sampleRankExtension_at_sample {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q) (i : ℕ) :
    SampleRankExtension v q u (q i) = u i :=
  le_antisymm (sampleRankExtension_upper hu hb le_rfl)
    (sampleRankExtension_lower hu hb le_rfl)

/-- Inclusion of lower cuts preserves weak original rank comparisons. -/
theorem sampleRankExtension_mono {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x y : X} (hxy : v x ≤ v y) :
    SampleRankExtension v q u x ≤ SampleRankExtension v q u y := by
  apply csSup_le (sampleRankCut_nonempty u hb x)
  rintro a ⟨i, hi, rfl⟩
  exact sampleRankExtension_lower hu hb (hi.trans hxy)

/-- Two intermediate sampled ranks force a strict comparison of the completed values. -/
theorem sampleRankExtension_strict {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    (hs : StrictRankSeparator v (Set.range q)) {x y : X} (hxy : v x < v y) :
    SampleRankExtension v q u x < SampleRankExtension v q u y := by
  obtain ⟨a, ⟨i, rfl⟩, hxi, hiy⟩ := hs x y hxy
  obtain ⟨b, ⟨j, rfl⟩, hij, hjy⟩ := hs (q i) y hiy
  exact (sampleRankExtension_upper hu hb hxi.le).trans_lt
    (((rankPreserving_lt hu i j).mp hij).trans_le (sampleRankExtension_lower hu hb hjy.le))

/-- The extension represents the original preference on the entire domain. -/
theorem sampleRankExtension_represents {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    {r : X → X → Prop} (hv : Represents v r) (hu : RankPreserving (v ∘ q) u)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Represents (SampleRankExtension v q u) r := by
  intro x y
  constructor
  · exact fun hxy => sampleRankExtension_mono hu hb ((hv x y).mp hxy)
  · intro hxy
    by_contra h
    have hlt : v x < v y := lt_of_not_ge (fun hle => h ((hv x y).mpr hle))
    exact not_lt_of_ge hxy (sampleRankExtension_strict hu hb hs hlt)

/-- A represented continuous preference has continuous utility if its range has no open gaps. -/
theorem continuous_of_interval_closure_range [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r) (hc : ContinuousPreference r)
    (hgap : ∀ x y, Set.Icc (u x) (u y) ⊆ closure (Set.range u)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change a < u x at hx
    by_cases hall : ∀ y, a < u y
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · push Not at hall
      obtain ⟨y, hy⟩ := hall
      have hm : (a + u x) / 2 ∈ closure (Set.range u) :=
        hgap y x ⟨by linarith, by linarith⟩
      obtain ⟨_, ⟨haz, hzx⟩, z, rfl⟩ := mem_closure_iff.mp hm (Set.Ioo a (u x))
        isOpen_Ioo ⟨by linarith, by linarith⟩
      have hxz := (strict_iff_utility_lt hu x z).mpr hzx
      apply Filter.mem_of_superset ((ho z).1.mem_nhds hxz)
      intro w hw
      exact haz.trans ((strict_iff_utility_lt hu w z).mp hw)
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change u x < a at hx
    by_cases hall : ∀ y, u y < a
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · push Not at hall
      obtain ⟨y, hy⟩ := hall
      have hm : (u x + a) / 2 ∈ closure (Set.range u) :=
        hgap x y ⟨by linarith, by linarith⟩
      obtain ⟨_, ⟨hxz, hza⟩, z, rfl⟩ := mem_closure_iff.mp hm (Set.Ioo (u x) a)
        isOpen_Ioo ⟨by linarith, by linarith⟩
      have hzx := (strict_iff_utility_lt hu z x).mpr hxz
      apply Filter.mem_of_superset ((ho z).2.mem_nhds hzx)
      intro w hw
      exact ((strict_iff_utility_lt hu z w).mp hw).trans hza

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Topological foundations of the additive construction

Preparation for Kreps I, Proposition 2.14. A nontrivial connected third block
has an interior preference rank. Strong separability then gives local Thomsen
cancellation on a slice through the other two blocks. All hypotheses in this
step are derived from the original preference; no additive representation or
hexagon condition is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Restricting a rational preference through a map preserves rationality. -/
theorem rational_preference_pullback {X Y : Type*} {r : X → X → Prop}
    (hr : Rational r) (f : Y → X) : Rational (fun x y => r (f x) (f y)) :=
  ⟨fun x y => hr.1 (f x) (f y), fun x y z => hr.2 (f x) (f y) (f z)⟩

/-- A continuous parametrization preserves the joint openness of strict preference. -/
theorem continuousPreference_pullback {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {r : X → X → Prop} (hc : ContinuousPreference r) {f : Y → X} (hf : Continuous f) :
    ContinuousPreference (fun x y => r (f x) (f y)) := hc.preimage (hf.prodMap hf)

variable {I : Type*} [DecidableEq I] {B : I → Type*}

/-- Varying three coordinates is a continuous parametrization of the commodity product. -/
theorem threeCoordinateBundle_continuous [∀ i, TopologicalSpace (B i)]
    (z : ∀ i, B i) (i j l : I) :
    Continuous (fun p : B i × B j × B l =>
      ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2) :=
  ((continuous_const.update i continuous_fst).update j continuous_snd.fst).update l
    continuous_snd.snd

/-- Preference restricted to a three-coordinate slice. -/
def ThreeCoordinatePreference (r : (∀ i, B i) → (∀ i, B i) → Prop)
    (z : ∀ i, B i) (i j l : I) (p q : B i × B j × B l) : Prop :=
  r (ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2)
    (ThreeCoordinateBundle z i j l q.1 q.2.1 q.2.2)

/-- Connectedness gives an interior rank between any strict pair in the third factor. -/
theorem third_factor_interior_rank {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (a : A) (b : B) {cLow cHigh : C}
    (hstrict : Strict r (a, b, cHigh) (a, b, cLow)) :
    ∃ c, Strict r (a, b, c) (a, b, cLow) ∧ Strict r (a, b, cHigh) (a, b, c) := by
  have hf : Continuous (fun c : C => (a, b, c)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  obtain ⟨c, hhi, hlo⟩ := exists_strict_between
    (rational_preference_pullback hr (fun c => (a, b, c)))
    (continuousPreference_pullback hc hf) hstrict
  exact ⟨c, hlo, hhi⟩

/-- A nontrivial third factor supplies the interior rank needed for local cancellation. -/
theorem third_factor_local_hexagon_of_nontrivial {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hi : ThreeFactorIndependent r) (a₁ : A) (b₁ : B)
    (hnt : ∃ cHigh cLow, Strict r (a₁, b₁, cHigh) (a₁, b₁, cLow)) :
    ∃ c : C, ∃ U : Set (A × B), IsOpen U ∧ (a₁, b₁) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, b₁) ∈ U →
        Indifferent r (a₂, b₁, c) (a₁, b₂, c) →
        Indifferent r (a₃, b₁, c) (a₁, b₃, c) →
        Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨cHigh, cLow, hstrict⟩ := hnt
  obtain ⟨c, hlo, hhi⟩ := third_factor_interior_rank hr hc a₁ b₁ hstrict
  obtain ⟨U, hU, hp, hhex⟩ := third_factor_local_hexagon hr hc hi a₁ b₁ c cLow cHigh hlo hhi
  exact ⟨c, U, hU, hp, hhex⟩

/-- Strong separability, continuity and a connected nontrivial third block imply a local hexagon. -/
theorem stronglySeparable_local_hexagon [Finite I] [∀ i, TopologicalSpace (B i)]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StronglySeparable r)
    {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    [PreconnectedSpace (B l)] (hnt : NontrivialBlock r l) :
    ∃ z : ∀ i, B i, ∃ c : B l, ∃ U : Set (B i × B j), IsOpen U ∧ (z i, z j) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, z j) ∈ U →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₂, z j, c) (z i, b₂, c) →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₃, z j, c) (z i, b₃, c) →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨cHigh, cLow, z, hz⟩ := hnt
  have hr' : Rational (ThreeCoordinatePreference r z i j l) :=
    rational_preference_pullback hr _
  have hc' : ContinuousPreference (ThreeCoordinatePreference r z i j l) :=
    continuousPreference_pullback hc (threeCoordinateBundle_continuous z i j l)
  have hi : ThreeFactorIndependent (ThreeCoordinatePreference r z i j l) :=
    stronglySeparable_threeFactor hs z hij hil hjl
  have hnt' : ∃ a b, Strict (ThreeCoordinatePreference r z i j l)
      (z i, z j, a) (z i, z j, b) := by
    refine ⟨cHigh, cLow, ?_⟩
    simpa only [Strict, ThreeCoordinatePreference, ThreeCoordinateBundle,
      Function.update_eq_self] using hz
  obtain ⟨c, U, hU, hp, hhex⟩ :=
    third_factor_local_hexagon_of_nontrivial hr' hc' hi (z i) (z j) hnt'
  exact ⟨z, c, U, hU, hp, hhex⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive representation after a change of coordinate scales

Preparation for Kreps I, Proposition 2.14. Continuous strictly increasing
coordinate scales on connected ordered blocks have interval ranges. The
finite transfer theorem therefore applies directly to pair comparisons stated
in those scales, and yields their sum as an actual utility representation.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B C : I → Type*}

/-- Applying coordinate maps commutes with replacing one coordinate. -/
theorem coordinateMap_update [DecidableEq I] (f : ∀ i, B i → C i) (x : ∀ i, B i)
    (i : I) (a : B i) :
    (fun j => f j (Function.update x i a j)) =
      Function.update (fun j => f j (x j)) i (f i a) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

/-- Pair transfers stated in continuous increasing scales determine the full additive utility. -/
theorem represents_additive_of_pair_scale_invariance [DecidableEq I] [Fintype I]
    [∀ i, LinearOrder (B i)] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {F : (∀ i, B i) → ℝ} (hm : StrictMono F)
    (w : ∀ i, B i → ℝ) (hwc : ∀ i, Continuous (w i)) (hwm : ∀ i, StrictMono (w i))
    (hp : ∀ (x : ∀ i, B i) (i j : I) (a : B i) (b : B j), i ≠ j →
      w i a + w j b = w i (x i) + w j (x j) →
        F (Function.update (Function.update x i a) j b) = F x) :
    Represents (AdditiveUtility w) (UtilityPref F) := by
  let : ∀ i, Set.OrdConnected (Set.range (w i)) :=
    fun i => (isPreconnected_range (hwc i)).ordConnected
  let e (i : I) : B i ≃o Set.range (w i) := (hwm i).orderIso (w i)
  let E : (∀ i, B i) ≃o (∀ i, Set.range (w i)) :=
    { toEquiv := Equiv.piCongrRight (fun i => (e i).toEquiv)
      map_rel_iff' := by
        intro x y
        exact forall_congr' (fun i => (e i).le_iff_le) }
  let G : (∀ i, Set.range (w i)) → ℝ := fun q => F (E.symm q)
  have hEi (i : I) (q : Set.range (w i)) : w i ((e i).symm q) = q.val :=
    congrArg Subtype.val ((e i).apply_symm_apply q)
  have hGp : PairSumInvariant G := by
    intro q i j a b hij hab
    have hnum : w i ((e i).symm a) + w j ((e j).symm b) =
        w i ((E.symm q) i) + w j ((E.symm q) j) := by
      change w i ((e i).symm a) + w j ((e j).symm b) =
        w i ((e i).symm (q i)) + w j ((e j).symm (q j))
      simpa only [hEi] using hab
    have hh := hp (E.symm q) i j ((e i).symm a) ((e j).symm b) hij hnum
    change F (fun k => (e k).symm (Function.update (Function.update q i a) j b k)) = _
    rw [coordinateMap_update, coordinateMap_update]
    exact hh
  have hGm : StrictMono G := hm.comp E.symm.strictMono
  intro x y
  have hcmp := pairSumInvariant_comparison hGp hGm (E y) (E x)
  change F (E.symm (E y)) ≤ F (E.symm (E x)) ↔ _ at hcmp
  rw [E.symm_apply_apply, E.symm_apply_apply] at hcmp
  exact hcmp

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Fixed-companion calibration of coordinate charts

Preparation for Kreps I, Proposition 2.14. Along a varying target coordinate,
keep two other essential coordinates at fixed reference values. Their chart
domains always overlap the seed companions. Pair uniqueness fixes a positive
scale for every chart; after dividing by it, all target-coordinate overlap
transitions are translations. The fixed companions synchronize cardinal units.
-/

namespace Kreps.PreferenceProperties

/-- A target-coordinate chart family with two fixed essential companion coordinates. -/
structure CompanionChartFamily (K : Type*) where
  domain : K → Fin 3 → Set ℝ
  coord : K → Fin 3 → ℝ → ℝ
  open_domain : ∀ k i, IsOpen (domain k i)
  interval : ∀ k i, (domain k i).OrdConnected
  continuous : ∀ k i, ContinuousOn (coord k i) (domain k i)
  increasing : ∀ k i, StrictMonoOn (coord k i) (domain k i)
  firstReference : ℝ
  secondReference : ℝ
  first_mem : ∀ k, firstReference ∈ domain k 1
  second_mem : ∀ k, secondReference ∈ domain k 2
  pair_compatible : ∀ k l i j, i ≠ j →
    ∀ x ∈ domain k i ∩ domain l i, ∀ x' ∈ domain k i ∩ domain l i,
    ∀ y ∈ domain k j ∩ domain l j, ∀ y' ∈ domain k j ∩ domain l j,
      coord k i x + coord k j y = coord k i x' + coord k j y' →
        coord l i x + coord l j y = coord l i x' + coord l j y'

variable {K : Type*}

/-- Comparing the two fixed companions with a seed chart calibrates every chart's common unit. -/
theorem CompanionChartFamily.exists_calibration (F : CompanionChartFamily K) (seed : K) :
    ∃ slope firstOffset secondOffset : K → ℝ,
      (∀ k, 0 < slope k) ∧ slope seed = 1 ∧
      (∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
        F.coord k 1 x = slope k * F.coord seed 1 x + firstOffset k) ∧
      ∀ k x, x ∈ F.domain seed 2 ∩ F.domain k 2 →
        F.coord k 2 x = slope k * F.coord seed 2 x + secondOffset k := by
  classical
  have hcal (k : K) : ∃ slope firstOffset secondOffset : ℝ,
      0 < slope ∧ (k = seed → slope = 1) ∧
      (∀ x ∈ F.domain seed 1 ∩ F.domain k 1,
        F.coord k 1 x = slope * F.coord seed 1 x + firstOffset) ∧
      ∀ x ∈ F.domain seed 2 ∩ F.domain k 2,
        F.coord k 2 x = slope * F.coord seed 2 x + secondOffset := by
    by_cases hk : k = seed
    · subst k
      exact ⟨1, 0, 0, by norm_num, fun _ => rfl, by simp, by simp⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
        ((F.open_domain seed 1).inter (F.open_domain k 1)) ⟨F.first_mem seed, F.first_mem k⟩
      obtain ⟨c, hc, d, hd, hcd⟩ := open_real_set_has_pair
        ((F.open_domain seed 2).inter (F.open_domain k 2)) ⟨F.second_mem seed, F.second_mem k⟩
      obtain ⟨slope, β, γ, hpos, hf, hg⟩ := pair_chart_positive_affine_unique_on
        ((F.interval seed 1).inter (F.interval k 1))
        ((F.interval seed 2).inter (F.interval k 2))
        ((F.continuous seed 1).mono Set.inter_subset_left)
        ((F.continuous k 1).mono Set.inter_subset_right)
        ((F.continuous seed 2).mono Set.inter_subset_left)
        ((F.continuous k 2).mono Set.inter_subset_right)
        ((F.increasing seed 1).mono Set.inter_subset_left)
        ((F.increasing k 1).mono Set.inter_subset_right)
        ((F.increasing seed 2).mono Set.inter_subset_left)
        ((F.increasing k 2).mono Set.inter_subset_right)
        (F.pair_compatible seed k 1 2 (by decide)) ha hb hab hc hd hcd
      exact ⟨slope, β, γ, hpos, fun h => (hk h).elim, hf, hg⟩
  choose slope β γ hpos hseed hf hg using hcal
  exact ⟨slope, β, γ, hpos, hseed seed rfl, hf, hg⟩

/-- Calibrated companion scores agree with the seed up to translations. -/
theorem CompanionChartFamily.calibrated_companion (F : CompanionChartFamily K) (seed : K)
    {slope offset : K → ℝ} (hpos : ∀ k, 0 < slope k)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k)
    (k : K) (x : ℝ) (hx : x ∈ F.domain seed 1 ∩ F.domain k 1) :
    F.coord k 1 x / slope k = F.coord seed 1 x + offset k / slope k := by
  rw [hc k x hx, add_div]
  congr 1
  field_simp [(hpos k).ne']

/-- Once companions fix the units, every target overlap has a translation transition. -/
theorem CompanionChartFamily.calibrated_target_transition
    (F : CompanionChartFamily K) (seed : K) {slope offset : K → ℝ}
    (hpos : ∀ k, 0 < slope k)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k) (k l : K) :
    ∃ β : ℝ, ∀ x ∈ F.domain k 0 ∩ F.domain l 0,
      F.coord k 0 x / slope k = F.coord l 0 x / slope l + β := by
  classical
  by_cases hne : (F.domain k 0 ∩ F.domain l 0).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
      ((F.open_domain k 0).inter (F.open_domain l 0)) hx₀
    let T := (F.domain seed 1 ∩ F.domain k 1) ∩ F.domain l 1
    have hTo : IsOpen T := ((F.open_domain seed 1).inter (F.open_domain k 1)).inter
      (F.open_domain l 1)
    have hTi : T.OrdConnected := ((F.interval seed 1).inter (F.interval k 1)).inter
      (F.interval l 1)
    obtain ⟨c, hcm, d, hdm, hcd⟩ := open_real_set_has_pair hTo
      ⟨⟨F.first_mem seed, F.first_mem k⟩, F.first_mem l⟩
    have hcf (r : K) (i : Fin 3) :
        ContinuousOn (fun x => F.coord r i x / slope r) (F.domain r i) :=
      (F.continuous r i).div_const _
    have hmf (r : K) (i : Fin 3) :
        StrictMonoOn (fun x => F.coord r i x / slope r) (F.domain r i) := by
      intro x hx y hy hxy
      exact (div_lt_div_iff_of_pos_right (hpos r)).mpr (F.increasing r i hx hy hxy)
    have hunit : F.coord k 1 d / slope k - F.coord k 1 c / slope k =
        F.coord l 1 d / slope l - F.coord l 1 c / slope l := by
      rw [F.calibrated_companion seed hpos hc k d hdm.1,
        F.calibrated_companion seed hpos hc k c hcm.1,
        F.calibrated_companion seed hpos hc l d ⟨hdm.1.1, hdm.2⟩,
        F.calibrated_companion seed hpos hc l c ⟨hcm.1.1, hcm.2⟩]
      ring
    have hp : ∀ x ∈ F.domain k 0 ∩ F.domain l 0,
        ∀ x' ∈ F.domain k 0 ∩ F.domain l 0, ∀ y ∈ T, ∀ y' ∈ T,
        F.coord l 0 x / slope l + F.coord l 1 y / slope l =
          F.coord l 0 x' / slope l + F.coord l 1 y' / slope l →
        F.coord k 0 x / slope k + F.coord k 1 y / slope k =
          F.coord k 0 x' / slope k + F.coord k 1 y' / slope k := by
      intro x hx x' hx' y hy y' hy' he
      rw [← add_div, ← add_div] at he
      have hraw := (div_left_inj' (hpos l).ne').mp he
      have h := F.pair_compatible l k 0 1 (by decide) x ⟨hx.2, hx.1⟩ x' ⟨hx'.2, hx'.1⟩
        y ⟨hy.2, hy.1.2⟩ y' ⟨hy'.2, hy'.1.2⟩ hraw
      rw [← add_div, ← add_div, h]
    obtain ⟨β, _, hβ, _⟩ := pair_chart_translation_on
      ((F.interval k 0).inter (F.interval l 0)) hTi
      ((hcf l 0).mono Set.inter_subset_right) ((hcf k 0).mono Set.inter_subset_left)
      ((hcf l 1).mono (fun _ hx => hx.2)) ((hcf k 1).mono (fun _ hx => hx.1.2))
      ((hmf l 0).mono Set.inter_subset_right) ((hmf k 0).mono Set.inter_subset_left)
      ((hmf l 1).mono (fun _ hx => hx.2)) ((hmf k 1).mono (fun _ hx => hx.1.2))
      hp ha hb hab hcm hdm hcd hunit
    exact ⟨β, hβ⟩
  · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Retaining precisely the nondegenerate scalar factors

The scalar utility reduction may contain singleton score ranges. Their deletion
preserves every hypothesis needed for the nondegenerate interval theorem, and
zero extension transports its additive representation to all original ranges.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Scalar coordinates with at least two attainable values. -/
abbrev NontrivialScalarIndices (S : I → Set ℝ) := {i : I // Nontrivial (S i)}

/-- The exact utility on nondegenerate factors, with singleton coordinates fixed at baseline. -/
noncomputable def ActiveScalarUtility (V : (∀ i, S i) → ℝ) (z : ∀ i, S i)
    (x : ∀ i : NontrivialScalarIndices S, S i.val) : ℝ :=
  V (ActiveCoordinateExtend (fun i => Nontrivial (S i)) z x)

/-- A factor excluded from the active index set is a singleton type. -/
theorem inactiveScalar_subsingleton (i : I) (hi : ¬ Nontrivial (S i)) : Subsingleton (S i) :=
  not_nontrivial_iff_subsingleton.mp hi

/-- Continuity survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_continuous {V : (∀ i, S i) → ℝ} (hc : Continuous V)
    (z : ∀ i, S i) : Continuous (ActiveScalarUtility V z) :=
  hc.comp (activeCoordinateExtend_continuous (fun i => Nontrivial (S i)) z)

/-- Strict increase survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_strictMono {V : (∀ i, S i) → ℝ} (hm : StrictMono V)
    (z : ∀ i, S i) : StrictMono (ActiveScalarUtility V z) :=
  hm.comp (ActiveCoordinateOrderIso (fun i => Nontrivial (S i)) z
    inactiveScalar_subsingleton).strictMono

/-- Strong separability survives the deletion of singleton scalar factors. -/
theorem activeScalarUtility_stronglySeparable [DecidableEq I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, S i) :
    StronglySeparable (UtilityPref (ActiveScalarUtility V z)) :=
  stronglySeparable_activeCoordinates (fun i => Nontrivial (S i)) hs z

/-- Three nondegenerate scalar factors give three distinct members of the retained index set. -/
theorem three_nontrivialScalarIndices
    (h : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (S i) ∧ Nontrivial (S j) ∧ Nontrivial (S l)) :
    ∃ i j l : NontrivialScalarIndices S, i ≠ j ∧ i ≠ l ∧ j ≠ l := by
  obtain ⟨i, j, l, hij, hil, hjl, hi, hj, hl⟩ := h
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩,
    fun h => hij (congrArg Subtype.val h),
    fun h => hil (congrArg Subtype.val h),
    fun h => hjl (congrArg Subtype.val h)⟩

/-- Extend an actual continuous increasing active additive representation to every scalar factor. -/
theorem continuous_additive_of_activeScalar [Fintype I] [Fintype (NontrivialScalarIndices S)]
    {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (h : ∃ w : ∀ i : NontrivialScalarIndices S, S i.val → ℝ,
      (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
        Represents (AdditiveUtility w) (UtilityPref (ActiveScalarUtility V z))) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  obtain ⟨w, hwc, hwm, hwr⟩ := h
  exact ⟨ActiveCoordinateUtility (fun i => Nontrivial (S i)) w,
    activeCoordinateUtility_continuous _ hwc,
    activeCoordinateUtility_strictMono _ hwm inactiveScalar_subsingleton,
    represents_activeCoordinates _ z inactiveScalar_subsingleton hwr⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Lifting additive scalar scores to the original commodity blocks

Nontrivial original blocks have nondegenerate baseline score ranges. Continuous
additive functions on those ranges compose with the baseline scores to give
continuous additive functions on the original blocks.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- A nontrivial block has at least two distinct scores at any reference bundle. -/
theorem nontrivialBlock_baselineScores_nontrivial (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I) (hi : NontrivialBlock r i) :
    Nontrivial (Set.range (BaselineScores u z i)) := by
  let : Nonempty (∀ i, B i) := ⟨z⟩
  obtain ⟨a, b, hab⟩ := (nontrivialBlock_iff_every_context hs i).mp hi
  have hlt : BaselineScores u z i b < BaselineScores u z i a :=
    (strict_iff_utility_lt hu _ _).mp (hab z)
  refine ⟨⟨⟨BaselineScores u z i b, b, rfl⟩, ⟨BaselineScores u z i a, a, rfl⟩, ?_⟩⟩
  intro he
  exact hlt.ne (congrArg Subtype.val he)

/-- The book's three nontrivial blocks remain three distinct nondegenerate score factors. -/
theorem threeNontrivialBlocks_baselineScores (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (h : ThreeNontrivialBlocks r) :
    ∃ i j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (Set.range (BaselineScores u z i)) ∧
      Nontrivial (Set.range (BaselineScores u z j)) ∧
      Nontrivial (Set.range (BaselineScores u z l)) := by
  obtain ⟨i, j, l, hij, hil, hjl, hi, hj, hl⟩ := h
  exact ⟨i, j, l, hij, hil, hjl,
    nontrivialBlock_baselineScores_nontrivial hu hs z i hi,
    nontrivialBlock_baselineScores_nontrivial hu hs z j hj,
    nontrivialBlock_baselineScores_nontrivial hu hs z l hl⟩

/-- Compose each cardinal score function with its original block's baseline score. -/
def ScoreLiftedCoordinate (z : ∀ i, B i)
    (w : ∀ i, Set.range (BaselineScores u z i) → ℝ) (i : I) (a : B i) : ℝ :=
  w i ⟨BaselineScores u z i a, a, rfl⟩

/-- Continuous cardinal score functions lift to continuous original block functions. -/
theorem scoreLiftedCoordinate_continuous [∀ i, TopologicalSpace (B i)]
    (hc : Continuous u) (z : ∀ i, B i)
    {w : ∀ i, Set.range (BaselineScores u z i) → ℝ}
    (hw : ∀ i, Continuous (w i)) (i : I) :
    Continuous (ScoreLiftedCoordinate z w i) :=
  (hw i).comp ((baselineScores_continuous hc z i).subtype_mk (fun a => ⟨a, rfl⟩))

/-- An additive representation of the exact score aggregator represents the original preference. -/
theorem represents_additive_of_scoreAggregator [Fintype I] (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i)
    {w : ∀ i, Set.range (BaselineScores u z i) → ℝ}
    (hw : Represents (AdditiveUtility w) (UtilityPref (ScoreAggregator u z))) :
    Represents (AdditiveUtility (ScoreLiftedCoordinate z w)) r := by
  intro x y
  rw [hu, scoreAggregator_factors hu hs z x, scoreAggregator_factors hu hs z y]
  exact hw (BlockScores (BaselineScores u z) x) (BlockScores (BaselineScores u z) y)

/-- Continuous additive score functions yield the book's continuous additive block functions. -/
theorem continuous_additive_of_scoreAggregator [Fintype I]
    [∀ i, TopologicalSpace (B i)] (hu : Represents u r) (hs : StronglySeparable r)
    (hc : Continuous u) (z : ∀ i, B i)
    (h : ∃ w : ∀ i, Set.range (BaselineScores u z i) → ℝ,
      (∀ i, Continuous (w i)) ∧
        Represents (AdditiveUtility w) (UtilityPref (ScoreAggregator u z))) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  obtain ⟨w, hwc, hwr⟩ := h
  exact ⟨ScoreLiftedCoordinate z w, scoreLiftedCoordinate_continuous hc z hwc,
    represents_additive_of_scoreAggregator hu hs z hwr⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Completing an interior additive representation at every attained endpoint

For Proposition 2.14, the interior scales have finite limits at any attained
endpoints, because the original scalar utility is continuous and strictly
increasing. The extended scales preserve all comparisons on the full product.
No endpoint boundedness, endpoint limits or full-domain representation is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Interior additive scales extend continuously and strictly to the complete interval product. -/
theorem exists_full_interval_additive_extension {I : Type*} [Fintype I] [Nontrivial I]
    {S : I → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hne : ∀ i, (interior (S i)).Nonempty) {V : (∀ i, S i) → ℝ}
    (hc : Continuous V) (hm : StrictMono V) {f : ∀ i, interior (S i) → ℝ}
    (hf : ∀ i, Continuous (f i)) (hfm : ∀ i, StrictMono (f i))
    (hr : Represents (AdditiveUtility f) (UtilityPref (V ∘ InteriorScalarInclusion))) :
    ∃ g : ∀ i, S i → ℝ, (∀ i, Continuous (g i)) ∧ (∀ i, StrictMono (g i)) ∧
      Represents (AdditiveUtility g) (UtilityPref V) ∧
      ∀ i (x : interior (S i)), g i (Set.inclusion interior_subset x) = f i x := by
  classical
  have hr' : ∀ x y : ∀ i, interior (S i),
      V (fun i => Set.inclusion interior_subset (x i)) ≤
          V (fun i => Set.inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i) := fun x y => hr y x
  have hext (i : I) : ∃ g : S i → ℝ, Continuous g ∧ StrictMono g ∧
      ∀ x : interior (S i), g (Set.inclusion interior_subset x) = f i x := by
    have hb := interior_additive_scale_bounds hS hne hc hm hr' i
    exact interval_exists_continuous_strictMono_extension (hS i) (hne i) (hf i) (hfm i)
      (fun x _ hx => hb.1 x hx) (fun x _ hx => hb.2 x hx)
  choose g hg hgm heq using hext
  refine ⟨g, hg, hgm, ?_, heq⟩
  apply additive_comparison_of_interior hS hne hc hm hg hgm
  intro x y
  simpa only [heq] using hr' x y

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homothetic preferences and homogeneous utilities

Kreps I, Definitions 2.17-2.18 and the easy direction of Proposition 2.19, p. 44.
The scalar domain includes zero. A cone here requires closure under nonnegative
scaling; it need not be convex or closed under addition.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- **Definition 2.18:** closure under all nonnegative scalar multiples. -/
def NonnegativeCone {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S

/-- Scalar multiplication as an operation inside the cone domain. -/
def ScaleInCone {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : NonnegativeCone S) (t : ℝ≥0) (x : S) : S :=
  ⟨(t : ℝ) • x.val, hS x.val x.property t t.property⟩

/-- **Definition 2.18:** homogeneity of a specified nonnegative degree. -/
def HomogeneousOfDegree {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : NonnegativeCone S) (α : ℝ≥0) (u : S → ℝ) : Prop :=
  ∀ t x, u (ScaleInCone hS t x) = (t : ℝ) ^ (α : ℝ) * u x

/-- Degree one is ordinary scalar homogeneity, including the zero scalar. -/
theorem homogeneousOfDegree_one_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : NonnegativeCone S) (u : S → ℝ) :
    HomogeneousOfDegree hS 1 u ↔ ∀ t x, u (ScaleInCone hS t x) = (t : ℝ) * u x := by
  simp only [HomogeneousOfDegree, NNReal.coe_one, Real.rpow_one]

/-- The nonnegative orthant is a cone in the book's sense. -/
theorem orthant_nonnegativeCone (k : ℕ) :
    NonnegativeCone (Set.Ici (0 : Fin k → ℝ)) := by
  intro x hx t ht j
  exact mul_nonneg ht (hx j)

/-- The zero commodity bundle. -/
def OrthantZero (k : ℕ) : NonnegativeOrthant k := ⟨0, le_rfl⟩

/-- Nonnegative scalar multiplication of a consumption bundle. -/
def ScaleBundle {k : ℕ} (t : ℝ≥0) (x : NonnegativeOrthant k) : NonnegativeOrthant k :=
  ⟨fun j => (t : ℝ) * x.val j, fun j => mul_nonneg t.property (x.property j)⟩

/-- Bundle scaling is the general cone operation specialized to the orthant. -/
theorem scaleBundle_eq_cone {k : ℕ} (t : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle t x = ScaleInCone (orthant_nonnegativeCone k) t x := rfl

/-- Scaling by zero gives the origin. -/
theorem scaleBundle_zero {k : ℕ} (x : NonnegativeOrthant k) :
    ScaleBundle 0 x = OrthantZero k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, OrthantZero]

/-- Scaling by one preserves the bundle. -/
theorem scaleBundle_one {k : ℕ} (x : NonnegativeOrthant k) : ScaleBundle 1 x = x := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle]

/-- Every scalar leaves the origin fixed. -/
theorem scaleBundle_origin {k : ℕ} (t : ℝ≥0) :
    ScaleBundle t (OrthantZero k) = OrthantZero k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, OrthantZero]

/-- Successive scalings multiply their factors. -/
theorem scaleBundle_mul {k : ℕ} (t s : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle (t * s) x = ScaleBundle t (ScaleBundle s x) := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, mul_assoc]

/-- Every nonzero scaling can be undone within the nonnegative orthant. -/
theorem scaleBundle_inv {k : ℕ} {t : ℝ≥0} (ht : t ≠ 0) (x : NonnegativeOrthant k) :
    ScaleBundle t⁻¹ (ScaleBundle t x) = x := by
  rw [← scaleBundle_mul, inv_mul_cancel₀ ht, scaleBundle_one]

/-- Joint continuity of the scalar and the bundle. -/
theorem scaleBundle_continuous {k : ℕ} :
    Continuous (fun p : ℝ≥0 × NonnegativeOrthant k => ScaleBundle p.1 p.2) :=
  (continuous_pi fun j => (NNReal.continuous_coe.comp continuous_fst).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- A ray is continuous in its nonnegative scalar. -/
theorem scaleBundle_ray_continuous {k : ℕ} (x : NonnegativeOrthant k) :
    Continuous (fun t : ℝ≥0 => ScaleBundle t x) :=
  scaleBundle_continuous.comp (continuous_id.prodMk continuous_const)

/-- Iterating a contraction along a ray converges to the origin. -/
theorem scaleBundle_pow_tendsto_zero {k : ℕ} {t : ℝ≥0} (ht : t < 1)
    (x : NonnegativeOrthant k) :
    Filter.Tendsto (fun m : ℕ => ScaleBundle (t ^ m) x) Filter.atTop
      (nhds (OrthantZero k)) := by
  simpa only [Function.comp_def, scaleBundle_zero] using
    (scaleBundle_ray_continuous x).continuousAt.tendsto.comp
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ht)

/-- **Definition 2.17:** every common nonnegative scaling preserves weak preference. -/
def HomotheticPreference {k : ℕ}
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x y t, r x y → r (ScaleBundle t x) (ScaleBundle t y)

/-- Positive scaling preserves a comparison in both directions. -/
theorem homothetic_scale_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    r (ScaleBundle t x) (ScaleBundle t y) ↔ r x y := by
  constructor
  · intro h
    simpa only [scaleBundle_inv (ne_of_gt ht)] using hh _ _ t⁻¹ h
  · exact hh x y t

/-- Positive scaling preserves strict preference, while zero is deliberately excluded here. -/
theorem homothetic_scale_strict_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    Strict r (ScaleBundle t x) (ScaleBundle t y) ↔ Strict r x y :=
  and_congr (homothetic_scale_iff hh ht x y) (not_congr (homothetic_scale_iff hh ht y x))

/-- Positive scaling preserves indifference in both directions. -/
theorem homothetic_scale_indifferent_iff {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    {t : ℝ≥0} (ht : 0 < t) (x y : NonnegativeOrthant k) :
    Indifferent r (ScaleBundle t x) (ScaleBundle t y) ↔ Indifferent r x y :=
  and_congr (homothetic_scale_iff hh ht x y) (homothetic_scale_iff hh ht y x)

/-- Degree-one homogeneous utility on the nonnegative commodity orthant. -/
def HomogeneousUtility {k : ℕ} (u : NonnegativeOrthant k → ℝ) : Prop :=
  ∀ t x, u (ScaleBundle t x) = (t : ℝ) * u x

/-- The specialized definition agrees with the general cone definition at degree one. -/
theorem homogeneousUtility_iff_degree_one {k : ℕ} (u : NonnegativeOrthant k → ℝ) :
    HomogeneousUtility u ↔ HomogeneousOfDegree (orthant_nonnegativeCone k) 1 u := by
  exact (homogeneousOfDegree_one_iff (orthant_nonnegativeCone k)
    (fun x : Set.Ici (0 : Fin k → ℝ) => u ⟨x.val, x.property⟩)).symm

/-- Degree-one homogeneity forces utility at the origin to be zero. -/
theorem homogeneousUtility_origin {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : u (OrthantZero k) = 0 := by
  have h := hh 0 (OrthantZero k)
  simpa only [scaleBundle_zero, NNReal.coe_zero, zero_mul] using h

/-- A homogeneous utility representation gives homothetic preferences. -/
theorem homogeneous_represents_homothetic {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hu : Represents u r) (hh : HomogeneousUtility u) : HomotheticPreference r := by
  intro x y t hxy
  apply (hu _ _).mpr
  rw [hh, hh]
  exact mul_le_mul_of_nonneg_left ((hu x y).mp hxy) t.property

/-- **Proposition 2.19**, representation-to-preference direction. -/
theorem proposition_2_19_forward {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hu : Represents u r) (hc : Continuous u) (hh : HomogeneousUtility u) :
    ContinuousPreference r ∧ HomotheticPreference r :=
  ⟨proposition_2_9_forward hu hc, homogeneous_represents_homothetic hu hh⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuous semi-strictly convex preferences without concave representation

Kreps I, Problem 2.8b. Every contour is a half-space cut out by a linear form
whose coefficient depends on the rank. This gives continuity and semi-strict
convexity, completing the counterexample alongside the no-representation theorem.
-/

namespace Kreps.PreferenceProperties

/-- Below the dividing line, the denominator is positive. -/
theorem ratioSum_denominator_pos {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 ≤ 1) : 0 < 2 - x.val 0 := by
  have hx₁ := x.property 1
  change 0 ≤ x.val 1 at hx₁
  linarith

/-- The fractional branch takes values at most one. -/
theorem ratioSumUtility_low_le_one {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 ≤ 1) : RatioSumUtility x ≤ 1 := by
  rw [RatioSumUtility, ite_eq_left hx]
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (ratioSum_denominator_pos hx)).mpr
  nlinarith

/-- Both branches of the utility are nonnegative. -/
theorem ratioSumUtility_nonneg (x : NonnegativeOrthant 2) : 0 ≤ RatioSumUtility x := by
  have hx₀ : 0 ≤ x.val 0 := x.property 0
  have hx₁ : 0 ≤ x.val 1 := x.property 1
  by_cases hx : x.val 0 + x.val 1 ≤ 1
  · rw [RatioSumUtility, ite_eq_left hx]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (ratioSum_denominator_pos hx)).mpr
    nlinarith
  · rw [RatioSumUtility, ite_eq_right hx]
    linarith

/-- The linear form defining an upper contour at the given nonnegative rank. -/
noncomputable def RatioRankLinearForm (c : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  min (c + 1) 2 * x.val 0 + 2 * x.val 1

/-- Above the dividing line every rank at most one is strictly exceeded. -/
theorem ratioRankLinearForm_high {x : NonnegativeOrthant 2} {c : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hx : 1 < x.val 0 + x.val 1) :
    2 * c < RatioRankLinearForm c x := by
  have hx₁ : 0 ≤ x.val 1 := x.property 1
  rw [RatioRankLinearForm, min_eq_left (by linarith)]
  have hmain := mul_pos (show 0 < c + 1 by linarith) (sub_pos.mpr hx)
  have htail := mul_nonneg (sub_nonneg.mpr hc₁) hx₁
  nlinarith

/-- A weak upper utility contour is exactly a linear half-space. -/
theorem ratioSumUtility_le_iff {x : NonnegativeOrthant 2} {c : ℝ} (hc : 0 ≤ c) :
    c ≤ RatioSumUtility x ↔ 2 * c ≤ RatioRankLinearForm c x := by
  by_cases hc₁ : c ≤ 1
  · by_cases hx : x.val 0 + x.val 1 ≤ 1
    · rw [RatioSumUtility, ite_eq_left hx, RatioRankLinearForm, min_eq_left (by linarith)]
      rw [le_sub_iff_add_le, le_div_iff₀ (ratioSum_denominator_pos hx)]
      constructor <;> intro h <;> nlinarith
    · have hform := ratioRankLinearForm_high hc hc₁ (lt_of_not_ge hx)
      rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h
      · exact hform.le
      · linarith
  · have hc₁' : 1 < c := lt_of_not_ge hc₁
    rw [RatioRankLinearForm, min_eq_right (by linarith)]
    by_cases hx : x.val 0 + x.val 1 ≤ 1
    · have hu := ratioSumUtility_low_le_one hx
      constructor <;> intro h <;> nlinarith
    · rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h <;> nlinarith

/-- A strict upper utility contour is the corresponding open half-space. -/
theorem ratioSumUtility_lt_iff {x : NonnegativeOrthant 2} {c : ℝ} (hc : 0 ≤ c) :
    c < RatioSumUtility x ↔ 2 * c < RatioRankLinearForm c x := by
  by_cases hc₁ : c ≤ 1
  · by_cases hx : x.val 0 + x.val 1 ≤ 1
    · rw [RatioSumUtility, ite_eq_left hx, RatioRankLinearForm, min_eq_left (by linarith)]
      rw [lt_sub_iff_add_lt, lt_div_iff₀ (ratioSum_denominator_pos hx)]
      constructor <;> intro h <;> nlinarith
    · have hform := ratioRankLinearForm_high hc hc₁ (lt_of_not_ge hx)
      rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h
      · exact hform
      · linarith
  · have hc₁' : 1 < c := lt_of_not_ge hc₁
    rw [RatioRankLinearForm, min_eq_right (by linarith)]
    by_cases hx : x.val 0 + x.val 1 ≤ 1
    · have hu := ratioSumUtility_low_le_one hx
      constructor <;> intro h <;> nlinarith
    · rw [RatioSumUtility, ite_eq_right hx]
      constructor <;> intro h <;> nlinarith

/-- The two displayed branches agree at total consumption one. -/
theorem ratioSumUtility_boundary {x : NonnegativeOrthant 2}
    (hx : x.val 0 + x.val 1 = 1) : RatioSumUtility x = 1 := by
  apply le_antisymm (ratioSumUtility_low_le_one hx.le)
  apply (ratioSumUtility_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  norm_num [RatioRankLinearForm]
  linarith

/-- At the bundle's own rank its contour equation holds with equality. -/
theorem ratioRankLinearForm_self (x : NonnegativeOrthant 2) :
    RatioRankLinearForm (RatioSumUtility x) x = 2 * RatioSumUtility x := by
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((ratioSumUtility_lt_iff (ratioSumUtility_nonneg x)).mpr h)
  · exact (ratioSumUtility_le_iff (ratioSumUtility_nonneg x)).mp le_rfl

/-- The contour form is linear in consumption mixtures. -/
theorem ratioRankLinearForm_mix (c : ℝ) (x y : NonnegativeOrthant 2)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    RatioRankLinearForm c (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ha) =
      a * RatioRankLinearForm c x + (1 - a) * RatioRankLinearForm c y := by
  dsimp [RatioRankLinearForm, Mix]
  ring

/-- The ratio-and-sum preference is convex on the full orthant. -/
theorem ratioSumPreference_convex :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref RatioSumUtility) := by
  intro x y hxy a ha
  apply (ratioSumUtility_le_iff (ratioSumUtility_nonneg y)).mpr
  have hm := ratioRankLinearForm_mix (RatioSumUtility y) x y a ha
  have hy := ratioRankLinearForm_self y
  have hx := (ratioSumUtility_le_iff (ratioSumUtility_nonneg y)).mp hxy
  have hlin : 2 * RatioSumUtility y ≤ a * RatioRankLinearForm (RatioSumUtility y) x +
      (1 - a) * RatioRankLinearForm (RatioSumUtility y) y := by
    have hyeq := congrArg (fun v : ℝ => (1 - a) * v) hy
    nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx)]
  exact hlin.trans_eq hm.symm

/-- Strictly better endpoints improve every interior mixture strictly over the lower rank. -/
theorem ratioSumPreference_semiStrict :
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref RatioSumUtility) := by
  refine ⟨ratioSumPreference_convex, ?_⟩
  intro x y hxy a ha
  have hu : Represents RatioSumUtility (UtilityPref RatioSumUtility) := fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ y).mpr
  apply (ratioSumUtility_lt_iff (ratioSumUtility_nonneg y)).mpr
  have hm := ratioRankLinearForm_mix (RatioSumUtility y) x y a ⟨ha.1.le, ha.2.le⟩
  have hy := ratioRankLinearForm_self y
  have hx := (ratioSumUtility_lt_iff (ratioSumUtility_nonneg y)).mp
    ((strict_iff_utility_lt hu x y).mp hxy)
  have hlin : 2 * RatioSumUtility y < a * RatioRankLinearForm (RatioSumUtility y) x +
      (1 - a) * RatioRankLinearForm (RatioSumUtility y) y := by
    nlinarith [mul_pos ha.1 (sub_pos.mpr hx)]
  exact hlin.trans_eq hm.symm

/-- Every fixed-rank contour form is continuous. -/
theorem ratioRankLinearForm_continuous (c : ℝ) : Continuous (RatioRankLinearForm c) :=
  (((continuous_apply 0).comp continuous_subtype_val).const_mul _).add
    (((continuous_apply 1).comp continuous_subtype_val).const_mul _)

/-- The weak upper and lower contours are closed linear half-spaces. -/
theorem ratioSumPreference_continuous : ContinuousPreference (UtilityPref RatioSumUtility) := by
  apply (proposition_1_14c (proposition_1_3a RatioSumUtility)).mpr
  intro x
  have hn := ratioSumUtility_nonneg x
  have hlo : NoBetterThan (UtilityPref RatioSumUtility) x =
      {y | RatioRankLinearForm (RatioSumUtility x) y ≤ 2 * RatioSumUtility x} := by
    ext y
    change RatioSumUtility y ≤ RatioSumUtility x ↔
      RatioRankLinearForm (RatioSumUtility x) y ≤ 2 * RatioSumUtility x
    constructor
    · intro h
      apply le_of_not_gt
      intro hf
      exact not_lt_of_ge h ((ratioSumUtility_lt_iff hn).mpr hf)
    · intro h
      apply le_of_not_gt
      intro hf
      exact not_lt_of_ge h ((ratioSumUtility_lt_iff hn).mp hf)
  have hhi : NoWorseThan (UtilityPref RatioSumUtility) x =
      {y | 2 * RatioSumUtility x ≤ RatioRankLinearForm (RatioSumUtility x) y} := by
    ext y
    exact ratioSumUtility_le_iff hn
  rw [hlo, hhi]
  exact ⟨isClosed_le (ratioRankLinearForm_continuous _) continuous_const,
    isClosed_le continuous_const (ratioRankLinearForm_continuous _)⟩

/-- The displayed utility itself is continuous, not merely its represented preference. -/
theorem ratioSumUtility_continuous : Continuous RatioSumUtility :=
  continuous_of_full_nonnegative_range (fun _ _ => Iff.rfl)
    ratioSumPreference_continuous ratioSumUtility_nonneg
    (fun c hc => ⟨RatioAxisBundle c, ratioSumUtility_axis hc⟩)

/-- **Problem 2.8b:** continuous semi-strictly convex preference with no concave representation. -/
theorem problem_2_8b :
    Rational (UtilityPref RatioSumUtility) ∧
      ContinuousPreference (UtilityPref RatioSumUtility) ∧
      SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref RatioSumUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref RatioSumUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _, ratioSumPreference_continuous, ratioSumPreference_semiStrict,
    problem_2_8b_no_concave_representation⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The continuous extension and finite limits of the recursive scale

Kreps I, Problem 2.14(f)-(g). Complete precisely the assigned midpoint scale by
lower cuts. Its dense numerical range gives continuity. Every convergent sequence
of sampled points consequently has a finite limit, with extended-real limsup and
liminf equal to that real number. All such sequences give the same value.

The final wrapper constructs its initial, possibly discontinuous representation
by the countable weighted-sum method. It does not invoke the separate general
continuous-representation theorem.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

variable {X : Type*}

/-- The extension of the exact recursive assignment to the full preference domain. -/
noncomputable def RecursiveUtility (v : X → ℝ) (q : ℕ → X) : X → ℝ :=
  SampleRankExtension v q (RecursiveRank (v ∘ q))

/-- The extension retains every value assigned by the recursion. -/
theorem recursiveUtility_at_sample {v : X → ℝ} {q : ℕ → X}
    (hb : SampleBrackets v q) (n : ℕ) :
    RecursiveUtility v q (q n) = RecursiveRank (v ∘ q) n :=
  sampleRankExtension_at_sample (recursiveRank_preserving _) hb n

/-- Completing the recursive scale preserves every preference comparison. -/
theorem recursiveUtility_represents {r : X → X → Prop} {v : X → ℝ} {q : ℕ → X}
    (hv : Represents v r) (hb : SampleBrackets v q)
    (hs : StrictRankSeparator v (Set.range q)) : Represents (RecursiveUtility v q) r :=
  sampleRankExtension_represents hv (recursiveRank_preserving _) hb hs

/-- Every completed value lies in the smallest interval containing the sampled assigned values. -/
theorem recursiveUtility_mem_interval {v : X → ℝ} {q : ℕ → X}
    (hb : SampleBrackets v q) (x : X) :
    RecursiveUtility v q x ∈ RecursiveRankInterval (v ∘ q) := by
  obtain ⟨i, j, hi, hj⟩ := hb x
  exact ⟨i, j, sampleRankExtension_lower (recursiveRank_preserving _) hb hi,
    sampleRankExtension_upper (recursiveRank_preserving _) hb hj⟩

/-- Dense assigned ranks make the completed representation continuous, including at extrema. -/
theorem recursiveUtility_continuous [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Continuous (RecursiveUtility v q) := by
  apply continuous_of_interval_closure_range (recursiveUtility_represents hv hb hs) hc
  have hd : ∀ i j, (v ∘ q) i < (v ∘ q) j →
      ∃ k, (v ∘ q) i < (v ∘ q) k ∧ (v ∘ q) k < (v ∘ q) j := by
    intro i j hij
    obtain ⟨z, ⟨k, rfl⟩, hik, hkj⟩ := hs (q i) (q j) hij
    exact ⟨k, hik, hkj⟩
  have hrange : Set.range (RecursiveRank (v ∘ q)) ⊆ Set.range (RecursiveUtility v q) := by
    rintro t ⟨n, rfl⟩
    exact ⟨q n, recursiveUtility_at_sample hb n⟩
  intro x y t ht
  apply closure_mono hrange
  apply recursiveRankInterval_subset_closure (v ∘ q) hd
  exact (recursiveRankInterval_ordConnected (v ∘ q)).out
    (recursiveUtility_mem_interval hb x) (recursiveUtility_mem_interval hb y) ht

/-- Along every convergent sampled sequence, the assigned values converge to the extension. -/
theorem recursiveUtility_sample_limit [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x)) :
    Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) := by
  have h := (recursiveUtility_continuous hv hc hb hs).continuousAt.tendsto.comp hseq
  simpa only [Function.comp_def, recursiveUtility_at_sample hb] using h

/-- **Problem 2.14(f):** limsup and liminf agree and are finite, as extended-real limits. -/
theorem problem_2_14f [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x)) :
    ∃ l : ℝ, Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 l) ∧
      Filter.limsup (fun n => (RecursiveRank (v ∘ q) (s n) : EReal)) Filter.atTop =
        (l : EReal) ∧
      Filter.liminf (fun n => (RecursiveRank (v ∘ q) (s n) : EReal)) Filter.atTop =
        (l : EReal) := by
  have h := recursiveUtility_sample_limit hv hc hb hs s hseq
  have he : Filter.Tendsto (fun n => (RecursiveRank (v ∘ q) (s n) : EReal))
      Filter.atTop (𝓝 (RecursiveUtility v q x : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp h
  exact ⟨RecursiveUtility v q x, h, he.limsup_eq, he.liminf_eq⟩

/-- The limiting value is independent of the sampled sequence and its enumeration indices. -/
theorem recursiveUtility_limit_unique [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q))
    {x : X} (s : ℕ → ℕ) (hseq : Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x))
    {l : ℝ} (hl : Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 l)) :
    l = RecursiveUtility v q x :=
  tendsto_nhds_unique hl (recursiveUtility_sample_limit hv hc hb hs s hseq)

/-- Every point of a dense sampled metric domain is approached by a sampled sequence. -/
theorem dense_sample_sequence [TopologicalSpace X] [FrechetUrysohnSpace X]
    (q : ℕ → X) (hq : DenseRange q) (x : X) :
    ∃ s : ℕ → ℕ, Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) := by
  classical
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (hq x)
  choose s hs using hf
  refine ⟨s, ?_⟩
  have he : q ∘ s = f := funext hs
  rwa [he]

/-- Best and worst preference classes, when attained, are represented in the sample. -/
def SampleContainsPreferenceExtremes (r : X → X → Prop) (q : ℕ → X) : Prop :=
  (∀ x, (∀ y, r y x) → ∃ n, Indifferent r (q n) x) ∧
    (∀ x, (∀ y, r x y) → ∃ n, Indifferent r (q n) x)

/-- The preference formulation of included extremes gives the numerical formulation. -/
theorem sampleContainsExtremes_of_preference {r : X → X → Prop} {v : X → ℝ} {q : ℕ → X}
    (hv : Represents v r) (he : SampleContainsPreferenceExtremes r q) :
    SampleContainsExtremes v q := by
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := he.1 x (fun y => (hv y x).mpr (hx y))
    exact ⟨n, le_antisymm ((hv x (q n)).mp hn.2) ((hv (q n) x).mp hn.1)⟩
  · intro x hx
    obtain ⟨n, hn⟩ := he.2 x (fun y => (hv x y).mpr (hx y))
    exact ⟨n, le_antisymm ((hv x (q n)).mp hn.2) ((hv (q n) x).mp hn.1)⟩

/-- **Problem 2.14(g):** the sequence limits define a continuous representation. -/
theorem problem_2_14g [TopologicalSpace X] {r : X → X → Prop}
    {v : X → ℝ} {q : ℕ → X} (hv : Represents v r) (hc : ContinuousPreference r)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Represents (RecursiveUtility v q) r ∧ Continuous (RecursiveUtility v q) ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) →
        Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) :=
  ⟨recursiveUtility_represents hv hb hs, recursiveUtility_continuous hv hc hb hs,
    fun _ s hseq => recursiveUtility_sample_limit hv hc hb hs s hseq⟩

/-- Parts (d)-(g) need only continuous rational preference and the book's augmented dense sample. -/
theorem problem_2_14_recursive_completion [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} (hr : Rational r) (hc : ContinuousPreference r)
    (q : ℕ → X) (hq : DenseRange q) (he : SampleContainsPreferenceExtremes r q) :
    let v := SampledWeightedUtility r q DyadicWeight
    Represents v r ∧ Represents (RecursiveUtility v q) r ∧ Continuous (RecursiveUtility v q) ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q ∘ s) Filter.atTop (𝓝 x) →
        Filter.Tendsto (RecursiveRank (v ∘ q) ∘ s) Filter.atTop (𝓝 (RecursiveUtility v q x)) := by
  let v := SampledWeightedUtility r q DyadicWeight
  have hv : Represents v r := sampledWeightedUtility_represents q dyadicWeight_pos
    dyadicWeight_summable hr (dense_orderSeparating hr hc hq)
  have hs := dense_strictRankSeparator hr hc hv hq
  have hb := sampleBrackets_of_extremes hs (sampleContainsExtremes_of_preference hv he)
  exact ⟨hv, problem_2_14g hv hc hb hs⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Interior reference scores

Preparation for Kreps I, Proposition 2.14. The reference bundle can be chosen
so that every nontrivial block has both strictly better and strictly worse
alternatives. Consequently its common baseline utility lies in the interior
of each nontrivial block's real score interval.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- A connected nontrivial block has an intermediate rank at every fixed surrounding bundle. -/
theorem nontrivialBlock_interior_rank_at (hr : Rational r) (hc : ContinuousPreference r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I) [PreconnectedSpace (B i)]
    (hnt : NontrivialBlock r i) :
    ∃ a lo hi, Strict r (Function.update z i a) (Function.update z i lo) ∧
      Strict r (Function.update z i hi) (Function.update z i a) := by
  let : Nonempty (∀ i, B i) := ⟨z⟩
  obtain ⟨hi, lo, hh⟩ := (nontrivialBlock_iff_every_context hs i).mp hnt
  let f : B i → ∀ j, B j := fun a => Function.update z i a
  have hfc : Continuous f := continuous_const.update i continuous_id
  obtain ⟨a, hhia, halo⟩ := exists_strict_between (rational_preference_pullback hr f)
    (continuousPreference_pullback hc hfc) (hh z)
  exact ⟨a, lo, hi, halo, hhia⟩

/-- One reference bundle simultaneously puts all nontrivial blocks at interior preference ranks. -/
theorem exists_interior_reference [∀ i, PreconnectedSpace (B i)]
    (hr : Rational r) (hc : ContinuousPreference r) (hs : StronglySeparable r)
    (z : ∀ i, B i) :
    ∃ t : ∀ i, B i, ∀ i, NontrivialBlock r i →
      ∃ lo hi, Strict r t (Function.update t i lo) ∧
        Strict r (Function.update t i hi) t := by
  classical
  have hp (i : I) : ∃ a : B i, NontrivialBlock r i →
      ∃ lo hi, Strict r (Function.update z i a) (Function.update z i lo) ∧
        Strict r (Function.update z i hi) (Function.update z i a) := by
    by_cases hnt : NontrivialBlock r i
    · obtain ⟨a, lo, hi, hlo, hhi⟩ := nontrivialBlock_interior_rank_at hr hc hs z i hnt
      exact ⟨a, fun _ => ⟨lo, hi, hlo, hhi⟩⟩
    · exact ⟨z i, fun h => (hnt h).elim⟩
  choose t ht using hp
  refine ⟨t, fun i hnt => ?_⟩
  obtain ⟨lo, hi, hlo, hhi⟩ := ht i hnt
  have hl := (weaklySeparable_strict (stronglySeparable_weakly hs)
    i (t i) lo (z, ()) (t, ())).mp hlo
  have hh := (weaklySeparable_strict (stronglySeparable_weakly hs)
    i hi (t i) (z, ()) (t, ())).mp hhi
  exact ⟨lo, hi, by simpa only [Strict, ReplaceBlock, Function.update_eq_self] using hl,
    by simpa only [Strict, ReplaceBlock, Function.update_eq_self] using hh⟩

/-- Interior ordinal rank is interior membership in the baseline score interval. -/
theorem baselineScores_reference_interior {u : (∀ i, B i) → ℝ} (hu : Represents u r)
    (hc : Continuous u) (z : ∀ i, B i) (i : I) [PreconnectedSpace (B i)]
    (hi : ∃ lo hi, Strict r z (Function.update z i lo) ∧
      Strict r (Function.update z i hi) z) :
    u z ∈ interior (Set.range (BaselineScores u z i)) := by
  obtain ⟨lo, hi, hlo, hhi⟩ := hi
  have hl : BaselineScores u z i lo < u z := (strict_iff_utility_lt hu _ _).mp hlo
  have hh : u z < BaselineScores u z i hi := (strict_iff_utility_lt hu _ _).mp hhi
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds hl hh)
  intro v hv
  exact (baselineScores_ordConnected hc z i).out ⟨lo, rfl⟩ ⟨hi, rfl⟩
    ⟨hv.1.le, hv.2.le⟩

/-- All nontrivial score intervals can share the same interior reference utility. -/
theorem exists_interior_baseline_scores [∀ i, PreconnectedSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) :
    ∃ t : ∀ i, B i, ∀ i, NontrivialBlock r i →
      u t ∈ interior (Set.range (BaselineScores u t i)) := by
  obtain ⟨t, ht⟩ := exists_interior_reference hr (proposition_2_9_forward hu hc) hs z
  exact ⟨t, fun i hi => baselineScores_reference_interior hu hc t i (ht i hi)⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Global coordinates from companion-calibrated charts

For Proposition 2.14, two fixed essential companion coordinates determine cardinal units for
all local charts along a target interval. Translation-atlas gluing then gives a continuous
increasing target scale using those units throughout the interval.
-/

namespace Kreps.PreferenceProperties

/-- A fixed companion calibration glues all target charts without changing their units. -/
theorem CompanionChartFamily.globalize_target_of_calibration {K : Type*}
    (F : CompanionChartFamily K) {S : Set ℝ} (hS : S.OrdConnected)
    (hsub : ∀ k, F.domain k 0 ⊆ S) (hcover : ∀ x ∈ S, ∃ k, x ∈ F.domain k 0)
    (seed : K) (hne : (F.domain seed 0).Nonempty) {slope offset : K → ℝ}
    (hpos : ∀ k, 0 < slope k) (hunit : slope seed = 1)
    (hc : ∀ k x, x ∈ F.domain seed 1 ∩ F.domain k 1 →
      F.coord k 1 x = slope k * F.coord seed 1 x + offset k) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ F.domain seed 0, f x = F.coord seed 0 x) ∧
      ∀ k, ∃ B : ℝ, ∀ x ∈ F.domain k 0, f x = F.coord k 0 x / slope k + B := by
  have ht := F.calibrated_target_transition seed hpos hc
  let a : PositiveAffineIntervalAtlas K S := {
    domain := fun k => F.domain k 0
    coord := fun k x => F.coord k 0 x / slope k
    isOpen := fun k => F.open_domain k 0
    interval := fun k => F.interval k 0
    subset := hsub
    cover := hcover
    continuous := fun k => (F.continuous k 0).div_const _
    increasing := fun k _ hx _ hy hxy =>
      (div_lt_div_iff_of_pos_right (hpos k)).mpr (F.increasing k 0 hx hy hxy)
    transition := fun k l => by
      obtain ⟨B, hB⟩ := ht k l
      exact ⟨1, B, zero_lt_one, fun x hx => by simpa only [one_mul] using hB x hx⟩ }
  obtain ⟨f, hfc, hfm, hseed, hf⟩ := a.globalize_translations hS seed hne ht
  refine ⟨f, hfc, hfm, ?_, hf⟩
  intro x hx
  simpa only [a, hunit, div_one] using hseed x hx

/-- Two fixed companions provide both the calibration and a global increasing target scale. -/
theorem CompanionChartFamily.exists_global_target {K : Type*}
    (F : CompanionChartFamily K) {S : Set ℝ} (hS : S.OrdConnected)
    (hsub : ∀ k, F.domain k 0 ⊆ S) (hcover : ∀ x ∈ S, ∃ k, x ∈ F.domain k 0)
    (seed : K) (hne : (F.domain seed 0).Nonempty) :
    ∃ (slope : K → ℝ) (f : ℝ → ℝ), (∀ k, 0 < slope k) ∧ slope seed = 1 ∧
      ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ F.domain seed 0, f x = F.coord seed 0 x) ∧
      ∀ k, ∃ B : ℝ, ∀ x ∈ F.domain k 0, f x = F.coord k 0 x / slope k + B := by
  obtain ⟨slope, offset, _, hpos, hunit, hc, _⟩ := F.exists_calibration seed
  obtain ⟨f, hfc, hfm, hseed, hf⟩ :=
    F.globalize_target_of_calibration hS hsub hcover seed hne hpos hunit hc
  exact ⟨slope, f, hpos, hunit, hfc, hfm, hseed, hf⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The topology of a full commodity partition

A partition assigns every original commodity to exactly one block. Grouping the
nonnegative orthant by that assignment is a homeomorphism onto the product of
the nonnegative block orthants, with no leftover commodity factor.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k n : ℕ}

/-- The nonnegative quantities assigned to one member of a full commodity partition. -/
abbrev PartitionBlock (owner : Fin k → Fin n) (i : Fin n) :=
  {j : Fin k // owner j = i} → ℝ≥0

/-- Group each original commodity quantity into its unique assigned block. -/
def PartitionGroup (owner : Fin k → Fin n) (x : NonnegativeOrthant k) :
    ∀ i, PartitionBlock owner i :=
  fun _ j => ⟨x.val j.val, x.property j.val⟩

/-- Recover all original quantities from a full collection of partition blocks. -/
def PartitionUngroup (owner : Fin k → Fin n) (x : ∀ i, PartitionBlock owner i) :
    NonnegativeOrthant k :=
  ⟨fun j => (x (owner j) ⟨j, rfl⟩).val, fun j => (x (owner j) ⟨j, rfl⟩).property⟩

/-- Regrouping the original commodity quantities changes nothing. -/
theorem partitionUngroup_group (owner : Fin k → Fin n) (x : NonnegativeOrthant k) :
    PartitionUngroup owner (PartitionGroup owner x) = x := by
  apply Subtype.ext
  rfl

/-- Recovering and then regrouping quantities preserves every partition block. -/
theorem partitionGroup_ungroup (owner : Fin k → Fin n)
    (x : ∀ i, PartitionBlock owner i) :
    PartitionGroup owner (PartitionUngroup owner x) = x := by
  funext i j
  rcases j with ⟨j, hj⟩
  subst i
  rfl

/-- Each grouped quantity is a continuous coordinate of the original orthant. -/
theorem partitionGroup_continuous (owner : Fin k → Fin n) :
    Continuous (PartitionGroup owner) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply j.val).comp continuous_subtype_val).subtype_mk _

/-- Recovering the original quantities is continuous. -/
theorem partitionUngroup_continuous (owner : Fin k → Fin n) :
    Continuous (PartitionUngroup owner) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact continuous_subtype_val.comp
    ((continuous_apply (⟨j, rfl⟩ : {j' : Fin k // owner j' = owner j})).comp
      (continuous_apply (owner j)))

/-- A full partition is a homeomorphic regrouping of the original nonnegative orthant. -/
def partitionGroupingHomeomorph (owner : Fin k → Fin n) :
    NonnegativeOrthant k ≃ₜ (∀ i, PartitionBlock owner i) where
  toFun := PartitionGroup owner
  invFun := PartitionUngroup owner
  left_inv := partitionUngroup_group owner
  right_inv := partitionGroup_ungroup owner
  continuous_toFun := partitionGroup_continuous owner
  continuous_invFun := partitionUngroup_continuous owner

/-- Every partition block is connected, including empty blocks containing just one sub-bundle. -/
theorem partitionBlock_preconnected (owner : Fin k → Fin n) (i : Fin n) :
    PreconnectedSpace (PartitionBlock owner i) := by
  infer_instance

/-- A finite commodity partition has a separable product domain. -/
theorem partitionBlocks_separable (owner : Fin k → Fin n) :
    TopologicalSpace.SeparableSpace (∀ i, PartitionBlock owner i) := by
  infer_instance

/-- Every disjoint covering family of commodity subsets has a unique-owner assignment. -/
theorem exists_partition_assignment (J : Fin n → Set (Fin k))
    (hd : ∀ i j, i ≠ j → Disjoint (J i) (J j)) (hc : ∀ j, ∃ i, j ∈ J i) :
    ∃ owner : Fin k → Fin n, ∀ i j, owner j = i ↔ j ∈ J i := by
  classical
  let owner := fun j => (hc j).choose
  refine ⟨owner, fun i j => ?_⟩
  have hj : j ∈ J (owner j) := (hc j).choose_spec
  constructor
  · intro he
    exact he ▸ hj
  · intro hji
    by_contra hne
    exact Set.disjoint_left.mp (hd _ _ hne) hj hji

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preference along rays, without commodity monotonicity

Ingredients for the full Proposition 2.19 and Problem 2.12. Continuity and
homotheticity make a ray strictly increasing above the origin's rank and strictly
decreasing below it. Positive and negative reference rays bracket every relevant
indifference class. No commodity-monotonicity hypothesis is used.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A preferred scalar multiple can be iterated to give a chain above the original bundle. -/
theorem homothetic_iterate_above (hr : Rational r) (hh : HomotheticPreference r)
    {t : ℝ≥0} {x : NonnegativeOrthant k} (h : r (ScaleBundle t x) x) :
    ∀ m : ℕ, r (ScaleBundle (t ^ m) x) x := by
  intro m
  induction m with
  | zero => simpa only [pow_zero, scaleBundle_one] using complete_refl hr.1 x
  | succ m ih =>
    rw [pow_succ, scaleBundle_mul]
    exact hr.2 _ _ x (hh _ _ (t ^ m) h) ih

/-- A worse scalar multiple can be iterated to give a chain below the original bundle. -/
theorem homothetic_iterate_below (hr : Rational r) (hh : HomotheticPreference r)
    {t : ℝ≥0} {x : NonnegativeOrthant k} (h : r x (ScaleBundle t x)) :
    ∀ m : ℕ, r x (ScaleBundle (t ^ m) x) := by
  intro m
  induction m with
  | zero => simpa only [pow_zero, scaleBundle_one] using complete_refl hr.1 x
  | succ m ih =>
    rw [pow_succ, scaleBundle_mul]
    exact hr.2 x _ _ ih (hh _ _ (t ^ m) h)

/-- Contracting a bundle strictly above the origin strictly reduces its rank. -/
theorem homothetic_contract_positive (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {t : ℝ≥0} (ht : t < 1)
    {x : NonnegativeOrthant k} (hx : Strict r x (OrthantZero k)) :
    Strict r x (ScaleBundle t x) := by
  apply (proposition_1_9a hr.1 x _).mpr
  intro h
  have hseq := homothetic_iterate_above hr hh h
  have hclosed := ((proposition_1_14c hr).mp hc x).2
  exact hx.2 (hclosed.mem_of_tendsto (scaleBundle_pow_tendsto_zero ht x)
    (Filter.Eventually.of_forall hseq))

/-- Contracting a bundle strictly below the origin strictly raises its rank. -/
theorem homothetic_contract_negative (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {t : ℝ≥0} (ht : t < 1)
    {x : NonnegativeOrthant k} (hx : Strict r (OrthantZero k) x) :
    Strict r (ScaleBundle t x) x := by
  apply (proposition_1_9a hr.1 _ x).mpr
  intro h
  have hseq := homothetic_iterate_below hr hh h
  have hclosed := ((proposition_1_14c hr).mp hc x).1
  exact hx.2 (hclosed.mem_of_tendsto (scaleBundle_pow_tendsto_zero ht x)
    (Filter.Eventually.of_forall hseq))

/-- Scaling preserves the origin's indifference class, even at scalar zero. -/
theorem homothetic_origin_indifferent (hh : HomotheticPreference r)
    {x : NonnegativeOrthant k} (hx : Indifferent r x (OrthantZero k)) (t : ℝ≥0) :
    Indifferent r (ScaleBundle t x) (OrthantZero k) := by
  have h : Indifferent r (ScaleBundle t x) (ScaleBundle t (OrthantZero k)) :=
    ⟨hh _ _ t hx.1, hh _ _ t hx.2⟩
  simpa only [scaleBundle_origin] using h

/-- Larger multiples of a positive-rank bundle are strictly preferred. -/
theorem homothetic_positive_ray (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) {t s : ℝ≥0} (hts : t < s) :
    Strict r (ScaleBundle s p) (ScaleBundle t p) := by
  have hs : 0 < s := (show 0 ≤ t from zero_le).trans_lt hts
  have hts' : t / s < 1 := (div_lt_one hs).mpr hts
  have h := (homothetic_scale_strict_iff hh hs p (ScaleBundle (t / s) p)).mpr
    (homothetic_contract_positive hr hc hh hts' hp)
  have he : s * (t / s) = t := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  rwa [← scaleBundle_mul, he] at h

/-- Larger multiples of a negative-rank bundle are strictly worse. -/
theorem homothetic_negative_ray (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r (OrthantZero k) p) {t s : ℝ≥0} (hts : t < s) :
    Strict r (ScaleBundle t p) (ScaleBundle s p) := by
  have hs : 0 < s := (show 0 ≤ t from zero_le).trans_lt hts
  have hts' : t / s < 1 := (div_lt_one hs).mpr hts
  have h := (homothetic_scale_strict_iff hh hs (ScaleBundle (t / s) p) p).mpr
    (homothetic_contract_negative hr hc hh hts' hp)
  have he : s * (t / s) = t := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  rwa [← scaleBundle_mul, he] at h

/-- A numerical representation is strictly increasing along a positive reference ray. -/
theorem positive_ray_strictMono (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {u : NonnegativeOrthant k → ℝ} (hu : Represents u r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k)) :
    StrictMono (fun t : ℝ≥0 => u (ScaleBundle t p)) := by
  intro t s hts
  exact (strict_iff_utility_lt hu _ _).mp (homothetic_positive_ray hr hc hh hp hts)

/-- A numerical representation is strictly decreasing along a negative reference ray. -/
theorem negative_ray_strictAnti (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {u : NonnegativeOrthant k → ℝ} (hu : Represents u r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p) :
    StrictAnti (fun t : ℝ≥0 => u (ScaleBundle t p)) := by
  intro t s hts
  exact (strict_iff_utility_lt hu _ _).mp (homothetic_negative_ray hr hc hh hp hts)

/-- Every bundle is strictly dominated by some positive multiple of a positive reference. -/
theorem positive_ray_cofinal (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k)) (x : NonnegativeOrthant k) :
    ∃ t : ℝ≥0, 0 < t ∧ Strict r (ScaleBundle t p) x := by
  have hlim := scaleBundle_pow_tendsto_zero (show (1 / 2 : ℝ≥0) < 1 by norm_num) x
  have hevent := hlim.eventually ((continuousPreference_openStrictContours hc p).2.mem_nhds hp)
  obtain ⟨m, hm⟩ := hevent.exists
  have ha : (0 : ℝ≥0) < (1 / 2) ^ m := pow_pos (by norm_num) _
  have hinv : (0 : ℝ≥0) < ((1 / 2) ^ m)⁻¹ := inv_pos.mpr ha
  refine ⟨((1 / 2) ^ m)⁻¹, hinv, ?_⟩
  have h := (homothetic_scale_strict_iff hh hinv p
    (ScaleBundle ((1 / 2) ^ m) x)).mpr hm
  simpa only [scaleBundle_inv (ne_of_gt ha)] using h

/-- Every bundle strictly dominates some positive multiple of a negative reference. -/
theorem negative_ray_coinitial (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p) (x : NonnegativeOrthant k) :
    ∃ t : ℝ≥0, 0 < t ∧ Strict r x (ScaleBundle t p) := by
  have hlim := scaleBundle_pow_tendsto_zero (show (1 / 2 : ℝ≥0) < 1 by norm_num) x
  have hevent := hlim.eventually ((continuousPreference_openStrictContours hc p).1.mem_nhds hp)
  obtain ⟨m, hm⟩ := hevent.exists
  have ha : (0 : ℝ≥0) < (1 / 2) ^ m := pow_pos (by norm_num) _
  have hinv : (0 : ℝ≥0) < ((1 / 2) ^ m)⁻¹ := inv_pos.mpr ha
  refine ⟨((1 / 2) ^ m)⁻¹, hinv, ?_⟩
  have h := (homothetic_scale_strict_iff hh hinv
    (ScaleBundle ((1 / 2) ^ m) x) p).mpr hm
  simpa only [scaleBundle_inv (ne_of_gt ha)] using h

/-- Every rank weakly above the origin occurs on any positive reference ray. -/
theorem positive_ray_indifference (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) {x : NonnegativeOrthant k}
    (hx : r x (OrthantZero k)) : ∃ t : ℝ≥0, Indifferent r (ScaleBundle t p) x := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  obtain ⟨T, _, hT⟩ := positive_ray_cofinal hc hh hp x
  have hf := huc.comp (scaleBundle_ray_continuous p)
  have h0 : u (ScaleBundle 0 p) ≤ u x := by
    simpa only [scaleBundle_zero] using (hu x (OrthantZero k)).mp hx
  have h1 : u x ≤ u (ScaleBundle T p) := (hu _ _).mp hT.1
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show 0 ≤ T from zero_le) hf.continuousOn ⟨h0, h1⟩
  exact ⟨t, (hu _ _).mpr ht.ge, (hu _ _).mpr ht.le⟩

/-- Every rank weakly below the origin occurs on any negative reference ray. -/
theorem negative_ray_indifference (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r (OrthantZero k) p) {x : NonnegativeOrthant k}
    (hx : r (OrthantZero k) x) : ∃ t : ℝ≥0, Indifferent r (ScaleBundle t p) x := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  obtain ⟨T, _, hT⟩ := negative_ray_coinitial hc hh hp x
  have hf := huc.comp (scaleBundle_ray_continuous p)
  have h0 : u x ≤ u (ScaleBundle 0 p) := by
    simpa only [scaleBundle_zero] using (hu (OrthantZero k) x).mp hx
  have h1 : u (ScaleBundle T p) ≤ u x := (hu _ _).mp hT.1
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (show 0 ≤ T from zero_le) hf.continuousOn ⟨h1, h0⟩
  exact ⟨t, (hu _ _).mpr ht.ge, (hu _ _).mpr ht.le⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Minimum utility and the two forms of strict monotonicity

Kreps I, p. 32. A finite minimum of strictly increasing component utilities
strictly increases when every commodity increases. With at least two goods it
is never strictly monotone in the stronger, coordinatewise product-order sense.
The component utilities have the book's nonnegative one-good domain.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} [NeZero k]

/-- The minimum of the component utilities in the p. 32 example. -/
noncomputable def MinimumUtility (u : Fin k → ℝ≥0 → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => u j (.mk (x.val j) (x.property j)))

/-- Minimum utility is bounded by each component utility. -/
theorem minimumUtility_le_component (u : Fin k → ℝ≥0 → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) :
    MinimumUtility u x ≤ u j (.mk (x.val j) (x.property j)) :=
  Finset.inf'_le _ (Finset.mem_univ j)

/-- A component attains the finite minimum. -/
theorem minimumUtility_exists_index (u : Fin k → ℝ≥0 → ℝ) (x : NonnegativeOrthant k) :
    ∃ j, MinimumUtility u x = u j (.mk (x.val j) (x.property j)) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun j => u j (.mk (x.val j) (x.property j)))
  exact ⟨j, hj⟩

/-- Nondecreasing components give nondecreasing minimum utility. -/
theorem minimumUtility_monotone {u : Fin k → ℝ≥0 → ℝ} (hu : ∀ j, Monotone (u j)) :
    Monotone (MinimumUtility u) := by
  intro x y hxy
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u y
  rw [hj]
  exact (minimumUtility_le_component u x j).trans (hu j (hxy j))

/-- Strictly increasing components give strict preference improvement when all goods increase. -/
theorem minimumPreference_strictAllIncrease {u : Fin k → ℝ≥0 → ℝ}
    (hu : ∀ j, StrictMono (u j)) :
    StrictAllIncreasePreference (UtilityPref (MinimumUtility u)) := by
  intro x y hxy
  have hr : Represents (MinimumUtility u) (UtilityPref (MinimumUtility u)) := fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hr _ _).mpr
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u x
  exact (minimumUtility_le_component u y j).trans_lt ((hu j (hxy j)).trans_eq hj.symm)

/-- Increasing a coordinate other than a minimizing one cannot strictly raise the minimum. -/
theorem minimumPreference_not_strictlyMonotone (hk : 2 ≤ k) (u : Fin k → ℝ≥0 → ℝ) :
    ¬StrictlyMonotonePreference (UtilityPref (MinimumUtility u)) := by
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u (OrthantZero k)
  obtain ⟨i, hij⟩ := exists_ne j
  let y : NonnegativeOrthant k :=
    ⟨Function.update (0 : Fin k → ℝ) i 1, fun a => by
      simp only [Function.update_apply]
      split_ifs <;> norm_num⟩
  have hne : y ≠ OrthantZero k := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant k => z.val i) h
    simp [y, OrthantZero] at he
  have hyj : (NNReal.mk (y.val j) (y.property j) : ℝ≥0) = 0 := by
    apply NNReal.coe_injective
    change (Function.update (0 : Fin k → ℝ) i 1) j = 0
    simp [Function.update_of_ne hij.symm]
  have hj0 : MinimumUtility u (OrthantZero k) = u j 0 := hj
  have hle : MinimumUtility u y ≤ MinimumUtility u (OrthantZero k) := by
    calc
      MinimumUtility u y ≤ u j (.mk (y.val j) (y.property j)) :=
        minimumUtility_le_component u y j
      _ = u j 0 := congrArg (u j) hyj
      _ = MinimumUtility u (OrthantZero k) := hj0.symm
  intro h
  exact (h y (OrthantZero k) y.property hne).2 hle

/-- The p. 32 example separates all-coordinate increase from strict monotonicity. -/
theorem minimumUtility_example (hk : 2 ≤ k) {u : Fin k → ℝ≥0 → ℝ}
    (hu : ∀ j, StrictMono (u j)) :
    MonotonePreference (UtilityPref (MinimumUtility u)) ∧
      StrictAllIncreasePreference (UtilityPref (MinimumUtility u)) ∧
      LocallyInsatiable (UtilityPref (MinimumUtility u)) ∧
      ¬StrictlyMonotonePreference (UtilityPref (MinimumUtility u)) := by
  have hr : Represents (MinimumUtility u) (UtilityPref (MinimumUtility u)) := fun _ _ => Iff.rfl
  have hs := minimumPreference_strictAllIncrease hu
  exact ⟨(proposition_2_2_monotone hr).mpr (minimumUtility_monotone (fun j => (hu j).monotone)),
    hs, strictAllIncrease_locallyInsatiable hs, minimumPreference_not_strictlyMonotone hk u⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cobb-Douglas monotonicity and boundary failures

Kreps I, p. 32. Positive exponents give strict improvement when all coordinates
increase, and strict product-order monotonicity on the positive orthant. With
at least two goods, points on a coordinate axis give a counterexample to strict
monotonicity on the whole nonnegative orthant.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ}

/-- The finite-dimensional Cobb-Douglas utility in the p. 32 example. -/
noncomputable def CobbDouglasUtility (α : Fin k → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  ∏ j, (x.val j) ^ (α j)

/-- Every factor, and hence the product, is nonnegative on the orthant. -/
theorem cobbDouglasUtility_nonneg (α : Fin k → ℝ) (x : NonnegativeOrthant k) :
    0 ≤ CobbDouglasUtility α x :=
  Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (x.property j) _)

/-- Positive consumption of every good makes the product strictly positive. -/
theorem cobbDouglasUtility_pos (α : Fin k → ℝ) {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j) : 0 < CobbDouglasUtility α x :=
  Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) _)

/-- A zero coordinate with nonzero exponent makes the entire product zero. -/
theorem cobbDouglasUtility_zero_coordinate {α : Fin k → ℝ} {x : NonnegativeOrthant k}
    {j : Fin k} (hα : α j ≠ 0) (hx : x.val j = 0) : CobbDouglasUtility α x = 0 := by
  unfold CobbDouglasUtility
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hx, Real.zero_rpow hα]

/-- With a positive number of goods and positive exponents, utility at the origin is zero. -/
theorem cobbDouglasUtility_origin [NeZero k] {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    CobbDouglasUtility α (OrthantZero k) = 0 :=
  cobbDouglasUtility_zero_coordinate (j := 0) (ne_of_gt (hα 0)) rfl

/-- Nonnegative exponents give weak product-order monotonicity. -/
theorem cobbDouglasUtility_monotone {α : Fin k → ℝ} (hα : ∀ j, 0 ≤ α j) :
    Monotone (CobbDouglasUtility α) := by
  intro x y hxy
  exact Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (x.property j) _)
    (fun j _ => Real.rpow_le_rpow (x.property j) (hxy j) (hα j))

/-- A nontrivial coordinatewise increase from a positive bundle strictly increases utility. -/
theorem cobbDouglasUtility_strict_of_positive {α : Fin k → ℝ} (hα : ∀ j, 0 < α j)
    {x y : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) (hxy : x < y) :
    CobbDouglasUtility α x < CobbDouglasUtility α y := by
  have hex : ∃ j, x.val j < y.val j := by
    by_contra hn
    push Not at hn
    exact hxy.ne (Subtype.ext (funext (fun j => le_antisymm (hxy.le j) (hn j))))
  obtain ⟨j, hj⟩ := hex
  exact Finset.prod_lt_prod₀ (fun i _ => Real.rpow_pos_of_pos (hx i) _)
    (fun i _ => Real.rpow_le_rpow (x.property i) (hxy.le i) (hα i).le)
    ⟨j, Finset.mem_univ j, Real.rpow_lt_rpow (x.property j) hj (hα j)⟩

/-- This gives strict monotonicity away from all coordinate axes. -/
theorem cobbDouglasUtility_strictMonoOn_positive {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    StrictMonoOn (CobbDouglasUtility α) {x : NonnegativeOrthant k | ∀ j, 0 < x.val j} :=
  fun _ hx _ _ hxy => cobbDouglasUtility_strict_of_positive hα hx hxy

/-- Strict increases in every commodity improve preference, including from boundary bundles. -/
theorem cobbDouglasPreference_strictAllIncrease [NeZero k] {α : Fin k → ℝ}
    (hα : ∀ j, 0 < α j) : StrictAllIncreasePreference (UtilityPref (CobbDouglasUtility α)) := by
  intro x y hxy
  have hu : Represents (CobbDouglasUtility α) (UtilityPref (CobbDouglasUtility α)) :=
    fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ _).mpr
  by_cases hy : ∀ j, 0 < y.val j
  · apply cobbDouglasUtility_strict_of_positive hα hy
    apply lt_of_le_of_ne (fun j => (hxy j).le)
    intro he
    exact (ne_of_lt (hxy 0)) (congrArg (fun z : NonnegativeOrthant k => z.val 0) he)
  · push Not at hy
    obtain ⟨j, hj⟩ := hy
    rw [cobbDouglasUtility_zero_coordinate (ne_of_gt (hα j))
      (le_antisymm hj (y.property j))]
    exact cobbDouglasUtility_pos α (fun i => (y.property i).trans_lt (hxy i))

/-- With at least two goods, increasing one coordinate on an axis leaves utility zero. -/
theorem cobbDouglasPreference_not_strictlyMonotone (hk : 2 ≤ k) {α : Fin k → ℝ}
    (hα : ∀ j, 0 < α j) : ¬StrictlyMonotonePreference (UtilityPref (CobbDouglasUtility α)) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  let y : NonnegativeOrthant k :=
    ⟨Function.update (0 : Fin k → ℝ) i 1, fun a => by
      simp only [Function.update_apply]
      split_ifs <;> norm_num⟩
  have hyj : y.val j = 0 := by simp [y, i, j]
  have hy : CobbDouglasUtility α y = 0 :=
    cobbDouglasUtility_zero_coordinate (ne_of_gt (hα j)) hyj
  have hz : CobbDouglasUtility α (OrthantZero k) = 0 :=
    cobbDouglasUtility_zero_coordinate (j := j) (ne_of_gt (hα j)) rfl
  have hne : y ≠ OrthantZero k := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant k => z.val i) h
    simp [y, OrthantZero] at he
  intro h
  apply (h y (OrthantZero k) y.property hne).2
  change CobbDouglasUtility α y ≤ CobbDouglasUtility α (OrthantZero k)
  rw [hy, hz]

/-- The p. 32 Cobb-Douglas example, with the dimension needed for its boundary counterexample. -/
theorem cobbDouglasUtility_example (hk : 2 ≤ k) {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) :
    MonotonePreference (UtilityPref (CobbDouglasUtility α)) ∧
      StrictAllIncreasePreference (UtilityPref (CobbDouglasUtility α)) ∧
      LocallyInsatiable (UtilityPref (CobbDouglasUtility α)) ∧
      ¬StrictlyMonotonePreference (UtilityPref (CobbDouglasUtility α)) ∧
      StrictMonoOn (CobbDouglasUtility α) {x : NonnegativeOrthant k | ∀ j, 0 < x.val j} := by
  let : NeZero k := ⟨by omega⟩
  have hu : Represents (CobbDouglasUtility α) (UtilityPref (CobbDouglasUtility α)) :=
    fun _ _ => Iff.rfl
  have hs := cobbDouglasPreference_strictAllIncrease hα
  exact ⟨(proposition_2_2_monotone hu).mpr (cobbDouglasUtility_monotone (fun j => (hα j).le)),
    hs, strictAllIncrease_locallyInsatiable hs,
    cobbDouglasPreference_not_strictlyMonotone hk hα,
    cobbDouglasUtility_strictMonoOn_positive hα⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Include attained best and worst ranks in the dense sample

Kreps I, Problem 2.14, pp. 48-49. Prepending a worst point when one exists and a
best point when one exists preserves density and covers both possible extreme
classes. If an extreme does not exist, the original first sample point is used.
Thus all four attained/unattained-extrema cases are covered without an assumption
that the numerical range is bounded or that its supremum or infimum is attained.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- A globally worst point when one exists; otherwise use the specified anchor. -/
noncomputable def WorstSamplePoint (r : X → X → Prop) (anchor : X) : X := by
  classical
  exact if h : ∃ x, ∀ y, r y x then h.choose else anchor

/-- A globally best point when one exists; otherwise use the specified anchor. -/
noncomputable def BestSamplePoint (r : X → X → Prop) (anchor : X) : X := by
  classical
  exact if h : ∃ x, ∀ y, r x y then h.choose else anchor

/-- The dense enumeration with possible extreme ranks prepended. -/
noncomputable def AugmentedPreferenceSample (r : X → X → Prop) (q : ℕ → X) : ℕ → X
  | 0 => WorstSamplePoint r (q 0)
  | 1 => BestSamplePoint r (q 0)
  | n + 2 => q n

/-- Every original sample point remains in the augmented enumeration. -/
theorem augmentedPreferenceSample_tail (r : X → X → Prop) (q : ℕ → X) (n : ℕ) :
    AugmentedPreferenceSample r q (n + 2) = q n := rfl

/-- Prepending the extreme ranks preserves density. -/
theorem augmentedPreferenceSample_dense [TopologicalSpace X]
    (r : X → X → Prop) (q : ℕ → X) (hq : DenseRange q) :
    DenseRange (AugmentedPreferenceSample r q) := by
  apply hq.mono
  rintro x ⟨n, rfl⟩
  exact ⟨n + 2, rfl⟩

/-- Every attained best or worst class is represented in the augmented sample. -/
theorem augmentedPreferenceSample_extremes (r : X → X → Prop) (q : ℕ → X) :
    SampleContainsPreferenceExtremes r (AugmentedPreferenceSample r q) := by
  classical
  constructor
  · intro x hx
    have h : ∃ z, ∀ y, r y z := ⟨x, hx⟩
    refine ⟨0, ?_⟩
    change Indifferent r (WorstSamplePoint r (q 0)) x
    rw [WorstSamplePoint, dite_eq_left h]
    exact ⟨hx h.choose, h.choose_spec x⟩
  · intro x hx
    have h : ∃ z, ∀ y, r z y := ⟨x, hx⟩
    refine ⟨1, ?_⟩
    change Indifferent r (BestSamplePoint r (q 0)) x
    rw [BestSamplePoint, dite_eq_left h]
    exact ⟨h.choose_spec x, hx h.choose⟩

/-- Dense samples augmented as in the book bracket every original numerical rank. -/
theorem augmentedPreferenceSample_brackets [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) (q : ℕ → X) (hq : DenseRange q) :
    SampleBrackets v (AugmentedPreferenceSample r q) :=
  sampleBrackets_of_extremes
    (dense_strictRankSeparator hr hc hv (augmentedPreferenceSample_dense r q hq))
    (sampleContainsExtremes_of_preference hv (augmentedPreferenceSample_extremes r q))

/-- The complete recursive proof starts from any dense enumeration. -/
theorem recursive_completion_of_dense_sample [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} (hr : Rational r) (hc : ContinuousPreference r)
    (q : ℕ → X) (hq : DenseRange q) :
    let q' := AugmentedPreferenceSample r q
    let v := SampledWeightedUtility r q' DyadicWeight
    Represents v r ∧ Represents (RecursiveUtility v q') r ∧ Continuous (RecursiveUtility v q') ∧
      ∀ x (s : ℕ → ℕ), Filter.Tendsto (q' ∘ s) Filter.atTop (nhds x) →
        Filter.Tendsto (RecursiveRank (v ∘ q') ∘ s) Filter.atTop
          (nhds (RecursiveUtility v q' x)) :=
  problem_2_14_recursive_completion hr hc (AugmentedPreferenceSample r q)
    (augmentedPreferenceSample_dense r q hq) (augmentedPreferenceSample_extremes r q)

/-- Existence of the augmented enumeration requires only a nonempty separable domain. -/
theorem exists_dense_sample_with_extremes [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X] (r : X → X → Prop) :
    ∃ q : ℕ → X, DenseRange q ∧ SampleContainsPreferenceExtremes r q := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq X
  exact ⟨AugmentedPreferenceSample r q, augmentedPreferenceSample_dense r q hq,
    augmentedPreferenceSample_extremes r q⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The cod liver oil and manna rank reversal

Kreps I, Section 2.7, p. 44. The book ranks `(1,2)` above `(1/5,14/5)` but
ranks `(1,14)` above `(5,10)`, reversing the comparison after multiplication
by five. These two rankings alone contradict homotheticity.

The book does not specify a utility formula. The utility constructed here is
an explicit continuous witness of its rankings: oil's health contribution
saturates at one teaspoon, while additional manna remains desirable.
-/

namespace Kreps.PreferenceProperties

/-- The source's smaller bundle containing one full teaspoon of cod liver oil. -/
def CodLiverMannaHealthBundle : NonnegativeOrthant 2 :=
  PairBundle 1 2 (by norm_num) (by norm_num)

/-- The source's smaller bundle with more manna but only one fifth teaspoon of oil. -/
noncomputable def CodLiverMannaTasteBundle : NonnegativeOrthant 2 :=
  PairBundle (1 / 5) (14 / 5) (by norm_num) (by norm_num)

/-- Multiplying the first source bundle by five gives `(5,10)`. -/
theorem codLiverManna_health_scale_five :
    ScaleBundle 5 CodLiverMannaHealthBundle = PairBundle 5 10 (by norm_num) (by norm_num) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> norm_num [ScaleBundle, CodLiverMannaHealthBundle, PairBundle]

/-- Multiplying the second source bundle by five gives `(1,14)`. -/
theorem codLiverManna_taste_scale_five :
    ScaleBundle 5 CodLiverMannaTasteBundle = PairBundle 1 14 (by norm_num) (by norm_num) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> norm_num [ScaleBundle, CodLiverMannaTasteBundle, PairBundle]

/-- The exact two source rankings already rule out homotheticity, independently of any utility. -/
theorem codLiverManna_rank_reversal_not_homothetic
    {r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop}
    (hsmall : Strict r CodLiverMannaHealthBundle CodLiverMannaTasteBundle)
    (hlarge : Strict r (PairBundle 1 14 (by norm_num) (by norm_num))
      (PairBundle 5 10 (by norm_num) (by norm_num))) : ¬HomotheticPreference r := by
  intro hh
  have h := hh CodLiverMannaHealthBundle CodLiverMannaTasteBundle 5 hsmall.1
  rw [codLiverManna_health_scale_five, codLiverManna_taste_scale_five] at h
  exact hlarge.2 h

/-- A constructed witness of the source rankings, with oil's benefit capped at one teaspoon. -/
noncomputable def CodLiverMannaUtility (x : NonnegativeOrthant 2) : ℝ :=
  2 * min (x.val 0) 1 + x.val 1

/-- The illustrative utility is continuous, including at the oil-satiation threshold. -/
theorem codLiverMannaUtility_continuous : Continuous CodLiverMannaUtility :=
  (continuous_const.mul (((continuous_apply 0).comp continuous_subtype_val).min
    continuous_const)).add ((continuous_apply 1).comp continuous_subtype_val)

/-- The four utility values reproduce the book's strict rank reversal exactly. -/
theorem codLiverMannaUtility_values :
    CodLiverMannaUtility CodLiverMannaHealthBundle = 4 ∧
      CodLiverMannaUtility CodLiverMannaTasteBundle = 16 / 5 ∧
      CodLiverMannaUtility (PairBundle 5 10 (by norm_num) (by norm_num)) = 12 ∧
      CodLiverMannaUtility (PairBundle 1 14 (by norm_num) (by norm_num)) = 16 := by
  norm_num [CodLiverMannaUtility, CodLiverMannaHealthBundle, CodLiverMannaTasteBundle, PairBundle]

/-- One continuous rational preference realizes both exact comparisons in the p. 44 example. -/
theorem codLiverManna_example :
    Rational (UtilityPref CodLiverMannaUtility) ∧
      ContinuousPreference (UtilityPref CodLiverMannaUtility) ∧
      Strict (UtilityPref CodLiverMannaUtility)
        CodLiverMannaHealthBundle CodLiverMannaTasteBundle ∧
      Strict (UtilityPref CodLiverMannaUtility)
        (PairBundle 1 14 (by norm_num) (by norm_num))
        (PairBundle 5 10 (by norm_num) (by norm_num)) ∧
      ¬HomotheticPreference (UtilityPref CodLiverMannaUtility) := by
  have hsmall : Strict (UtilityPref CodLiverMannaUtility)
      CodLiverMannaHealthBundle CodLiverMannaTasteBundle := by
    norm_num [Strict, UtilityPref, codLiverMannaUtility_values.1,
      codLiverMannaUtility_values.2.1]
  have hlarge : Strict (UtilityPref CodLiverMannaUtility)
      (PairBundle 1 14 (by norm_num) (by norm_num))
      (PairBundle 5 10 (by norm_num) (by norm_num)) := by
    norm_num [Strict, UtilityPref, codLiverMannaUtility_values.2.2.1,
      codLiverMannaUtility_values.2.2.2]
  exact ⟨proposition_1_3a _, proposition_2_9_forward (fun _ _ => Iff.rfl)
    codLiverMannaUtility_continuous, hsmall, hlarge,
    codLiverManna_rank_reversal_not_homothetic hsmall hlarge⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homogeneous utility from reference rays

The extension construction for Proposition 2.19 preserves homogeneity when the
reference curve and its utility scale compatibly. This module completes the
cases where every bundle is weakly above the origin or every bundle is weakly
below it. The case with ranks on both sides uses a signed reference curve.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- The scalar itself represents preference along a positive reference ray. -/
theorem positive_ray_represents (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) :
    Represents (fun t : ℝ≥0 => (t : ℝ)) (fun a b => r (ScaleBundle a p) (ScaleBundle b p)) := by
  obtain ⟨v, hv⟩ := proposition_1_15 k hr hc
  have hs := positive_ray_strictMono hr hc hh hv hp
  intro a b
  exact (hv _ _).trans (hs.le_iff_le.trans NNReal.coe_le_coe.symm)

/-- A scale-compatible reference representation extends to a homogeneous utility. -/
theorem liftedUtility_homogeneous {Y : Type*} (hr : Rational r)
    (hh : HomotheticPreference r) (f : Y → NonnegativeOrthant k) (v : Y → ℝ)
    (hcover : ∀ x, ∃ y, Indifferent r (f y) x)
    (hv : Represents v (fun a b => r (f a) (f b))) (σ : ℝ≥0 → Y → Y)
    (hfScale : ∀ t y, ScaleBundle t (f y) = f (σ t y))
    (hvScale : ∀ t y, v (σ t y) = (t : ℝ) * v y) :
    HomogeneousUtility (LiftedUtility f v hcover) := by
  intro t x
  let y := Classical.choose (hcover x)
  have hy : Indifferent r (f y) x := Classical.choose_spec (hcover x)
  have hscaled : Indifferent r (f (σ t y)) (ScaleBundle t x) := by
    rw [← hfScale]
    exact ⟨hh _ _ t hy.1, hh _ _ t hy.2⟩
  have hu := liftedUtility_represents hr f v hcover hv
  calc
    LiftedUtility f v hcover (ScaleBundle t x) = LiftedUtility f v hcover (f (σ t y)) :=
      le_antisymm ((hu _ _).mp hscaled.1) ((hu _ _).mp hscaled.2)
    _ = v (σ t y) := liftedUtility_agrees f v hcover hv _
    _ = (t : ℝ) * v y := hvScale t y
    _ = (t : ℝ) * LiftedUtility f v hcover x := rfl

/-- A positive reference represents all ranks when every bundle is weakly above the origin. -/
theorem homogeneous_representation_above_origin (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k))
    (hall : ∀ x, r x (OrthantZero k)) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  let f := fun t : ℝ≥0 => ScaleBundle t p
  let v := fun t : ℝ≥0 => (t : ℝ)
  have hcover (x : NonnegativeOrthant k) : ∃ t, Indifferent r (f t) x :=
    positive_ray_indifference hr hc hh hp (hall x)
  have hv : Represents v (fun a b => r (f a) (f b)) := positive_ray_represents hr hc hh hp
  refine ⟨LiftedUtility f v hcover, liftedUtility_represents hr f v hcover hv,
    liftedUtility_continuous hr hc f v hcover hv NNReal.continuous_coe, ?_⟩
  apply liftedUtility_homogeneous hr hh f v hcover hv (fun t s => t * s)
  · intro t s
    exact (scaleBundle_mul t s p).symm
  · intro t s
    exact NNReal.coe_mul t s

/-- Reversing all comparisons preserves rationality. -/
theorem reversePreference_rational (hr : Rational r) : Rational (fun x y => r y x) :=
  ⟨fun x y => hr.1 y x, fun x y z hxy hyz => hr.2 z y x hyz hxy⟩

/-- Reversing all comparisons preserves continuity. -/
theorem reversePreference_continuous (hc : ContinuousPreference r) :
    ContinuousPreference (fun x y => r y x) :=
  hc.preimage continuous_swap

/-- Reversing all comparisons preserves homotheticity. -/
theorem reversePreference_homothetic (hh : HomotheticPreference r) :
    HomotheticPreference (fun x y => r y x) := fun x y t h => hh y x t h

/-- Negating a utility for reversed preference recovers the original preference. -/
theorem neg_utility_represents {u : NonnegativeOrthant k → ℝ}
    (hu : Represents u (fun x y => r y x)) : Represents (fun x => -u x) r := by
  intro x y
  change r x y ↔ -u y ≤ -u x
  rw [neg_le_neg_iff]
  exact hu y x

/-- Negating a homogeneous utility preserves degree one. -/
theorem neg_utility_homogeneous {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : HomogeneousUtility (fun x => -u x) := by
  intro t x
  change -u (ScaleBundle t x) = (t : ℝ) * -u x
  rw [hh]
  ring

/-- A negative reference handles the case in which every rank lies below the origin. -/
theorem homogeneous_representation_below_origin (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p)
    (hall : ∀ x, r (OrthantZero k) x) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  obtain ⟨u, hu, huc, huh⟩ := homogeneous_representation_above_origin
    (reversePreference_rational hr) (reversePreference_continuous hc)
    (reversePreference_homothetic hh) hp hall
  exact ⟨fun x => -u x, neg_utility_represents hu, huc.neg, neg_utility_homogeneous huh⟩

/-- If every bundle is indifferent to the origin, constant zero is a homogeneous representation. -/
theorem homogeneous_representation_indifferent (hr : Rational r)
    (hall : ∀ x, Indifferent r x (OrthantZero k)) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  refine ⟨fun _ => 0, ?_, continuous_const, ?_⟩
  · intro x y
    exact iff_of_true (hr.2 x (OrthantZero k) y (hall x).1 (hall y).2) le_rfl
  · intro t x
    simp

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A countable sequence brackets every numerical rank

Kreps I, Problem 2.14(a). A countable dense sequence in the numerical range is
cofinal below every nonminimal rank and coinitial above every nonmaximal rank.
Include any attained extrema to obtain weak brackets for every point. This uses
only a real-valued representation, with no continuity assumption on that function.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- A dense sample of the numerical range, with extrema included, brackets every rank. -/
theorem sampleBrackets_of_dense_rank_range (v : X → ℝ) (q : ℕ → X)
    (hd : DenseRange (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)))
    (he : SampleContainsExtremes v q) : SampleBrackets v q := by
  intro x
  have hlo : ∃ i, v (q i) ≤ v x := by
    by_cases hy : ∃ y, v y < v x
    · obtain ⟨y, hy⟩ := hy
      have ho : IsOpen {a : Set.range v | a.val < v x} :=
        isOpen_lt continuous_subtype_val continuous_const
      obtain ⟨i, hi⟩ := hd.exists_mem_open ho ⟨⟨v y, Set.mem_range_self y⟩, hy⟩
      exact ⟨i, hi.le⟩
    · obtain ⟨i, hi⟩ := he.1 x (fun y => le_of_not_gt (fun h => hy ⟨y, h⟩))
      exact ⟨i, hi.le⟩
  have hhi : ∃ j, v x ≤ v (q j) := by
    by_cases hy : ∃ y, v x < v y
    · obtain ⟨y, hy⟩ := hy
      have ho : IsOpen {a : Set.range v | v x < a.val} :=
        isOpen_lt continuous_const continuous_subtype_val
      obtain ⟨j, hj⟩ := hd.exists_mem_open ho ⟨⟨v y, Set.mem_range_self y⟩, hy⟩
      exact ⟨j, hj.le⟩
    · obtain ⟨j, hj⟩ := he.2 x (fun y => le_of_not_gt (fun h => hy ⟨y, h⟩))
      exact ⟨j, hj.ge⟩
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  exact ⟨i, j, hi, hj⟩

/-- Every real-valued scale has a countable bracketing sample containing attained extremes. -/
theorem exists_sample_brackets [Nonempty X] (v : X → ℝ) :
    ∃ q : ℕ → X, SampleBrackets v q ∧ SampleContainsExtremes v q := by
  classical
  let : Nonempty (Set.range v) := ⟨⟨v (Classical.arbitrary X), Set.mem_range_self _⟩⟩
  obtain ⟨f, hf⟩ := TopologicalSpace.exists_dense_seq (Set.range v)
  let q : ℕ → X := fun n => (f n).property.choose
  have hq (n : ℕ) : v (q n) = (f n).val := (f n).property.choose_spec
  have hqd : DenseRange (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)) := by
    have heq : (fun n => (⟨v (q n), Set.mem_range_self (q n)⟩ : Set.range v)) = f := by
      funext n
      exact Subtype.ext (hq n)
    rwa [heq]
  let q' := AugmentedPreferenceSample (UtilityPref v) q
  have hd : DenseRange (fun n => (⟨v (q' n), Set.mem_range_self (q' n)⟩ : Set.range v)) := by
    apply hqd.mono
    rintro a ⟨n, rfl⟩
    exact ⟨n + 2, rfl⟩
  have he : SampleContainsExtremes v q' :=
    sampleContainsExtremes_of_preference (fun _ _ => Iff.rfl)
      (augmentedPreferenceSample_extremes (UtilityPref v) q)
  exact ⟨q', sampleBrackets_of_dense_rank_range v q' hd he, he⟩

/-- In preference language, a countable sequence is both cofinal and coinitial. -/
theorem exists_preference_bracketing_sequence [Nonempty X] {r : X → X → Prop}
    {v : X → ℝ} (hv : Represents v r) :
    ∃ q : ℕ → X, ∀ x, ∃ i j, r (q i) x ∧ r x (q j) := by
  obtain ⟨q, hb, _⟩ := exists_sample_brackets v
  refine ⟨q, fun x => ?_⟩
  obtain ⟨j, i, hj, hi⟩ := hb x
  exact ⟨i, j, (hv (q i) x).mpr hi, (hv x (q j)).mpr hj⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A signed homogeneous representation

Kreps I, Proposition 2.19 and Problem 2.12. Join a positive reference ray to a
negative reference ray at the origin, parameterize their ranks by the real line,
and extend by indifference. Together with the one-sided and constant cases, this
proves the full theorem without imposing monotonicity in commodities.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A positive ray for positive parameters and a negative ray for negative parameters. -/
def SignedRay (p n : NonnegativeOrthant k) (a : ℝ) : NonnegativeOrthant k :=
  ⟨fun j => max a 0 * p.val j + max (-a) 0 * n.val j,
    fun j => add_nonneg (mul_nonneg (le_max_right _ _) (p.property j))
      (mul_nonneg (le_max_right _ _) (n.property j))⟩

/-- On the nonnegative half-line the signed curve is the positive reference ray. -/
theorem signedRay_nonneg (p n : NonnegativeOrthant k) {a : ℝ} (ha : 0 ≤ a) :
    SignedRay p n a = ScaleBundle (.mk a ha) p := by
  apply Subtype.ext
  funext j
  simp [SignedRay, ScaleBundle, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]

/-- On the nonpositive half-line the signed curve is the negative reference ray. -/
theorem signedRay_nonpos (p n : NonnegativeOrthant k) {a : ℝ} (ha : a ≤ 0) :
    SignedRay p n a = ScaleBundle (.mk (-a) (neg_nonneg.mpr ha)) n := by
  apply Subtype.ext
  funext j
  simp [SignedRay, ScaleBundle, max_eq_right ha, max_eq_left (neg_nonneg.mpr ha)]

/-- The two reference rays meet at the origin. -/
theorem signedRay_zero (p n : NonnegativeOrthant k) : SignedRay p n 0 = OrthantZero k := by
  rw [signedRay_nonneg p n le_rfl]
  exact scaleBundle_zero p

/-- Joining the two rays gives a continuous curve, including at their meeting point. -/
theorem signedRay_continuous (p n : NonnegativeOrthant k) : Continuous (SignedRay p n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_id.max continuous_const).mul continuous_const).add
    ((continuous_id.neg.max continuous_const).mul continuous_const)

/-- Scalar multiplication of bundles multiplies the signed parameter by the same scalar. -/
theorem signedRay_scale (p n : NonnegativeOrthant k) (t : ℝ≥0) (a : ℝ) :
    ScaleBundle t (SignedRay p n a) = SignedRay p n ((t : ℝ) * a) := by
  apply Subtype.ext
  funext j
  change (t : ℝ) * (max a 0 * p.val j + max (-a) 0 * n.val j) =
    max ((t : ℝ) * a) 0 * p.val j + max (-((t : ℝ) * a)) 0 * n.val j
  have hp : max ((t : ℝ) * a) 0 = (t : ℝ) * max a 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg (a := (t : ℝ)) a 0 t.property).symm
  have hn : max (-((t : ℝ) * a)) 0 = (t : ℝ) * max (-a) 0 := by
    simpa only [mul_zero, mul_neg] using
      (mul_max_of_nonneg (a := (t : ℝ)) (-a) 0 t.property).symm
  rw [hp, hn]
  ring

/-- Increasing the signed parameter strictly raises preference rank. -/
theorem homothetic_signedRay_strict (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n)
    {a b : ℝ} (hab : a < b) : Strict r (SignedRay p n b) (SignedRay p n a) := by
  by_cases hb : b ≤ 0
  · rw [signedRay_nonpos p n hb, signedRay_nonpos p n (hab.le.trans hb)]
    apply homothetic_negative_ray hr hc hh hn
    exact NNReal.coe_lt_coe.mp (neg_lt_neg hab)
  · have hb' : 0 < b := lt_of_not_ge hb
    by_cases ha : 0 ≤ a
    · rw [signedRay_nonneg p n hb'.le, signedRay_nonneg p n ha]
      apply homothetic_positive_ray hr hc hh hp
      exact NNReal.coe_lt_coe.mp hab
    · have ha' : a < 0 := lt_of_not_ge ha
      rw [signedRay_nonneg p n hb'.le, signedRay_nonpos p n ha'.le]
      have hpos : Strict r (ScaleBundle (.mk b hb'.le) p) (OrthantZero k) := by
        simpa only [scaleBundle_zero] using homothetic_positive_ray hr hc hh hp
          (show (0 : ℝ≥0) < .mk b hb'.le from NNReal.coe_lt_coe.mp hb')
      have hneg : Strict r (OrthantZero k)
          (ScaleBundle (.mk (-a) (neg_nonneg.mpr ha'.le)) n) := by
        simpa only [scaleBundle_zero] using homothetic_negative_ray hr hc hh hn
          (show (0 : ℝ≥0) < .mk (-a) (neg_nonneg.mpr ha'.le) from
            NNReal.coe_lt_coe.mp (neg_pos.mpr ha'))
      exact strict_weak_trans hr.2 hpos hneg.1

/-- The real parameter represents preference on the joined reference rays. -/
theorem homothetic_signedRay_represents (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n) :
    Represents (fun a : ℝ => a) (fun a b => r (SignedRay p n a) (SignedRay p n b)) := by
  obtain ⟨u, hu⟩ := proposition_1_15 k hr hc
  have hs : StrictMono (fun a : ℝ => u (SignedRay p n a)) := by
    intro a b hab
    exact (strict_iff_utility_lt hu _ _).mp (homothetic_signedRay_strict hr hc hh hp hn hab)
  exact fun a b => (hu _ _).trans hs.le_iff_le

/-- The joined rays meet every indifference class. -/
theorem homothetic_signedRay_covers (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n)
    (x : NonnegativeOrthant k) : ∃ a : ℝ, Indifferent r (SignedRay p n a) x := by
  rcases hr.1 x (OrthantZero k) with hx | hx
  · obtain ⟨t, ht⟩ := positive_ray_indifference hr hc hh hp hx
    refine ⟨(t : ℝ), ?_⟩
    rw [signedRay_nonneg p n (a := (t : ℝ)) t.property]
    exact ht
  · obtain ⟨t, ht⟩ := negative_ray_indifference hr hc hh hn hx
    refine ⟨-(t : ℝ), ?_⟩
    rw [signedRay_nonpos p n (a := -(t : ℝ)) (neg_nonpos.mpr t.property)]
    have he : NNReal.mk (- -(t : ℝ)) (neg_nonneg.mpr (neg_nonpos.mpr t.property)) = t := by
      apply NNReal.coe_injective
      exact neg_neg (t : ℝ)
    rw [he]
    exact ht

/-- Positive and negative references give a continuous homogeneous representation of all ranks. -/
theorem homogeneous_representation_both_sides (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p n : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k))
    (hn : Strict r (OrthantZero k) n) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  have hcover := homothetic_signedRay_covers hr hc hh hp hn
  have hv := homothetic_signedRay_represents hr hc hh hp hn
  refine ⟨LiftedUtility (SignedRay p n) id hcover,
    liftedUtility_represents hr (SignedRay p n) id hcover hv,
    liftedUtility_continuous hr hc (SignedRay p n) id hcover hv continuous_id, ?_⟩
  exact liftedUtility_homogeneous hr hh (SignedRay p n) id hcover hv
    (fun t a => (t : ℝ) * a) (signedRay_scale p n) (fun _ _ => rfl)

/-- **Proposition 2.19:** continuity and homotheticity are equivalent to a continuous
degree-one homogeneous representation, with no commodity-monotonicity assumption. -/
theorem proposition_2_19 (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ∧ HomotheticPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  constructor
  · rintro ⟨hc, hh⟩
    by_cases hpos : ∃ p, Strict r p (OrthantZero k)
    · obtain ⟨p, hp⟩ := hpos
      by_cases hneg : ∃ n, Strict r (OrthantZero k) n
      · obtain ⟨n, hn⟩ := hneg
        exact homogeneous_representation_both_sides hr hc hh hp hn
      · apply homogeneous_representation_above_origin hr hc hh hp
        intro x
        by_contra hx
        exact hneg ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
    · by_cases hneg : ∃ n, Strict r (OrthantZero k) n
      · obtain ⟨n, hn⟩ := hneg
        apply homogeneous_representation_below_origin hr hc hh hn
        intro x
        by_contra hx
        exact hpos ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
      · apply homogeneous_representation_indifferent hr
        intro x
        constructor
        · by_contra hx
          exact hneg ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
        · by_contra hx
          exact hpos ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
  · rintro ⟨u, hu, huc, huh⟩
    exact proposition_2_19_forward hu huc huh

/-- **Problem 2.12:** the full homogeneous representation, without the optional extra assumption. -/
theorem problem_2_12 (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u :=
  (proposition_2_19 k hr).mp ⟨hc, hh⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A reference curve meeting every indifference class

Kreps I, Problem 2.14(a)-(b), p. 48. From any numerical representation, choose
a countable sequence bracketing all ranks and join the points by affine segments.
When best and worst ranks are both attained, a single segment suffices. Otherwise
the countable construction handles each of the remaining three extrema cases.
The connected-image crossing lemma then makes the curve meet every class.

The final theorem assembles parts (a)-(g): construct the curve, run the exact
recursive scale on an augmented dense subset of its image, and extend by indifference.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- A countable sequence of weak rank bounds gives a continuous bracketing polygonal curve. -/
theorem exists_bracketing_polygonal_curve [Nonempty S] (hS : Convex ℝ S)
    {r : S → S → Prop} {v : S → ℝ} (hv : Represents v r) :
    ∃ q : ℕ → S, Continuous (SequenceCurve hS q) ∧
      ∀ x, ∃ a b : ℝ, r (SequenceCurve hS q a) x ∧ r x (SequenceCurve hS q b) := by
  obtain ⟨q, hq⟩ := exists_preference_bracketing_sequence hv
  refine ⟨q, sequenceCurve_continuous hS q, fun x => ?_⟩
  obtain ⟨i, j, hi, hj⟩ := hq x
  refine ⟨i, j, ?_⟩
  simpa only [sequenceCurve_nat] using And.intro hi hj

/-- The single segment from a best point to a worst point. -/
def ExtremeReferenceSegment (hS : Convex ℝ S) (best worst : S) (t : UnitSegment) : S :=
  Mix hS worst best t.val t.property

/-- The segment starts at the best point. -/
theorem extremeReferenceSegment_zero (hS : Convex ℝ S) (best worst : S) :
    ExtremeReferenceSegment hS best worst ⟨0, by norm_num⟩ = best :=
  mix_zero hS worst best _

/-- The segment ends at the worst point. -/
theorem extremeReferenceSegment_one (hS : Convex ℝ S) (best worst : S) :
    ExtremeReferenceSegment hS best worst ⟨1, by norm_num⟩ = worst :=
  mix_one hS worst best _

/-- The one-segment construction is continuous. -/
theorem extremeReferenceSegment_continuous (hS : Convex ℝ S) (best worst : S) :
    Continuous (ExtremeReferenceSegment hS best worst) := by
  have h : Continuous (fun t : UnitSegment =>
      t.val • worst.val + (1 - t.val) • best.val) := by fun_prop
  exact h.subtype_mk _

/-- The both-extrema-attained case in **Problem 2.14(a)** uses only one line segment. -/
theorem problem_2_14a_both_extrema (hS : Convex ℝ S) {r : S → S → Prop}
    (best worst : S) (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) :
    Continuous (ExtremeReferenceSegment hS best worst) ∧
      ∀ x, r (ExtremeReferenceSegment hS best worst ⟨0, by norm_num⟩) x ∧
        r x (ExtremeReferenceSegment hS best worst ⟨1, by norm_num⟩) := by
  refine ⟨extremeReferenceSegment_continuous hS best worst, fun x => ?_⟩
  rw [extremeReferenceSegment_zero, extremeReferenceSegment_one]
  exact ⟨hbest x, hworst x⟩

/-- In the both-extrema case the single segment crosses every indifference class. -/
theorem extremeReferenceSegment_covers (hS : Convex ℝ S) {r : S → S → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) (best worst : S)
    (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) (x : S) :
    ∃ t, Indifferent r (ExtremeReferenceSegment hS best worst t) x := by
  have h := problem_2_14a_both_extrema hS best worst hbest hworst
  exact lemma_2_10 hr hc _ h.1 x (h.2 x).1 (h.2 x).2

/-- A two-point list continued constantly has just one nonconstant affine segment. -/
def ExtremeReferenceSequence (best worst : S) (n : ℕ) : S := if n = 0 then best else worst

/-- The two-point sequence starts at its best point. -/
theorem extremeReferenceSequence_curve_zero (hS : Convex ℝ S) (best worst : S) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) 0 = best := by
  simpa only [Nat.cast_zero, ExtremeReferenceSequence, ite_true] using
    sequenceCurve_nat hS (ExtremeReferenceSequence best worst) 0

/-- Its first affine segment ends at its worst point. -/
theorem extremeReferenceSequence_curve_one (hS : Convex ℝ S) (best worst : S) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) 1 = worst := by
  simpa only [Nat.cast_one, ExtremeReferenceSequence, one_ne_zero, ite_false] using
    sequenceCurve_nat hS (ExtremeReferenceSequence best worst) 1

/-- On the unit interval the two-point polygonal curve is exactly the single segment. -/
theorem extremeReferenceSequence_on_unit (hS : Convex ℝ S) (best worst : S)
    (t : UnitSegment) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) t.val =
      ExtremeReferenceSegment hS best worst t := by
  apply Subtype.ext
  have h := polygonalCurve_formula hS
    (fun n : ℤ => ExtremeReferenceSequence best worst n.toNat) 0 (t := t.val)
    (by simpa only [Int.cast_zero, zero_add] using t.property)
  simpa only [SequenceCurve, ExtremeReferenceSequence, zero_add, Int.toNat_zero,
    Int.toNat_one, ite_true, one_ne_zero, ite_false, Int.cast_zero, sub_zero,
    ExtremeReferenceSegment, Mix] using h

/-- The two-point polygonal curve has precisely the image of the one line segment. -/
theorem extremeReferenceSequence_range (hS : Convex ℝ S) (best worst : S) :
    Set.range (SequenceCurve hS (ExtremeReferenceSequence best worst)) =
      Set.range (ExtremeReferenceSegment hS best worst) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    let a := Int.fract t
    have ha : a ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    by_cases hA : (⌊t⌋ + 1).toNat = 0
    · by_cases hB : (⌊t⌋).toNat = 0
      · refine ⟨⟨0, by norm_num⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, extremeReferenceSegment_zero]
        exact (mix_self hS best (Int.fract t) _).symm
      · refine ⟨⟨1 - a, sub_nonneg.mpr ha.2, by linarith [ha.1]⟩, ?_⟩
        change Mix hS worst best (1 - a) _ = _
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, ite_false]
        exact (mix_swap hS best worst a ha).symm
    · by_cases hB : (⌊t⌋).toNat = 0
      · refine ⟨⟨a, ha⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, ite_false, ExtremeReferenceSegment]
        rfl
      · refine ⟨⟨1, by norm_num⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_false, extremeReferenceSegment_one]
        exact (mix_self hS worst (Int.fract t) _).symm
  · rintro x ⟨t, rfl⟩
    exact ⟨t.val, extremeReferenceSequence_on_unit hS best worst t⟩

/-- With both extrema attained, the real-parameter curve brackets all points using one segment. -/
theorem extremeReferenceSequence_brackets (hS : Convex ℝ S) {r : S → S → Prop}
    (best worst : S) (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) :
    Continuous (SequenceCurve hS (ExtremeReferenceSequence best worst)) ∧
      ∀ x, ∃ a b : ℝ, r (SequenceCurve hS (ExtremeReferenceSequence best worst) a) x ∧
        r x (SequenceCurve hS (ExtremeReferenceSequence best worst) b) := by
  refine ⟨sequenceCurve_continuous hS _, fun x => ⟨0, 1, ?_, ?_⟩⟩
  · rw [extremeReferenceSequence_curve_zero]
    exact hbest x
  · rw [extremeReferenceSequence_curve_one]
    exact hworst x

/-- **Problem 2.14(a):** a continuous countable connect-the-dots curve brackets all preferences. -/
theorem problem_2_14a {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ q : ℕ → NonnegativeOrthant k,
      Continuous (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q) ∧
        ∀ x, ∃ a b : ℝ,
          r (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q a) x ∧
          r x (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q b) := by
  classical
  let : Nonempty (NonnegativeOrthant k) := ⟨⟨0, le_rfl⟩⟩
  by_cases he : (∃ best, ∀ x, r best x) ∧ ∃ worst, ∀ x, r x worst
  · obtain ⟨⟨best, hbest⟩, ⟨worst, hworst⟩⟩ := he
    exact ⟨ExtremeReferenceSequence best worst, extremeReferenceSequence_brackets
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) best worst hbest hworst⟩
  · obtain ⟨v, hv⟩ := proposition_1_15 k hr hc
    exact exists_bracketing_polygonal_curve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) hv

/-- **Problem 2.14(b):** every bracketed class meets the connected curve. -/
theorem problem_2_14b {X : Type*} [TopologicalSpace X] {r : X → X → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) (f : ℝ → X) (hf : Continuous f)
    (hb : ∀ x, ∃ a b : ℝ, r (f a) x ∧ r x (f b)) :
    ∀ x, ∃ t, Indifferent r (f t) x := by
  intro x
  obtain ⟨a, b, ha, hb⟩ := hb x
  exact indifference_on_connected_image hr hc f hf x ha hb

/-- Parts (a)-(b) produce a connected curve image meeting every indifference class. -/
theorem problem_2_14ab {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ f : ℝ → NonnegativeOrthant k, Continuous f ∧
      IsPreconnected (Set.range f) ∧ ∀ x, ∃ t, Indifferent r (f t) x := by
  obtain ⟨q, hq, hb⟩ := problem_2_14a hr hc
  exact ⟨_, hq, isPreconnected_range hq, problem_2_14b hr hc _ hq hb⟩

/-- **Problem 2.14:** the complete curve, recursive-scale, and indifference-extension proof. -/
theorem problem_2_14 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u := by
  obtain ⟨f, hf, hZ, hcover⟩ := problem_2_14ab hr hc
  let Z := Set.range f
  let : Nonempty Z := ⟨⟨f 0, Set.mem_range_self 0⟩⟩
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp hZ
  let rz : Z → Z → Prop := fun x y => r x.val y.val
  have hrz : Rational rz := ⟨fun x y => hr.1 x.val y.val,
    fun x y z => hr.2 x.val y.val z.val⟩
  have hcz : ContinuousPreference rz :=
    hc.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  obtain ⟨q, hq, he⟩ := exists_dense_sample_with_extremes rz
  have hcomplete := problem_2_14_recursive_completion hrz hcz q hq he
  let v := SampledWeightedUtility rz q DyadicWeight
  have hu : Represents (RecursiveUtility v q) rz := hcomplete.2.1
  have huc : Continuous (RecursiveUtility v q) := hcomplete.2.2.1
  have hclasses : ∀ x, ∃ z : Z, Indifferent r z.val x := by
    intro x
    obtain ⟨t, ht⟩ := hcover x
    exact ⟨⟨f t, Set.mem_range_self t⟩, ht⟩
  obtain ⟨u, hrep, hcont, _⟩ := problem_2_14c hr hc Z hZ (RecursiveUtility v q) hu huc hclasses
  exact ⟨u, hrep, hcont⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Recovering homothetic preference from one indifference curve

Kreps I, Problem 2.13, p. 48. Under continuity, strict monotonicity and
homotheticity, the indifference class of any nonzero bundle determines every
comparison. The origin's singleton class is a degenerate exception. The result
is stated in any finite dimension, hence includes the book's two-good case.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- A representation identifies indifference with equality of utility values. -/
theorem indifferent_iff_utility_eq {X : Type*} {r : X → X → Prop} {u : X → ℝ}
    (hu : Represents u r) (x y : X) : Indifferent r x y ↔ u x = u y := by
  constructor
  · intro h
    exact le_antisymm ((hu y x).mp h.2) ((hu x y).mp h.1)
  · intro h
    exact ⟨(hu x y).mpr h.ge, (hu y x).mpr h.le⟩

/-- Positive homogeneous functions agreeing on their unit class agree everywhere. -/
theorem homogeneous_unit_class_unique {k : ℕ} {u v : NonnegativeOrthant k → ℝ}
    (hu : HomogeneousUtility u) (hv : HomogeneousUtility v)
    (hpos : ∀ x, x ≠ OrthantZero k → 0 < u x)
    (hclass : ∀ x, u x = 1 ↔ v x = 1) : u = v := by
  funext x
  by_cases hx : x = OrthantZero k
  · subst x
    rw [homogeneousUtility_origin hu, homogeneousUtility_origin hv]
  · have hux := hpos x hx
    let t : ℝ≥0 := .mk (u x)⁻¹ (inv_nonneg.mpr hux.le)
    have hut : u (ScaleBundle t x) = 1 := by
      rw [hu]
      exact inv_mul_cancel₀ (ne_of_gt hux)
    have hvt := (hclass (ScaleBundle t x)).mp hut
    rw [hv] at hvt
    change (u x)⁻¹ * v x = 1 at hvt
    calc
      u x = u x * ((u x)⁻¹ * v x) := by rw [hvt, mul_one]
      _ = v x := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hux), one_mul]

/-- Normalize a homogeneous representation so that a specified nonzero bundle has value one. -/
theorem normalized_homogeneous_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    (hm : StrictlyMonotonePreference r) {p : NonnegativeOrthant k} (hp : p ≠ OrthantZero k) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u ∧
      u p = 1 ∧ ∀ x, x ≠ OrthantZero k → 0 < u x := by
  obtain ⟨u, hu, huc, huh⟩ := problem_2_12 hr hc hh
  have hup : 0 < u p := by
    have h := (strict_iff_utility_lt hu _ _).mp (hm p (OrthantZero k) p.property hp)
    simpa only [homogeneousUtility_origin huh] using h
  have hrep : Represents (fun x => u x / u p) r := by
    intro x y
    exact (hu x y).trans (div_le_div_iff_of_pos_right hup).symm
  have hhom : HomogeneousUtility (fun x => u x / u p) := by
    intro t x
    change u (ScaleBundle t x) / u p = (t : ℝ) * (u x / u p)
    rw [huh]
    ring
  refine ⟨fun x => u x / u p, hrep, huc.div_const _, hhom, div_self (ne_of_gt hup), ?_⟩
  intro x hx
  have h := (strict_iff_utility_lt hrep _ _).mp (hm x (OrthantZero k) x.property hx)
  simpa only [homogeneousUtility_origin hhom] using h

/-- **Problem 2.13, homothetic case:** one nonzero indifference class identifies all preferences. -/
theorem problem_2_13_homothetic {k : ℕ}
    {r s : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hs : Rational s)
    (hrc : ContinuousPreference r) (hsc : ContinuousPreference s)
    (hrh : HomotheticPreference r) (hsh : HomotheticPreference s)
    (hrm : StrictlyMonotonePreference r) (hsm : StrictlyMonotonePreference s)
    {p : NonnegativeOrthant k} (hp : p ≠ OrthantZero k)
    (hclass : IndifferenceClass r p = IndifferenceClass s p) : r = s := by
  obtain ⟨u, hu, _, huh, hup, hupos⟩ := normalized_homogeneous_representation hr hrc hrh hrm hp
  obtain ⟨v, hv, _, hvh, hvp, _⟩ := normalized_homogeneous_representation hs hsc hsh hsm hp
  have huv : u = v := by
    apply homogeneous_unit_class_unique huh hvh hupos
    intro x
    have h : Indifferent r x p ↔ Indifferent s x p := Set.ext_iff.mp hclass x
    rw [indifferent_iff_utility_eq hu, indifferent_iff_utility_eq hv, hup, hvp] at h
    exact h
  funext x y
  exact propext ((hu x y).trans (huv ▸ (hv x y).symm))

/-- The origin's class is always a singleton under strict monotonicity, so it is exceptional. -/
theorem strictlyMonotone_origin_class {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hc : Complete r) (hm : StrictlyMonotonePreference r) :
    IndifferenceClass r (OrthantZero k) = {OrthantZero k} := by
  ext x
  change Indifferent r x (OrthantZero k) ↔ x = OrthantZero k
  constructor
  · intro hx
    by_contra hne
    exact (hm x (OrthantZero k) x.property hne).2 hx.2
  · intro hx
    subst x
    exact ⟨complete_refl hc _, complete_refl hc _⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quantifiers over utility representations

Kreps I, Problem 2.1 and Table 2.1, p. 45. The ordinal rows have an `all`
forward implication and a `some` converse. Existence of a representation is
explicit when interpreting an `all` statement as an equivalence, preventing
vacuous conclusions for unrepresentable preferences. Continuity, quasi-linearity,
and continuous degree-one homogeneity instead admit the indicated `some` forms.
The strict-convex-to-strict-concave box excluded by the book is not asserted.
The additive row is completed from primitive assumptions in `AdditiveRepresentationQuantifiers`.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : X → X → Prop}

/-- `All` in the representation columns of Table 2.1. -/
def EveryRepresentation (r : X → X → Prop) (P : (X → ℝ) → Prop) : Prop :=
  ∀ u, Represents u r → P u

/-- `Some` in the representation columns of Table 2.1. -/
def SomeRepresentation (r : X → X → Prop) (P : (X → ℝ) → Prop) : Prop :=
  ∃ u, Represents u r ∧ P u

/-- An ordinal property gives both quantifiers once at least one representation exists. -/
theorem representation_quantifiers_of_invariance {P : Prop} {Q : (X → ℝ) → Prop}
    (hex : ∃ u, Represents u r) (hQ : ∀ u, Represents u r → (P ↔ Q u)) :
    (P ↔ EveryRepresentation r Q) ∧ (P ↔ SomeRepresentation r Q) := by
  obtain ⟨u₀, hu₀⟩ := hex
  constructor
  · exact ⟨fun hp u hu => (hQ u hu).mp hp, fun hall => (hQ u₀ hu₀).mpr (hall u₀ hu₀)⟩
  · constructor
    · intro hp
      exact ⟨u₀, hu₀, (hQ u₀ hu₀).mp hp⟩
    · rintro ⟨u, hu, hqu⟩
      exact (hQ u hu).mpr hqu

/-- Table 2.1, monotonicity: `all` forward and `some` backward. -/
theorem table_monotone [PartialOrder X] (hex : ∃ u, Represents u r) :
    (MonotonePreference r ↔ EveryRepresentation r Monotone) ∧
      (MonotonePreference r ↔ SomeRepresentation r Monotone) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_2_monotone hu)

/-- Table 2.1, strict monotonicity: `all` forward and `some` backward. -/
theorem table_strictlyMonotone [PartialOrder X] (hex : ∃ u, Represents u r) :
    (StrictlyMonotonePreference r ↔ EveryRepresentation r StrictMono) ∧
      (StrictlyMonotonePreference r ↔ SomeRepresentation r StrictMono) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_2_strict hu)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- Table 2.1, convexity and quasi-concavity: `all` forward and `some` backward. -/
theorem table_quasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (ConvexPreference hS r ↔ EveryRepresentation r (QuasiConcaveUtility hS)) ∧
      (ConvexPreference hS r ↔ SomeRepresentation r (QuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex (fun _ hu => (proposition_2_8b_quasi hu).symm)

/-- Table 2.1, semi-strict convexity: `all` forward and `some` backward. -/
theorem table_semiStrictlyQuasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (SemiStrictlyConvexPreference hS r ↔
      EveryRepresentation r (SemiStrictlyQuasiConcaveUtility hS)) ∧
      (SemiStrictlyConvexPreference hS r ↔
        SomeRepresentation r (SemiStrictlyQuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex
    (fun _ hu => (proposition_2_8b_semiStrict hu).symm)

/-- Table 2.1, strict convexity and strict quasi-concavity: `all` and `some`. -/
theorem table_strictlyQuasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (StrictlyConvexPreference hS r ↔ EveryRepresentation r (StrictlyQuasiConcaveUtility hS)) ∧
      (StrictlyConvexPreference hS r ↔ SomeRepresentation r (StrictlyQuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex (fun _ hu => (proposition_2_8b_strict hu).symm)

/-- Table 2.1, a `some` concave representation implies convex preference. -/
theorem table_concave_converse (hS : Convex ℝ S) {r : S → S → Prop}
    (h : SomeRepresentation r (ConcaveUtility hS)) : ConvexPreference hS r := by
  obtain ⟨u, hu, hcu⟩ := h
  exact proposition_2_8a_concave hu hcu

/-- Table 2.1, a `some` strictly concave representation implies strict convexity. -/
theorem table_strictlyConcave_converse (hS : Convex ℝ S) {r : S → S → Prop}
    (h : SomeRepresentation r (StrictlyConcaveUtility hS)) : StrictlyConvexPreference hS r := by
  obtain ⟨u, hu, hcu⟩ := h
  exact proposition_2_8a_strict hu hcu

/-- Table 2.1, continuity: `some` in both directions. -/
theorem table_continuous (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ↔ SomeRepresentation r Continuous := proposition_2_9 k hr

/-- Table 2.1, weak separability: the exact given utility has the factorized form. -/
theorem table_weaklySeparable {I : Type*} {B : I → Type*} {L : Type*}
    [DecidableEq I] [Finite I] [Nonempty (BlockBundle B L)]
    {r : BlockBundle B L → BlockBundle B L → Prop} (hex : ∃ u, Represents u r) :
    (WeaklySeparable r ↔ EveryRepresentation r WeakSeparabilityRepresentation) ∧
      (WeaklySeparable r ↔ SomeRepresentation r WeakSeparabilityRepresentation) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_12 hu)

/-- Exact additive form of a given utility, as opposed to ordinal additive representability. -/
def AdditiveForm {I : Type*} [Fintype I] {B : I → Type*} (u : (∀ i, B i) → ℝ) : Prop :=
  ∃ w : ∀ i, B i → ℝ, u = AdditiveUtility w

/-- Table 2.1, the `some` additive representation implies strong separability. -/
theorem table_additive_converse {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (h : SomeRepresentation r AdditiveForm) :
    StronglySeparable r := by
  obtain ⟨u, hu, w, rfl⟩ := h
  exact proposition_2_14_additive hu

/-- The existential table entry is exactly additive representability. -/
theorem some_additiveForm_iff {I : Type*} [Fintype I] {B : I → Type*}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} :
    SomeRepresentation r AdditiveForm ↔ AdditivelyRepresentable r := by
  constructor
  · rintro ⟨u, hu, w, rfl⟩
    exact ⟨w, hu⟩
  · rintro ⟨w, hw⟩
    exact ⟨AdditiveUtility w, hw, w, rfl⟩

/-- Exact quasi-linear form uses money coefficient one. -/
def QuasiLinearForm (U : X × ℝ≥0 → ℝ) : Prop :=
  ∃ u : X → ℝ, U = QuasiLinearUtility u

/-- The existential quasi-linear table entry is exactly quasi-linearity. -/
theorem some_quasiLinearForm_iff {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop} :
    SomeRepresentation r QuasiLinearForm ↔ QuasiLinear r := by
  constructor
  · rintro ⟨U, hU, u, rfl⟩
    exact ⟨u, hU⟩
  · rintro ⟨u, hu⟩
    exact ⟨QuasiLinearUtility u, hu, u, rfl⟩

/-- Table 2.1, the three money properties and normalized quasi-linearity: `some` both ways. -/
theorem table_quasiLinear [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    (OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r) ↔
      SomeRepresentation r QuasiLinearForm :=
  (proposition_2_16 hr).symm.trans some_quasiLinearForm_iff.symm

/-- Table 2.1, continuous homothetic preference: `some` continuous homogeneous utility. -/
theorem table_homogeneous (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    (ContinuousPreference r ∧ HomotheticPreference r) ↔
      SomeRepresentation r (fun u => Continuous u ∧ HomogeneousUtility u) :=
  proposition_2_19 k hr

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The region identified by a quasi-linear indifference curve

Kreps I, Problem 2.13, p. 48. With nonnegative money, an indifference curve need
not intersect every goods fiber. It identifies all comparisons between bundles
whose goods occur somewhere on that curve, at arbitrary nonnegative money levels.
The curve's projection is exactly a subutility sublevel set.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r s : (X × ℝ≥0) → (X × ℝ≥0) → Prop}

/-- Goods bundles that appear on the specified indifference curve at some feasible balance. -/
def CurveGoods (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) (p : X × ℝ≥0) : Set X :=
  {x | ∃ m : ℝ≥0, Indifferent r (x, m) p}

/-- A quasi-linear indifference curve is the graph of the compensating money balance. -/
theorem quasiLinear_class_iff {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r)
    (p q : X × ℝ≥0) :
    Indifferent r q p ↔ (q.2 : ℝ) = QuasiLinearUtility u p - u q.1 := by
  rw [indifferent_iff_utility_eq hu]
  unfold QuasiLinearUtility
  constructor <;> intro h <;> linarith

/-- Nonnegative money restricts the curve's goods projection to a subutility sublevel set. -/
theorem curveGoods_iff_subutility_le {u : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (p : X × ℝ≥0) (x : X) :
    x ∈ CurveGoods r p ↔ u x ≤ QuasiLinearUtility u p := by
  constructor
  · rintro ⟨m, hm⟩
    have he := (quasiLinear_class_iff hu p (x, m)).mp hm
    have hn : 0 ≤ (m : ℝ) := m.property
    change (m : ℝ) = QuasiLinearUtility u p - u x at he
    linarith
  · intro hx
    let m : ℝ≥0 := .mk (QuasiLinearUtility u p - u x) (sub_nonneg.mpr hx)
    exact ⟨m, (quasiLinear_class_iff hu p (x, m)).mpr rfl⟩

/-- Equal curves calibrate both subutilities up to one constant on their goods projection. -/
theorem quasiLinear_class_offset {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    {x : X} (hx : x ∈ CurveGoods r p) : v x - u x = v p.1 - u p.1 := by
  obtain ⟨m, hm⟩ := hx
  have hs : Indifferent s (x, m) p := (Set.ext_iff.mp hclass (x, m)).mp hm
  have he := (indifferent_iff_utility_eq hu (x, m) p).mp hm
  have hf := (indifferent_iff_utility_eq hv (x, m) p).mp hs
  change u x + (m : ℝ) = u p.1 + p.2 at he
  change v x + (m : ℝ) = v p.1 + p.2 at hf
  linarith

/-- **Problem 2.13:** the curve identifies all money levels over its goods projection. -/
theorem problem_2_13_quasiLinear_identified {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    {x y : X} (hx : x ∈ CurveGoods r p) (hy : y ∈ CurveGoods r p) (m n : ℝ≥0) :
    r (x, m) (y, n) ↔ s (x, m) (y, n) := by
  have hdx := quasiLinear_class_offset hu hv p hclass hx
  have hdy := quasiLinear_class_offset hu hv p hclass hy
  rw [hu, hv]
  change u y + (n : ℝ) ≤ u x + m ↔ v y + (n : ℝ) ≤ v x + m
  constructor <;> intro h <;> linarith

/-- If the curve intersects every goods fiber, it identifies the entire quasi-linear preference. -/
theorem quasiLinear_identified_of_full_projection {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    (hfull : ∀ x, x ∈ CurveGoods r p) : r = s := by
  funext a b
  exact propext (problem_2_13_quasiLinear_identified hu hv p hclass (hfull a.1) (hfull b.1)
    a.2 b.2)

/-- Goods outside the projection give bundles strictly above the curve at every feasible balance. -/
theorem quasiLinear_outside_projection {u : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (p : X × ℝ≥0)
    {x : X} (hx : x ∉ CurveGoods r p) (m : ℝ≥0) : Strict r (x, m) p := by
  have hg : QuasiLinearUtility u p < u x :=
    lt_of_not_ge (fun h => hx ((curveGoods_iff_subutility_le hu p x).mpr h))
  apply (strict_iff_utility_lt hu _ _).mpr
  change QuasiLinearUtility u p < u x + (m : ℝ)
  exact hg.trans_le (le_add_of_nonneg_right m.property)

/-- Continuous subutility gives continuous quasi-linear utility on goods and nonnegative money. -/
theorem quasiLinearUtility_continuous [TopologicalSpace X] {u : X → ℝ}
    (hu : Continuous u) : Continuous (QuasiLinearUtility u) :=
  (hu.comp continuous_fst).add (NNReal.continuous_coe.comp continuous_snd)

/-- Strictly increasing subutility gives strict monotonicity in the product order. -/
theorem quasiLinearUtility_strictMono [PartialOrder X] {u : X → ℝ}
    (hu : StrictMono u) : StrictMono (QuasiLinearUtility u) := by
  intro a b hab
  have hg : u a.1 ≤ u b.1 := hu.monotone hab.le.1
  have hm : (a.2 : ℝ) ≤ b.2 := NNReal.coe_le_coe.mpr hab.le.2
  by_contra hn
  have hn' : u b.1 + (b.2 : ℝ) ≤ u a.1 + a.2 := le_of_not_gt hn
  have hge : u a.1 = u b.1 := by linarith
  have hme : (a.2 : ℝ) = b.2 := by linarith
  have hgoods : a.1 = b.1 := by
    by_contra hne
    exact (ne_of_lt (hu (lt_of_le_of_ne hab.le.1 hne))) hge
  exact hab.ne (Prod.ext hgoods (NNReal.coe_injective hme))

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Positive linear utility on two goods

Kreps I, Problem 2.9a, p. 47. Positive coefficients give monotone, strictly monotone,
locally insatiable, convex, semi-strictly convex and continuous preferences, but
not strictly convex preferences. Indifference curves are the feasible portions
of straight lines with slope `-α/β`.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The two-good linear utility in Problem 2.9a. -/
def TwoGoodLinearUtility (α β : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  α * x.val 0 + β * x.val 1

/-- Utility of a mixture is the mixture of utilities. -/
theorem twoGoodLinearUtility_mix (α β : ℝ) (x y : NonnegativeOrthant 2)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    TwoGoodLinearUtility α β (Mix (convex_Ici (0 : Fin 2 → ℝ)) x y a ha) =
      a * TwoGoodLinearUtility α β x + (1 - a) * TwoGoodLinearUtility α β y := by
  change α * (a * x.val 0 + (1 - a) * y.val 0) +
    β * (a * x.val 1 + (1 - a) * y.val 1) =
    a * (α * x.val 0 + β * x.val 1) + (1 - a) * (α * y.val 0 + β * y.val 1)
  ring

/-- Linear utility is concave, with equality in Jensen's inequality. -/
theorem twoGoodLinearUtility_concave (α β : ℝ) :
    ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) (TwoGoodLinearUtility α β) :=
  fun x y a ha => (twoGoodLinearUtility_mix α β x y a ha).ge

/-- Linear utility is continuous on the entire closed orthant. -/
theorem twoGoodLinearUtility_continuous (α β : ℝ) : Continuous (TwoGoodLinearUtility α β) :=
  (continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)).add
    (continuous_const.mul ((continuous_apply 1).comp continuous_subtype_val))

/-- Positive coefficients make every nontrivial coordinatewise increase strictly beneficial. -/
theorem twoGoodLinearUtility_strictMono {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictMono (TwoGoodLinearUtility α β) := by
  intro x y hxy
  have h0 := mul_le_mul_of_nonneg_left (hxy.le 0) hα.le
  have h1 := mul_le_mul_of_nonneg_left (hxy.le 1) hβ.le
  by_contra h
  have hsum : α * y.val 0 + β * y.val 1 ≤ α * x.val 0 + β * x.val 1 := le_of_not_gt h
  have he0 : α * x.val 0 = α * y.val 0 := by linarith
  have he1 : β * x.val 1 = β * y.val 1 := by linarith
  apply hxy.ne
  apply Subtype.ext
  funext j
  fin_cases j
  · exact mul_left_cancel₀ (ne_of_gt hα) he0
  · exact mul_left_cancel₀ (ne_of_gt hβ) he1

/-- Two distinct bundles on the same line refute strict convexity. -/
theorem twoGoodLinearPreference_not_strictlyConvex {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) := by
  let x := PairBundle β 0 hβ.le le_rfl
  let y := PairBundle 0 α le_rfl hα.le
  have hne : x ≠ y := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant 2 => z.val 0) h
    have hβ0 : β = 0 := by simpa [x, y, PairBundle] using he
    exact (ne_of_gt hβ) hβ0
  have hx : TwoGoodLinearUtility α β x = α * β := by
    simp [x, TwoGoodLinearUtility, PairBundle]
  have hy : TwoGoodLinearUtility α β y = α * β := by
    simp [y, TwoGoodLinearUtility, PairBundle, mul_comm]
  have hxy : UtilityPref (TwoGoodLinearUtility α β) x y := by
    change TwoGoodLinearUtility α β y ≤ TwoGoodLinearUtility α β x
    rw [hx, hy]
  intro h
  have hs := h x y hne hxy (1 / 2) (by constructor <;> norm_num)
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  have hm := (strict_iff_utility_lt hu _ _).mp hs
  norm_num [TwoGoodLinearUtility, Mix, x, y, PairBundle, smul_eq_mul] at hm
  nlinarith

/-- Linear utility is degree-one homogeneous, including at the origin. -/
theorem twoGoodLinearUtility_homogeneous (α β : ℝ) :
    HomogeneousUtility (TwoGoodLinearUtility α β) := by
  intro t x
  change α * ((t : ℝ) * x.val 0) + β * ((t : ℝ) * x.val 1) =
    (t : ℝ) * (α * x.val 0 + β * x.val 1)
  ring

/-- Each indifference curve is a straight line intersected with the nonnegative orthant. -/
theorem twoGoodLinear_indifference_curve (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (p x : NonnegativeOrthant 2) :
    Indifferent (UtilityPref (TwoGoodLinearUtility α β)) x p ↔
      x.val 1 = (TwoGoodLinearUtility α β p - α * x.val 0) / β := by
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  rw [indifferent_iff_utility_eq hu, eq_div_iff hβ]
  unfold TwoGoodLinearUtility
  constructor <;> intro h <;> nlinarith

/-- **Problem 2.9a:** all seven properties, including failure of strict convexity. -/
theorem problem_2_9a {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    MonotonePreference (UtilityPref (TwoGoodLinearUtility α β)) ∧
    StrictlyMonotonePreference (UtilityPref (TwoGoodLinearUtility α β)) ∧
    LocallyInsatiable (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) ∧
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (TwoGoodLinearUtility α β)) ∧
    ContinuousPreference (UtilityPref (TwoGoodLinearUtility α β)) := by
  have hu : Represents (TwoGoodLinearUtility α β) (UtilityPref (TwoGoodLinearUtility α β)) :=
    fun _ _ => Iff.rfl
  have hs := (proposition_2_2_strict hu).mpr (twoGoodLinearUtility_strictMono hα hβ)
  have hc := twoGoodLinearUtility_concave α β
  exact ⟨strictlyMonotone_monotone (proposition_1_3a _).1 hs, hs,
    strictAllIncrease_locallyInsatiable (strictlyMonotone_strictAllIncrease (by decide) hs),
    proposition_2_8a_concave hu hc, twoGoodLinearPreference_not_strictlyConvex hα hβ,
    (proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc),
    proposition_2_9_forward hu (twoGoodLinearUtility_continuous α β)⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Utility from the measure of a lower preference contour

Ingredients for Kreps I, Problem 2.15. A finite measure positive on every nonempty
open set gives a representation on a connected domain. A continuous numerical
representation identifies the construction with a cumulative distribution,
which proves upper semicontinuity. Null indifference classes suffice for continuity.
The book's Lebesgue-positivity assumption is handled by a separate orthant bridge.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {r : X → X → Prop}

/-- The finite-measure construction `u(x) = μ(NBT(x))` in Problem 2.15. -/
noncomputable def MeasureUtility (μ : Measure X) (r : X → X → Prop) (x : X) : ℝ :=
  μ.real (NoBetterThan r x)

/-- Transitivity gives inclusion of lower contours and hence weakly increasing measure utility. -/
theorem measureUtility_mono (μ : Measure X) [IsFiniteMeasure μ] (ht : TransitivePref r)
    {x y : X} (hxy : r x y) : MeasureUtility μ r y ≤ MeasureUtility μ r x :=
  measureReal_mono (fun z hz => ht x y z hxy hz)

/-- A strict rank interval contains a nonempty open set and therefore positive measure. -/
theorem measureUtility_strict [TopologicalSpace X] [OpensMeasurableSpace X]
    [PreconnectedSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) {x y : X} (hxy : Strict r x y) :
    MeasureUtility μ r y < MeasureUtility μ r x := by
  obtain ⟨z, hxz, hzy⟩ := exists_strict_between hr hc hxy
  have ho := (continuousPreference_openStrictContours hc y).1.inter
    (continuousPreference_openStrictContours hc x).2
  have hpos := ho.measure_pos μ ⟨z, hzy, hxz⟩
  have hsub : StrictlyBetterThan r y ∩ StrictlyWorseThan r x ⊆
      NoBetterThan r x \ NoBetterThan r y := fun _ h => ⟨h.2.1, h.1.2⟩
  have hdiff : 0 < μ (NoBetterThan r x \ NoBetterThan r y) :=
    hpos.trans_le (measure_mono hsub)
  have hreal : 0 < μ.real (NoBetterThan r x \ NoBetterThan r y) :=
    ENNReal.toReal_pos (ne_of_gt hdiff) (measure_ne_top μ _)
  have hnsub : NoBetterThan r y ⊆ NoBetterThan r x := fun w hw => hr.2 x y w hxy.1 hw
  rw [measureReal_sdiff hnsub (((proposition_1_14c hr).mp hc y).1.measurableSet)] at hreal
  exact sub_pos.mp hreal

/-- Positive mass on nonempty opens suffices for the finite-measure representation. -/
theorem measureUtility_represents [TopologicalSpace X] [OpensMeasurableSpace X]
    [PreconnectedSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) : Represents (MeasureUtility μ r) r := by
  intro x y
  constructor
  · exact measureUtility_mono μ hr.2
  · intro h
    by_contra hxy
    have hyx : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact not_lt_of_ge h (measureUtility_strict μ hr hc hyx)

/-- A continuous representation expresses lower-contour mass as cumulative mass of real ranks. -/
theorem measureUtility_eq_distribution [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} (hu : Represents u r) (huc : Continuous u) (x : X) :
    MeasureUtility μ r x = LowerDistribution (μ.map u) (u x) := by
  unfold LowerDistribution
  rw [map_measureReal_apply huc.measurable isClosed_Iic.measurableSet]
  change μ.real (NoBetterThan r x) = μ.real (u ⁻¹' Set.Iic (u x))
  congr 1
  ext y
  exact hu x y

/-- A continuous representation makes finite lower-contour measure upper semicontinuous. -/
theorem measureUtility_upperSemicontinuous [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : Represents u r) (huc : Continuous u) : UpperSemicontinuous (MeasureUtility μ r) := by
  have he : MeasureUtility μ r = fun x => LowerDistribution (μ.map u) (u x) :=
    funext (measureUtility_eq_distribution μ hu huc)
  rw [he]
  exact (lowerDistribution_upperSemicontinuous (μ.map u)).comp huc

/-- Zero mass on an indifference class is exactly zero mass at its represented rank. -/
theorem measureUtility_rank_atom [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} (hu : Represents u r) (huc : Continuous u) (x : X) :
    (μ.map u) {u x} = μ (IndifferenceClass r x) := by
  rw [Measure.map_apply huc.measurable isClosed_singleton.measurableSet]
  congr 1
  ext y
  exact (indifferent_iff_utility_eq hu y x).symm

/-- Null indifference classes give continuity at the corresponding bundles. -/
theorem measureUtility_continuousAt_of_null_class [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Represents u r)
    (huc : Continuous u) (x : X) (hx : μ (IndifferenceClass r x) = 0) :
    ContinuousAt (MeasureUtility μ r) x := by
  have he : MeasureUtility μ r = fun y => LowerDistribution (μ.map u) (u y) :=
    funext (measureUtility_eq_distribution μ hu huc)
  rw [he]
  have ha : (μ.map u) {u x} = 0 := (measureUtility_rank_atom μ hu huc x).trans hx
  exact (lowerDistribution_continuousAt (μ.map u) (u x) ha).comp huc.continuousAt

/-- If every indifference class has zero measure, the finite-measure utility is continuous. -/
theorem measureUtility_continuous_of_null_classes [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Represents u r)
    (huc : Continuous u) (hnull : ∀ x, μ (IndifferenceClass r x) = 0) :
    Continuous (MeasureUtility μ r) :=
  continuous_iff_continuousAt.mpr (fun x =>
    measureUtility_continuousAt_of_null_class μ hu huc x (hnull x))

/-- The representation and upper-semicontinuity conclusions on the book's orthant domain. -/
theorem problem_2_15_openPos {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hr : Rational r) (hc : ContinuousPreference r) :
    Represents (MeasureUtility μ r) r ∧ UpperSemicontinuous (MeasureUtility μ r) := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  exact ⟨measureUtility_represents μ hr hc, measureUtility_upperSemicontinuous μ hu huc⟩

/-- A sufficient continuity condition in **Problem 2.15**, stated on indifference classes. -/
theorem problem_2_15_continuity {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ]
    (hr : Rational r) (hc : ContinuousPreference r)
    (hnull : ∀ x, μ (IndifferenceClass r x) = 0) : Continuous (MeasureUtility μ r) := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  exact measureUtility_continuous_of_null_classes μ hu huc hnull

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Why the representation table needs `some` rather than `all`

Kreps I, Problem 2.1, Table 2.1, p. 45. Increasing transformations preserve the
preference but need not preserve concavity, continuity, exact additive form,
the quasi-linear money normalization, or degree-one homogeneity.
The additive example has three nontrivial commodity blocks and continuous preference.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : X → X → Prop}

/-- Adding a constant preserves every ordinal comparison. -/
theorem represents_add_constant {u : X → ℝ} (hu : Represents u r) (c : ℝ) :
    Represents (fun x => u x + c) r := by
  intro x y
  simpa only [add_le_add_iff_right] using hu x y

/-- Multiplication by a positive constant preserves every ordinal comparison. -/
theorem represents_mul_positive {u : X → ℝ} (hu : Represents u r) {c : ℝ} (hc : 0 < c) :
    Represents (fun x => c * u x) r := by
  intro x y
  simpa only [mul_le_mul_iff_right₀ hc] using hu x y

/-- Concavity can hold for one representation and fail for another of the same convex preference. -/
theorem table_concave_not_all :
    ConvexPreference (convex_Ici (0 : ℝ)) (UtilityPref (fun x : OneGood => x.val)) ∧
      SomeRepresentation (UtilityPref (fun x : OneGood => x.val))
        (ConcaveUtility (convex_Ici (0 : ℝ))) ∧
      ¬EveryRepresentation (UtilityPref (fun x : OneGood => x.val))
        (ConcaveUtility (convex_Ici (0 : ℝ))) := by
  have hu : Represents (fun x : OneGood => x.val) (UtilityPref (fun x : OneGood => x.val)) :=
    fun _ _ => Iff.rfl
  refine ⟨proposition_2_8a_concave hu identityUtility_concave,
    ⟨_, hu, identityUtility_concave⟩, ?_⟩
  intro hall
  exact convexWarp_not_concave
    (hall _ (proposition_1_20 hu convexWarp_strictMono))

/-- Convexity need not give even one concave representation, despite continuous preference. -/
theorem table_convex_not_some_concave :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref PlateauProductUtility) ∧
      ContinuousPreference (UtilityPref PlateauProductUtility) ∧
      ¬SomeRepresentation (UtilityPref PlateauProductUtility)
        (ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ))) :=
  ⟨problem_2_8a_first.2.1, problem_2_8a_first.2.2.1,
    plateauProductPreference_no_concave_representation⟩

/-- Continuity of preference guarantees a continuous representation, but not continuity of all. -/
theorem table_continuous_not_all :
    ContinuousPreference (UtilityPref (fun x : OneGood => x.val)) ∧
      SomeRepresentation (UtilityPref (fun x : OneGood => x.val)) Continuous ∧
      ¬EveryRepresentation (UtilityPref (fun x : OneGood => x.val)) Continuous := by
  have hu : Represents (fun x : OneGood => x.val) (UtilityPref (fun x : OneGood => x.val)) :=
    fun _ _ => Iff.rfl
  refine ⟨continuousPreference_of_continuous_utility continuous_subtype_val,
    ⟨_, hu, continuous_subtype_val⟩, ?_⟩
  intro hall
  exact jumpUtility_not_continuous
    (hall _ (proposition_1_20 hu jumpUtility_strictMono))

/-- Doubling a quasi-linear utility destroys its required money coefficient of one. -/
theorem doubled_quasiLinear_not_form [Nonempty X] (u : X → ℝ) :
    ¬QuasiLinearForm (fun p => 2 * QuasiLinearUtility u p) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rintro ⟨v, he⟩
  have h0 := congrArg (fun U => U (x, 0)) he
  have h1 := congrArg (fun U => U (x, 1)) he
  norm_num [QuasiLinearUtility] at h0 h1
  linarith

/-- For every quasi-linear preference on a nonempty goods domain, `all` is false. -/
theorem table_quasiLinear_not_all [Nonempty X]
    {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop} (hq : QuasiLinear r) :
    ¬EveryRepresentation r QuasiLinearForm := by
  obtain ⟨u, hu⟩ := hq
  intro hall
  exact doubled_quasiLinear_not_form u
    (hall _ (represents_mul_positive hu (by norm_num : (0 : ℝ) < 2)))

/-- Shifting a homogeneous representation by one violates the required value at the origin. -/
theorem shifted_homogeneous_not_homogeneous {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hh : HomogeneousUtility u) : ¬HomogeneousUtility (fun x => u x + 1) := by
  intro hs
  have hzero := homogeneousUtility_origin hh
  have hshift := homogeneousUtility_origin hs
  change u (OrthantZero k) + 1 = 0 at hshift
  linarith

/-- An ordinal homogeneous representation cannot make every representation homogeneous. -/
theorem homogeneous_not_every_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} {u : NonnegativeOrthant k → ℝ}
    (hu : Represents u r) (hh : HomogeneousUtility u) :
    ¬EveryRepresentation r HomogeneousUtility := by
  intro hall
  exact shifted_homogeneous_not_homogeneous hh (hall _ (represents_add_constant hu 1))

/-- Table 2.1, continuous homogeneous representation is `some`, never `all`. -/
theorem table_homogeneous_not_all {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r) :
    ¬EveryRepresentation r (fun u => Continuous u ∧ HomogeneousUtility u) := by
  obtain ⟨u, hu, _, huh⟩ := (proposition_2_19 k hr).mp ⟨hc, hh⟩
  intro hall
  exact homogeneous_not_every_representation hu huh (fun v hv => (hall v hv).2)

/-- Total quantity of three independent nonnegative commodities, in additive form. -/
def ThreeCommodityTotal (x : Fin 3 → ℝ≥0) : ℝ :=
  AdditiveUtility (fun (_ : Fin 3) (a : ℝ≥0) => (a : ℝ)) x

/-- Total quantity is nonnegative. -/
theorem threeCommodityTotal_nonneg (x : Fin 3 → ℝ≥0) : 0 ≤ ThreeCommodityTotal x := by
  change 0 ≤ ∑ i : Fin 3, (x i : ℝ)
  exact Finset.sum_nonneg (fun i _ => (x i).property)

/-- Squaring total quantity preserves its preference because all its values are nonnegative. -/
theorem squared_threeCommodityTotal_represents :
    Represents (fun x => ThreeCommodityTotal x ^ 2) (UtilityPref ThreeCommodityTotal) := by
  intro x y
  exact (sq_le_sq₀ (threeCommodityTotal_nonneg y) (threeCommodityTotal_nonneg x)).symm

/-- A nonzero cross difference rules out every exact additive decomposition of the square. -/
theorem squared_threeCommodityTotal_not_additive :
    ¬AdditiveForm (fun x => ThreeCommodityTotal x ^ 2) := by
  rintro ⟨w, he⟩
  have h00 := congrArg (fun U => U (![0, 0, 0] : Fin 3 → ℝ≥0)) he
  have h10 := congrArg (fun U => U (![1, 0, 0] : Fin 3 → ℝ≥0)) he
  have h01 := congrArg (fun U => U (![0, 1, 0] : Fin 3 → ℝ≥0)) he
  have h11 := congrArg (fun U => U (![1, 1, 0] : Fin 3 → ℝ≥0)) he
  norm_num [ThreeCommodityTotal, AdditiveUtility, Fin.sum_univ_succ] at h00 h10 h01 h11
  linarith

/-- Every commodity in the additive counterexample is nontrivial, independently of its context. -/
theorem threeCommodityTotal_nontrivial (i : Fin 3) :
    NontrivialBlock (UtilityPref ThreeCommodityTotal) i := by
  refine ⟨1, 0, fun _ => 0, ?_⟩
  change (ThreeCommodityTotal (Function.update (fun _ => 0) i 0) ≤
      ThreeCommodityTotal (Function.update (fun _ => 0) i 1)) ∧
    ¬(ThreeCommodityTotal (Function.update (fun _ => 0) i 1) ≤
      ThreeCommodityTotal (Function.update (fun _ => 0) i 0))
  fin_cases i <;>
    norm_num [ThreeCommodityTotal, AdditiveUtility, Fin.sum_univ_succ, Function.update]

/-- The counterexample satisfies the substantive three-nontrivial-block hypothesis. -/
theorem threeCommodityTotal_threeNontrivial :
    ThreeNontrivialBlocks (UtilityPref ThreeCommodityTotal) :=
  ⟨0, 1, 2, by decide, by decide, by decide, threeCommodityTotal_nontrivial 0,
    threeCommodityTotal_nontrivial 1, threeCommodityTotal_nontrivial 2⟩

/-- The additive counterexample's preference is rational, continuous, and strongly separable. -/
theorem threeCommodityTotal_preference_properties :
    Rational (UtilityPref ThreeCommodityTotal) ∧
      ContinuousPreference (UtilityPref ThreeCommodityTotal) ∧
      StronglySeparable (UtilityPref ThreeCommodityTotal) := by
  have hu : Represents (AdditiveUtility (fun (_ : Fin 3) (a : ℝ≥0) => (a : ℝ)))
      (UtilityPref ThreeCommodityTotal) := fun _ _ => Iff.rfl
  exact ⟨proposition_1_3a ThreeCommodityTotal,
    continuousPreference_of_additive hu (fun _ => NNReal.continuous_coe),
    proposition_2_14_additive hu⟩

/-- Strong separability need not make every representation additive, even with three active blocks.
-/
theorem table_additive_not_all :
    SomeRepresentation (UtilityPref ThreeCommodityTotal) AdditiveForm ∧
      ¬EveryRepresentation (UtilityPref ThreeCommodityTotal) AdditiveForm := by
  refine ⟨⟨ThreeCommodityTotal, (fun _ _ => Iff.rfl), (fun _ a => (a : ℝ)), rfl⟩, ?_⟩
  intro hall
  exact squared_threeCommodityTotal_not_additive (hall _ squared_threeCommodityTotal_represents)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Algebra of three normalized independent utility factors

Preparation for Kreps I, Proposition 2.14. If the three baseline axes have the
same numerical scale, independence makes the induced two-factor operation
symmetric. Pair substitutions give associativity and the medial identity
whenever the pair values are attained on the common axis. These are derived
identities of the original utility, rather than additional representation axioms.
-/

namespace Kreps.PreferenceProperties

variable {A B C : Type*} {u : A × B × C → ℝ}

/-- First-factor independence transports utility equalities. -/
theorem threeFactor_first_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (a a' : A) (b b' : B) (c c' : C) :
    u (a, b, c) = u (a, b', c') ↔ u (a', b, c) = u (a', b', c') := by
  have h := threeFactor_first_indifferent hi a a' b b' c c'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

/-- Second-factor independence transports utility equalities. -/
theorem threeFactor_second_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (b b' : B) (a a' : A) (c c' : C) :
    u (a, b, c) = u (a', b, c') ↔ u (a, b', c) = u (a', b', c') := by
  have h := threeFactor_second_indifferent hi b b' a a' c c'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

/-- Third-factor independence transports utility equalities. -/
theorem threeFactor_third_utility_eq (hi : ThreeFactorIndependent (UtilityPref u))
    (c c' : C) (a a' : A) (b b' : B) :
    u (a, b, c) = u (a', b', c) ↔ u (a, b, c') = u (a', b', c') := by
  have h := threeFactor_third_indifferent hi c c' a a' b b'
  simpa only [indifferent_iff_utility_eq (show Represents u (UtilityPref u) from
    fun _ _ => Iff.rfl)] using h

variable {D : Type*} {v : D × D × D → ℝ} {f : D → ℝ} {e : D}

/-- The baseline axes agree with one common numerical scale. -/
def NormalizedThreeAxes (v : D × D × D → ℝ) (f : D → ℝ) (e : D) : Prop :=
  (∀ a, v (a, e, e) = f a) ∧ (∀ a, v (e, a, e) = f a) ∧
    ∀ a, v (e, e, a) = f a

/-- A score can move from the second axis to the third at any fixed first coordinate. -/
theorem normalized_threeFactor_second_third
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (a, e, b) :=
  (threeFactor_first_utility_eq hi e a b e e b).mp ((hn.2.1 b).trans (hn.2.2 b).symm)

/-- A score can move from the first axis to the second at any fixed third coordinate. -/
theorem normalized_threeFactor_first_second
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a c : D) : v (a, e, c) = v (e, a, c) :=
  (threeFactor_third_utility_eq hi e c a e e a).mp ((hn.1 a).trans (hn.2.1 a).symm)

/-- A score can move from the first axis to the third at any fixed second coordinate. -/
theorem normalized_threeFactor_first_third
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (e, b, a) :=
  (threeFactor_second_utility_eq hi e b a e e a).mp ((hn.1 a).trans (hn.2.2 a).symm)

/-- The binary operation on the reference slice is symmetric. -/
theorem normalized_threeFactor_pair_symmetric
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b : D) : v (a, b, e) = v (b, a, e) := by
  calc
    v (a, b, e) = v (a, e, b) := normalized_threeFactor_second_third hi hn a b
    _ = v (e, a, b) := normalized_threeFactor_first_second hi hn a b
    _ = v (b, a, e) := (normalized_threeFactor_first_third hi hn b a).symm

/-- Symmetry of two factors persists at every value of the third factor. -/
theorem normalized_threeFactor_swap_first_two
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c : D) : v (a, b, c) = v (b, a, c) :=
  (threeFactor_third_utility_eq hi e c a b b a).mp
    (normalized_threeFactor_pair_symmetric hi hn a b)

/-- The last two factors use the same binary operation as the first two. -/
theorem normalized_threeFactor_first_base
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (b c : D) : v (e, b, c) = v (b, c, e) :=
  (normalized_threeFactor_first_third hi hn c b).symm.trans
    (normalized_threeFactor_pair_symmetric hi hn c b)

/-- An attained pair value can replace its first two coordinates at any third coordinate. -/
theorem normalized_threeFactor_merge_first
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c p : D) (hp : v (a, b, e) = f p) : v (a, b, c) = v (p, e, c) :=
  (threeFactor_third_utility_eq hi e c a p b e).mp (hp.trans (hn.1 p).symm)

/-- An attained pair value can replace the last two coordinates at any first coordinate. -/
theorem normalized_threeFactor_merge_last
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c q : D) (hq : v (b, c, e) = f q) : v (a, b, c) = v (a, q, e) :=
  (threeFactor_first_utility_eq hi e a b q c e).mp
    ((normalized_threeFactor_first_base hi hn b c).trans (hq.trans (hn.2.1 q).symm))

/-- The binary operation is associative whenever its two intermediate values are attained. -/
theorem normalized_threeFactor_pair_associative
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c p q : D) (hp : v (a, b, e) = f p) (hq : v (b, c, e) = f q) :
    v (p, c, e) = v (a, q, e) := by
  calc
    v (p, c, e) = v (p, e, c) := normalized_threeFactor_second_third hi hn p c
    _ = v (a, b, c) := (normalized_threeFactor_merge_first hi hn a b c p hp).symm
    _ = v (a, q, e) := normalized_threeFactor_merge_last hi hn a b c q hq

/-- The medial identity needs only the four pair values to be attained on the common axis. -/
theorem normalized_threeFactor_pair_medial
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v f e)
    (a b c d p q s t : D)
    (hp : v (a, b, e) = f p) (hq : v (c, d, e) = f q)
    (hs : v (a, c, e) = f s) (ht : v (b, d, e) = f t) :
    v (p, q, e) = v (s, t, e) := by
  have hzero : v (e, b, q) = v (e, c, t) := by
    calc
      v (e, b, q) = v (b, q, e) := normalized_threeFactor_first_base hi hn b q
      _ = v (b, c, d) := (normalized_threeFactor_merge_last hi hn b c d q hq).symm
      _ = v (c, b, d) := normalized_threeFactor_swap_first_two hi hn b c d
      _ = v (c, t, e) := normalized_threeFactor_merge_last hi hn c b d t ht
      _ = v (e, c, t) := (normalized_threeFactor_first_base hi hn c t).symm
  calc
    v (p, q, e) = v (p, e, q) := normalized_threeFactor_second_third hi hn p q
    _ = v (a, b, q) := (normalized_threeFactor_merge_first hi hn a b q p hp).symm
    _ = v (a, c, t) := (threeFactor_first_utility_eq hi e a b c q t).mp hzero
    _ = v (s, e, t) := normalized_threeFactor_merge_first hi hn a c t s hs
    _ = v (s, t, e) := (normalized_threeFactor_second_third hi hn s t).symm

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One quasi-linear curve need not identify the whole preference

Kreps I, Problem 2.13, p. 48. On two nonnegative goods, `x + m` and
`max x (2*x - 1) + m` give continuous, strictly monotone, quasi-linear preferences.
Their indifference curves through `(0,1)` agree. Their rankings of `(2,0)` and
`(0,5/2)` differ. The observed goods projection is precisely `[0,1]`.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The piecewise linear transformation is the maximum of its two affine branches. -/
theorem convexWarp_eq_max (t : ℝ) : ConvexWarp t = max t (2 * t - 1) := by
  unfold ConvexWarp
  split_ifs with h
  · exact (max_eq_left (by linarith)).symm
  · exact (max_eq_right (by linarith)).symm

/-- The branches meet continuously at one. -/
theorem convexWarp_continuous : Continuous ConvexWarp := by
  have he : ConvexWarp = fun t : ℝ => max t (2 * t - 1) := funext convexWarp_eq_max
  rw [he]
  exact continuous_id.max ((continuous_const.mul continuous_id).sub continuous_const)

/-- Linear utility in the non-money good and money. -/
def LinearMoneyUtility : (ℝ≥0 × ℝ≥0) → ℝ := QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ))

/-- The marginal value of the first good rises at one, while money's coefficient stays one. -/
noncomputable def WarpedMoneyUtility : (ℝ≥0 × ℝ≥0) → ℝ :=
  QuasiLinearUtility (fun x : ℝ≥0 => ConvexWarp (x : ℝ))

/-- Both utility functions satisfy continuity and strict product-order monotonicity. -/
theorem linear_warped_utilities_regular :
    Continuous LinearMoneyUtility ∧ StrictMono LinearMoneyUtility ∧
      Continuous WarpedMoneyUtility ∧ StrictMono WarpedMoneyUtility := by
  have hcoe : StrictMono (fun x : ℝ≥0 => (x : ℝ)) := fun _ _ h => NNReal.coe_lt_coe.mpr h
  exact ⟨quasiLinearUtility_continuous NNReal.continuous_coe,
    quasiLinearUtility_strictMono hcoe,
    quasiLinearUtility_continuous (convexWarp_continuous.comp NNReal.continuous_coe),
    quasiLinearUtility_strictMono (convexWarp_strictMono.comp hcoe)⟩

/-- The two preferences have exactly the same indifference curve through `(0,1)`. -/
theorem linear_warped_same_curve :
    IndifferenceClass (UtilityPref LinearMoneyUtility) (0, 1) =
      IndifferenceClass (UtilityPref WarpedMoneyUtility) (0, 1) := by
  have hu : Represents LinearMoneyUtility (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  have hv : Represents WarpedMoneyUtility (UtilityPref WarpedMoneyUtility) := fun _ _ => Iff.rfl
  ext q
  change Indifferent (UtilityPref LinearMoneyUtility) q (0, 1) ↔
    Indifferent (UtilityPref WarpedMoneyUtility) q (0, 1)
  rw [indifferent_iff_utility_eq hu, indifferent_iff_utility_eq hv]
  change (q.1 : ℝ) + (q.2 : ℝ) = 0 + 1 ↔
    ConvexWarp (q.1 : ℝ) + (q.2 : ℝ) = ConvexWarp 0 + 1
  have hv0 : ConvexWarp 0 = 0 := by norm_num [ConvexWarp]
  rw [hv0, zero_add]
  have hm : 0 ≤ (q.2 : ℝ) := q.2.property
  constructor
  · intro h
    have hx : (q.1 : ℝ) ≤ 1 := by linarith
    simpa only [ConvexWarp, ite_eq_left hx] using h
  · intro h
    have hg : (q.1 : ℝ) ≤ ConvexWarp (q.1 : ℝ) := by
      rw [convexWarp_eq_max]
      exact le_max_left _ _
    have hx : (q.1 : ℝ) ≤ 1 := by linarith
    simpa only [ConvexWarp, ite_eq_left hx] using h

/-- The observed goods range ends at one because money cannot be negative. -/
theorem linear_curve_goods :
    CurveGoods (UtilityPref LinearMoneyUtility) (0, 1) = Set.Iic (1 : ℝ≥0) := by
  have hu : Represents (QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ)))
      (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  ext x
  rw [curveGoods_iff_subutility_le hu]
  change (x : ℝ) ≤ (0 : ℝ) + 1 ↔ x ≤ 1
  simpa only [zero_add, NNReal.coe_one] using
    (show (x : ℝ) ≤ ((1 : ℝ≥0) : ℝ) ↔ x ≤ 1 from NNReal.coe_le_coe)

/-- **Problem 2.13:** even continuous, strictly monotone quasi-linear preferences
can share a nonzero indifference curve and disagree on other comparisons. -/
theorem problem_2_13_quasiLinear_nonidentification :
    ∃ r s : (ℝ≥0 × ℝ≥0) → (ℝ≥0 × ℝ≥0) → Prop,
      Rational r ∧ Rational s ∧ ContinuousPreference r ∧ ContinuousPreference s ∧
      StrictlyMonotonePreference r ∧ StrictlyMonotonePreference s ∧
      QuasiLinear r ∧ QuasiLinear s ∧ IndifferenceClass r (0, 1) = IndifferenceClass s (0, 1) ∧
      ¬r (2, 0) (0, 5 / 2) ∧ s (2, 0) (0, 5 / 2) := by
  have hu : Represents LinearMoneyUtility (UtilityPref LinearMoneyUtility) := fun _ _ => Iff.rfl
  have hv : Represents WarpedMoneyUtility (UtilityPref WarpedMoneyUtility) := fun _ _ => Iff.rfl
  obtain ⟨huc, hum, hvc, hvm⟩ := linear_warped_utilities_regular
  refine ⟨UtilityPref LinearMoneyUtility, UtilityPref WarpedMoneyUtility,
    proposition_1_3a _, proposition_1_3a _, proposition_2_9_forward hu huc,
    proposition_2_9_forward hv hvc, (proposition_2_2_strict hu).mpr hum,
    (proposition_2_2_strict hv).mpr hvm, ⟨_, hu⟩, ⟨_, hv⟩, linear_warped_same_curve, ?_, ?_⟩
  · norm_num [UtilityPref, LinearMoneyUtility, QuasiLinearUtility]
  · norm_num [UtilityPref, WarpedMoneyUtility, QuasiLinearUtility, ConvexWarp]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Leontief utility on two goods

Kreps I, Problem 2.9b, p. 47. For positive α and β, `min (x₁/α) (x₂/β)`
gives monotone, locally insatiable, convex, semi-strictly convex and continuous
preferences. Neither strict monotonicity nor strict convexity holds. The two
rays describing each indifference curve are stated as an exact set condition.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

/-- The fixed-proportions utility in Problem 2.9b. -/
noncomputable def LeontiefUtility (α β : ℝ) (x : NonnegativeOrthant 2) : ℝ :=
  min (x.val 0 / α) (x.val 1 / β)

/-- Positive scale parameters give nondecreasing Leontief utility. -/
theorem leontiefUtility_monotone {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Monotone (LeontiefUtility α β) := by
  intro x y hxy
  exact min_le_min (div_le_div_of_nonneg_right (hxy 0) hα.le)
    (div_le_div_of_nonneg_right (hxy 1) hβ.le)

/-- Increasing both goods strictly raises the minimum of their normalized quantities. -/
theorem leontiefPreference_strictAllIncrease {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictAllIncreasePreference (UtilityPref (LeontiefUtility α β)) := by
  intro x y hxy
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hu _ _).mpr
  exact lt_min ((min_le_left _ _).trans_lt (div_lt_div_of_pos_right (hxy 0) hα))
    ((min_le_right _ _).trans_lt (div_lt_div_of_pos_right (hxy 1) hβ))

/-- The minimum of these two affine functions satisfies Jensen's concavity inequality. -/
theorem leontiefUtility_concave (α β : ℝ) :
    ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) (LeontiefUtility α β) := by
  intro x y a ha
  change a * min (x.val 0 / α) (x.val 1 / β) +
    (1 - a) * min (y.val 0 / α) (y.val 1 / β) ≤
    min ((a * x.val 0 + (1 - a) * y.val 0) / α)
      ((a * x.val 1 + (1 - a) * y.val 1) / β)
  apply le_min
  · calc
      _ ≤ a * (x.val 0 / α) + (1 - a) * (y.val 0 / α) := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left _ _) ha.1)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ha.2))
      _ = _ := by ring
  · calc
      _ ≤ a * (x.val 1 / β) + (1 - a) * (y.val 1 / β) := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_right _ _) ha.1)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (sub_nonneg.mpr ha.2))
      _ = _ := by ring

/-- The minimum is continuous, including at its corner and on the coordinate axes. -/
theorem leontiefUtility_continuous (α β : ℝ) : Continuous (LeontiefUtility α β) := by
  have h0 : Continuous (fun x : NonnegativeOrthant 2 => x.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun x : NonnegativeOrthant 2 => x.val 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact (h0.div_const α).min (h1.div_const β)

/-- No amount of the first good raises utility when the second good is absent. -/
theorem leontiefUtility_first_axis {α : ℝ} (hα : 0 < α) (β : ℝ)
    {x : NonnegativeOrthant 2} (hx : x.val 1 = 0) : LeontiefUtility α β x = 0 := by
  unfold LeontiefUtility
  rw [hx, zero_div, min_eq_right (div_nonneg (x.property 0) hα.le)]

/-- The first coordinate axis refutes strict monotonicity. -/
theorem leontiefPreference_not_strictlyMonotone {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ¬StrictlyMonotonePreference (UtilityPref (LeontiefUtility α β)) := by
  let y := PairBundle 1 0 (by norm_num) le_rfl
  have hy : LeontiefUtility α β y = 0 :=
    leontiefUtility_first_axis hα β (by simp [y, PairBundle])
  have hz : LeontiefUtility α β (OrthantZero 2) = 0 := leontiefUtility_first_axis hα β rfl
  have hne : y ≠ OrthantZero 2 := by
    intro h
    have he := congrArg (fun x : NonnegativeOrthant 2 => x.val 0) h
    simp [y, PairBundle, OrthantZero] at he
  intro h
  apply (h y (OrthantZero 2) y.property hne).2
  change LeontiefUtility α β y ≤ LeontiefUtility α β (OrthantZero 2)
  rw [hy, hz]

/-- Mixing two distinct points on the first axis leaves utility zero, refuting strict convexity. -/
theorem leontiefPreference_not_strictlyConvex {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (LeontiefUtility α β)) := by
  let y := PairBundle 1 0 (by norm_num) le_rfl
  have hy : LeontiefUtility α β y = 0 :=
    leontiefUtility_first_axis hα β (by simp [y, PairBundle])
  have hz : LeontiefUtility α β (OrthantZero 2) = 0 := leontiefUtility_first_axis hα β rfl
  have hne : y ≠ OrthantZero 2 := by
    intro h
    have he := congrArg (fun x : NonnegativeOrthant 2 => x.val 0) h
    simp [y, PairBundle, OrthantZero] at he
  have hp : UtilityPref (LeontiefUtility α β) y (OrthantZero 2) := by
    change LeontiefUtility α β (OrthantZero 2) ≤ LeontiefUtility α β y
    rw [hy, hz]
  intro h
  have hs := h y (OrthantZero 2) hne hp (1 / 2) (by constructor <;> norm_num)
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  have hgt := (strict_iff_utility_lt hu _ _).mp hs
  have hm : LeontiefUtility α β
      (Mix (convex_Ici (0 : Fin 2 → ℝ)) y (OrthantZero 2) (1 / 2)
        (by constructor <;> norm_num)) = 0 :=
    leontiefUtility_first_axis hα β (by simp [Mix, y, PairBundle, OrthantZero])
  exact not_lt_of_ge hz.ge (hgt.trans_eq hm)

/-- Leontief utility is degree-one homogeneous. -/
theorem leontiefUtility_homogeneous (α β : ℝ) : HomogeneousUtility (LeontiefUtility α β) := by
  intro t x
  change min (((t : ℝ) * x.val 0) / α) (((t : ℝ) * x.val 1) / β) =
    (t : ℝ) * min (x.val 0 / α) (x.val 1 / β)
  rw [mul_min_of_nonneg (a := (t : ℝ)) _ _ t.property]
  congr 1 <;> ring

/-- A level curve consists of a vertical ray and a horizontal ray meeting at `(αc,βc)`. -/
theorem leontief_indifference_curve {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (p x : NonnegativeOrthant 2) :
    Indifferent (UtilityPref (LeontiefUtility α β)) x p ↔
      (x.val 0 = α * LeontiefUtility α β p ∧ β * LeontiefUtility α β p ≤ x.val 1) ∨
      (x.val 1 = β * LeontiefUtility α β p ∧ α * LeontiefUtility α β p ≤ x.val 0) := by
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  rw [indifferent_iff_utility_eq hu]
  change min (x.val 0 / α) (x.val 1 / β) = LeontiefUtility α β p ↔ _
  constructor
  · intro h
    rcases min_eq_iff.mp h with ⟨he, hle⟩ | ⟨he, hle⟩
    · rw [he] at hle
      exact Or.inl ⟨by simpa [mul_comm] using (div_eq_iff (ne_of_gt hα)).mp he,
        by simpa [mul_comm] using (le_div_iff₀ hβ).mp hle⟩
    · rw [he] at hle
      exact Or.inr ⟨by simpa [mul_comm] using (div_eq_iff (ne_of_gt hβ)).mp he,
        by simpa [mul_comm] using (le_div_iff₀ hα).mp hle⟩
  · rintro (⟨he, hle⟩ | ⟨he, hle⟩)
    · have hd : x.val 0 / α = LeontiefUtility α β p :=
        (div_eq_iff (ne_of_gt hα)).mpr (by simpa [mul_comm] using he)
      rw [hd]
      exact min_eq_left ((le_div_iff₀ hβ).mpr (by simpa [mul_comm] using hle))
    · have hd : x.val 1 / β = LeontiefUtility α β p :=
        (div_eq_iff (ne_of_gt hβ)).mpr (by simpa [mul_comm] using he)
      rw [hd]
      exact min_eq_right ((le_div_iff₀ hα).mpr (by simpa [mul_comm] using hle))

/-- **Problem 2.9b:** all seven requested preference properties. -/
theorem problem_2_9b {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    MonotonePreference (UtilityPref (LeontiefUtility α β)) ∧
    ¬StrictlyMonotonePreference (UtilityPref (LeontiefUtility α β)) ∧
    LocallyInsatiable (UtilityPref (LeontiefUtility α β)) ∧
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (LeontiefUtility α β)) ∧
    ¬StrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref (LeontiefUtility α β)) ∧
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref (LeontiefUtility α β)) ∧
    ContinuousPreference (UtilityPref (LeontiefUtility α β)) := by
  have hu : Represents (LeontiefUtility α β) (UtilityPref (LeontiefUtility α β)) :=
    fun _ _ => Iff.rfl
  have hc := leontiefUtility_concave α β
  exact ⟨(proposition_2_2_monotone hu).mpr (leontiefUtility_monotone hα hβ),
    leontiefPreference_not_strictlyMonotone hα β,
    strictAllIncrease_locallyInsatiable (leontiefPreference_strictAllIncrease hα hβ),
    proposition_2_8a_concave hu hc, leontiefPreference_not_strictlyConvex hα β,
    (proposition_2_8b_semiStrict hu).mp (concaveUtility_semiStrict hc),
    proposition_2_9_forward hu (leontiefUtility_continuous α β)⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Lebesgue-positivity hypothesis in Problem 2.15

Lebesgue measure on the orthant is the ambient product measure pulled back through
the subtype inclusion. Every nonempty relatively open set has positive measure,
including neighborhoods at the boundary. Consequently, the book's condition that
positive-Lebesgue-measure sets have positive `μ`-measure gives the full-support
hypothesis used in the finite-measure utility construction.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory

/-- Lebesgue measure restricted to the nonnegative orthant, as a measure on its subtype. -/
noncomputable def OrthantLebesgue (k : ℕ) : Measure (NonnegativeOrthant k) :=
  (volume : Measure (Fin k → ℝ)).comap Subtype.val

/-- Subtype measure is the ambient measure of the corresponding set of bundles. -/
theorem orthantLebesgue_apply (k : ℕ) (A : Set (NonnegativeOrthant k)) :
    OrthantLebesgue k A = volume (Subtype.val '' A) := by
  exact (MeasurableEmbedding.subtype_coe
    (isClosed_Ici (a := (0 : Fin k → ℝ))).measurableSet).comap_apply volume A

/-- Every relative neighborhood contains an ambient ball inside the orthant. -/
theorem orthant_open_contains_ambient_ball {k : ℕ} {U : Set (NonnegativeOrthant k)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : Fin k → ℝ, ∃ δ > 0, Metric.ball y δ ⊆ Subtype.val '' U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let y := RaisedBundle x (ε / 2) (by positivity)
  have hyx : dist y x ≤ ε / 2 := raisedBundle_dist_le x (by positivity)
  refine ⟨y.val, ε / 4, by positivity, ?_⟩
  intro z hz
  have hzdist : dist z y.val < ε / 4 := hz
  have hznonneg : 0 ≤ z := by
    intro j
    have hcoord := (dist_le_pi_dist z y.val j).trans_lt hzdist
    change |z j - (x.val j + ε / 2)| < ε / 4 at hcoord
    have hlow := (abs_lt.mp hcoord).1
    have hxj := x.property j
    change 0 ≤ x.val j at hxj
    change 0 ≤ z j
    linarith
  let z' : NonnegativeOrthant k := ⟨z, hznonneg⟩
  refine ⟨z', hball ?_, rfl⟩
  change dist z x.val < ε
  have htriangle := dist_triangle z y.val x.val
  change dist y.val x.val ≤ ε / 2 at hyx
  linarith

/-- Relative nonempty opens have positive Lebesgue measure, also at boundary points. -/
theorem orthantLebesgue_open_pos {k : ℕ} {U : Set (NonnegativeOrthant k)}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < OrthantLebesgue k U := by
  obtain ⟨y, δ, hδ, hball⟩ := orthant_open_contains_ambient_ball hU hne
  have hpos := Metric.isOpen_ball.measure_pos (volume : Measure (Fin k → ℝ))
    ⟨y, Metric.mem_ball_self hδ⟩
  rw [orthantLebesgue_apply]
  exact hpos.trans_le (measure_mono hball)

/-- The book's Lebesgue-positivity assumption implies positive mass on nonempty opens. -/
theorem orthant_measure_openPos {k : ℕ} (μ : Measure (NonnegativeOrthant k))
    (hμ : ∀ A, MeasurableSet A → 0 < OrthantLebesgue k A → 0 < μ A) :
    μ.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  exact ne_of_gt (hμ U hU.measurableSet (orthantLebesgue_open_pos hU hne))

/-- **Problem 2.15:** lower-contour measure represents preference and is upper semicontinuous. -/
theorem problem_2_15 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (μ : Measure (NonnegativeOrthant k)) [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → 0 < OrthantLebesgue k A → 0 < μ A)
    (hr : Rational r) (hc : ContinuousPreference r) :
    Represents (MeasureUtility μ r) r ∧ UpperSemicontinuous (MeasureUtility μ r) := by
  let : μ.IsOpenPosMeasure := orthant_measure_openPos μ hμ
  exact problem_2_15_openPos μ hr hc

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local additive scales from independent utility factors

Preparation for Kreps I, Proposition 2.14. The diagonal-inverse mean and its
dyadic cardinal scale give an actual additive representation on a compact
pair domain. The surrounding partial medial identity is enough; its proof
from normalized independent utility factors is supplied separately.
-/

namespace Kreps.PreferenceProperties

/-- The partial medial identity yields a continuous additive scale for pair comparisons. -/
theorem exists_pair_additive_scale_of_partialMedial
    {A B : Type*} [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
    [CompactSpace A] [DenselyOrdered A] [PreconnectedSpace A]
    (G : B → B → ℝ) (f : B → ℝ) (k : A → B) {lo hi : A}
    (hlohi : lo < hi) (hlo : ∀ x, lo ≤ x) (hhi : ∀ x, x ≤ hi)
    (hl : ∀ y, StrictMono (fun x => G (k x) (k y)))
    (hr : ∀ x, StrictMono (fun y => G (k x) (k y)))
    (hc : Continuous (fun p : A × A => G (k p.1) (k p.2)))
    (hs : ∀ x y, G (k x) (k y) = G (k y) (k x))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p)) :
    ∃ φ : A → ℝ, Continuous φ ∧ StrictMono φ ∧ φ lo = 0 ∧ φ hi = 1 ∧
      ∀ a b c d, G (k a) (k b) ≤ G (k c) (k d) ↔ φ a + φ b ≤ φ c + φ d := by
  let F : A → A → ℝ := fun x y => G (k x) (k y)
  have he : ∀ x y, ∃ z, F z z = F x y :=
    utilityDiagonal_attains_pair hl hr (hc.comp (continuous_id.prodMk continuous_id))
  let M := OrderedUtilityMean G f k he hl hr hs (fun _ _ => rfl) hsmall hmed hd
  have hmc : Continuous (fun p : A × A => M.mean p.1 p.2) :=
    diagonalUtilityMean_continuous he hl hr hc
  obtain ⟨φ, hφc, hφm, hφlo, hφhi, hφmean⟩ :=
    exists_continuous_bisymmetricMean_scale M hlohi hlo hhi hmc
  refine ⟨φ, hφc, hφm, hφlo, hφhi, ?_⟩
  intro a b c d
  calc
    G (k a) (k b) ≤ G (k c) (k d) ↔ M.mean a b ≤ M.mean c d :=
      diagonalUtilityMean_comparison he hl hr a b c d
    _ ↔ φ (M.mean a b) ≤ φ (M.mean c d) := hφm.le_iff_le.symm
    _ ↔ φ a + φ b ≤ φ c + φ d := by
      rw [hφmean, hφmean]
      exact div_le_div_iff_of_pos_right (by norm_num)

/-- Normalized independent factors supply the partial medial premise used above. -/
theorem normalized_threeFactor_partialMedial {B : Type*} {v : B × B × B → ℝ}
    {f : B → ℝ} {e : B} (hi : ThreeFactorIndependent (UtilityPref v))
    (hn : NormalizedThreeAxes v f e) :
    PartialUtilityMedial (fun x y => v (x, y, e)) f := by
  intro a b c d p q s t hp hq hs ht
  exact normalized_threeFactor_pair_medial hi hn a b c d p q s t hp hq hs ht

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Restriction to three common scalar-score axes

A common subset of three score ranges defines a scalar three-factor utility.
The restriction inherits independence, continuity and strict coordinate
monotonicity. Baseline normalization gives the same numerical scale on all axes.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- The scalar aggregator restricted to three axes with a common score domain. -/
def CommonThreeScoreUtility (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) (i j l : I)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (p : J × J × J) : ℝ :=
  V (ThreeCoordinateBundle z i j l (Set.inclusion hi p.1)
    (Set.inclusion hj p.2.1) (Set.inclusion hl p.2.2))

/-- Three-factor independence is preserved by restricting each factor through a map. -/
theorem threeFactorIndependent_pullback {A B C D E F : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hr : ThreeFactorIndependent r)
    (f : D → A) (g : E → B) (h : F → C) :
    ThreeFactorIndependent (fun p q : D × E × F =>
      r (f p.1, g p.2.1, h p.2.2) (f q.1, g q.2.1, h q.2.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a a' b b' c c'
    exact hr.1 (f a) (f a') (g b) (g b') (h c) (h c')
  · intro b b' a a' c c'
    exact hr.2.1 (g b) (g b') (f a) (f a') (h c) (h c')
  · intro c c' a a' b b'
    exact hr.2.2 (h c) (h c') (f a) (f a') (g b) (g b')

/-- A common score restriction inherits three-factor independence. -/
theorem commonThreeScoreUtility_independent [Finite I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, S i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) :
    ThreeFactorIndependent (UtilityPref (CommonThreeScoreUtility V z i j l hi hj hl)) :=
  threeFactorIndependent_pullback (stronglySeparable_threeFactor hs z hij hil hjl)
    (Set.inclusion hi) (Set.inclusion hj) (Set.inclusion hl)

/-- Restricting a continuous scalar aggregator to the three common axes is continuous. -/
theorem commonThreeScoreUtility_continuous {V : (∀ i, S i) → ℝ} (hc : Continuous V)
    (z : ∀ i, S i) (i j l : I) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) :
    Continuous (CommonThreeScoreUtility V z i j l hi hj hl) :=
  hc.comp ((threeCoordinateBundle_continuous z i j l).comp
    ((continuous_inclusion hi).prodMap
      ((continuous_inclusion hj).prodMap (continuous_inclusion hl))))

/-- The first restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_first_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) {i j l : I} (hij : i ≠ j) (hil : i ≠ l)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (b c : J) :
    StrictMono (fun a : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  have hx := threeCoordinateBundle_update_first z hij hil
    (Set.inclusion hi x) (Set.inclusion hi x) (Set.inclusion hj b) (Set.inclusion hl c)
  have hy := threeCoordinateBundle_update_first z hij hil
    (Set.inclusion hi x) (Set.inclusion hi y) (Set.inclusion hj b) (Set.inclusion hl c)
  rw [← hx, ← hy]
  exact Function.update_strictMono hxy

/-- The second restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_second_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) {i j l : I} (hjl : j ≠ l)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (a c : J) :
    StrictMono (fun b : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  have hx := threeCoordinateBundle_update_second z hjl
    (Set.inclusion hi a) (Set.inclusion hj x) (Set.inclusion hj x) (Set.inclusion hl c)
  have hy := threeCoordinateBundle_update_second z hjl
    (Set.inclusion hi a) (Set.inclusion hj x) (Set.inclusion hj y) (Set.inclusion hl c)
  rw [← hx, ← hy]
  exact Function.update_strictMono hxy

/-- The third restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_third_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) (i j l : I)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (a b : J) :
    StrictMono (fun c : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  exact Function.update_strictMono hxy

/-- A reference-normalized aggregator has the same numerical scale on all common axes. -/
theorem commonThreeScoreUtility_axes {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (hv : ∀ k (q : S k), V (Function.update z k q) = q.val) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (e : J)
    (he : ∀ k, (z k).val = e.val) :
    NormalizedThreeAxes (CommonThreeScoreUtility V z i j l hi hj hl) Subtype.val e := by
  have hei : Set.inclusion hi e = z i := Subtype.ext (he i).symm
  have hej : Set.inclusion hj e = z j := Subtype.ext (he j).symm
  have hel : Set.inclusion hl e = z l := Subtype.ext (he l).symm
  refine ⟨?_, ?_, ?_⟩
  · intro a
    unfold CommonThreeScoreUtility
    rw [hej, hel]
    have h := threeCoordinateBundle_update_first z hij hil (z i)
      (Set.inclusion hi a) (z j) (z l)
    simp only [ThreeCoordinateBundle, Function.update_eq_self] at h ⊢
    rw [← h, hv]
  · intro a
    unfold CommonThreeScoreUtility
    rw [hei, hel]
    have h := threeCoordinateBundle_update_second z hjl (z i) (z j)
      (Set.inclusion hj a) (z l)
    simp only [ThreeCoordinateBundle, Function.update_eq_self] at h ⊢
    rw [← h, hv]
  · intro a
    unfold CommonThreeScoreUtility
    rw [hei, hej]
    simp only [ThreeCoordinateBundle, Function.update_eq_self, hv]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Atoms can make lower-contour utility discontinuous

Kreps I, Problem 2.15. Adding a unit atom at a nonminimal bundle creates a jump
along any sequence of strictly worse bundles converging to it. Starting with a
finite measure equivalent to ambient Lebesgue measure preserves the book's exact
positivity condition. The counterexample uses the ordinary increasing preference
on one commodity, so even strict monotonicity cannot exclude this problem.
-/

namespace Kreps.PreferenceProperties

open MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {r : X → X → Prop}

/-- A unit atom adds one to lower-contour utility at its own reflexive rank. -/
theorem measureUtility_add_dirac_self (ν : Measure X) [IsFiniteMeasure ν]
    (p : X) (hp : r p p) :
    MeasureUtility (ν + Measure.dirac p) r p = MeasureUtility ν r p + 1 := by
  unfold MeasureUtility
  rw [measureReal_add_apply, Measure.dirac_real_apply_of_mem (s := NoBetterThan r p) hp]

/-- The same atom contributes nothing to a strictly lower rank. -/
theorem measureUtility_add_dirac_below [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] {p x : X} (hpx : Strict r p x) :
    MeasureUtility (ν + Measure.dirac p) r x = MeasureUtility ν r x := by
  unfold MeasureUtility
  rw [measureReal_add_apply, Measure.dirac_real_apply,
    Set.indicator_of_notMem (s := NoBetterThan r x) hpx.2, add_zero]

/-- Approaching an atom from strictly worse bundles witnesses a discontinuity. -/
theorem measureUtility_add_dirac_not_continuousAt [TopologicalSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsFiniteMeasure ν]
    (hr : Rational r) (p : X) (f : ℕ → X)
    (hf : Filter.Tendsto f Filter.atTop (𝓝 p)) (hfp : ∀ n, Strict r p (f n)) :
    ¬ ContinuousAt (MeasureUtility (ν + Measure.dirac p) r) p := by
  intro hc
  have hlim := hc.tendsto.comp hf
  have hbound : ∀ n,
      MeasureUtility (ν + Measure.dirac p) r (f n) ≤ MeasureUtility ν r p := by
    intro n
    rw [measureUtility_add_dirac_below ν (hfp n)]
    exact measureUtility_mono ν hr.2 (hfp n).1
  have hle := le_of_tendsto' hlim hbound
  rw [measureUtility_add_dirac_self ν p (complete_refl hr.1 p)] at hle
  linarith

/-- The numerical quantity of the single commodity. -/
def OneCommodityUtility (x : NonnegativeOrthant 1) : ℝ := x.val 0

/-- One unit of the single commodity, where the counterexample places its atom. -/
def OneCommodityUnit : NonnegativeOrthant 1 := Diagonal ⟨1, by norm_num⟩

/-- A sequence of quantities below one converging to one. -/
noncomputable def OneCommodityApproach (n : ℕ) : NonnegativeOrthant 1 :=
  Diagonal ⟨1 - (1 / 2 : ℝ) ^ n,
    sub_nonneg.mpr (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := n)
      (by norm_num) (by norm_num))⟩

/-- The ordinary one-commodity utility is continuous and strictly increasing. -/
theorem oneCommodityUtility_properties :
    Continuous OneCommodityUtility ∧ StrictMono OneCommodityUtility := by
  refine ⟨(continuous_apply 0).comp continuous_subtype_val, ?_⟩
  intro x y hxy
  have hle := hxy.le 0
  have hne : x.val 0 ≠ y.val 0 := by
    intro he
    apply hxy.ne
    apply Subtype.ext
    funext j
    fin_cases j
    exact he
  exact lt_of_le_of_ne hle hne

/-- The specified sequence converges to the atom bundle. -/
theorem oneCommodityApproach_tendsto :
    Filter.Tendsto OneCommodityApproach Filter.atTop (𝓝 OneCommodityUnit) := by
  have hreal : Filter.Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n)
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hsub : Filter.Tendsto (fun n : ℕ => (⟨1 - (1 / 2 : ℝ) ^ n,
      sub_nonneg.mpr (pow_le_one₀ (a := (1 / 2 : ℝ)) (n := n)
        (by norm_num) (by norm_num))⟩ : Set.Ici (0 : ℝ)))
      Filter.atTop (𝓝 (⟨1, by norm_num⟩ : Set.Ici (0 : ℝ))) :=
    tendsto_subtype_rng.mpr hreal
  exact diagonal_continuous.continuousAt.tendsto.comp hsub

/-- Every quantity in the sequence is strictly worse than one unit. -/
theorem oneCommodityApproach_strict (n : ℕ) :
    Strict (UtilityPref OneCommodityUtility) OneCommodityUnit (OneCommodityApproach n) := by
  change (1 - (1 / 2 : ℝ) ^ n ≤ 1) ∧ ¬ (1 ≤ 1 - (1 / 2 : ℝ) ^ n)
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  constructor <;> linarith

/-- Pulling back a finite measure that dominates Lebesgue null sets preserves positive sets. -/
theorem orthant_comap_positive {k : ℕ} (ν : Measure (Fin k → ℝ))
    (hν : (volume : Measure (Fin k → ℝ)) ≪ ν)
    {A : Set (NonnegativeOrthant k)} (hA : 0 < OrthantLebesgue k A) :
    0 < ν.comap Subtype.val A := by
  have he : ν.comap Subtype.val A = ν (Subtype.val '' A) :=
    (MeasurableEmbedding.subtype_coe
      (isClosed_Ici (a := (0 : Fin k → ℝ))).measurableSet).comap_apply ν A
  rw [he]
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hvol := hν hzero
  rw [← orthantLebesgue_apply] at hvol
  exact ne_of_gt hA hvol

/-- **Problem 2.15:** the book's assumptions allow a discontinuous measure utility. -/
theorem problem_2_15_not_continuous :
    ∃ μ : Measure (NonnegativeOrthant 1), IsFiniteMeasure μ ∧
      (∀ A, MeasurableSet A → 0 < OrthantLebesgue 1 A → 0 < μ A) ∧
      Represents (MeasureUtility μ (UtilityPref OneCommodityUtility))
        (UtilityPref OneCommodityUtility) ∧
      UpperSemicontinuous (MeasureUtility μ (UtilityPref OneCommodityUtility)) ∧
      ¬ Continuous (MeasureUtility μ (UtilityPref OneCommodityUtility)) := by
  obtain ⟨ν, hfinite, hν, _⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (volume : Measure (Fin 1 → ℝ))
  let : IsFiniteMeasure ν := hfinite
  let ν' : Measure (NonnegativeOrthant 1) := ν.comap Subtype.val
  let μ := ν' + Measure.dirac OneCommodityUnit
  have hpos : ∀ A, MeasurableSet A → 0 < OrthantLebesgue 1 A → 0 < μ A := by
    intro A _ hA
    change 0 < (ν' + Measure.dirac OneCommodityUnit) A
    rw [Measure.add_apply]
    exact (orthant_comap_positive ν hν hA).trans_le (le_add_right le_rfl)
  have hr := proposition_1_3a OneCommodityUtility
  have hc := continuousPreference_of_continuous_utility oneCommodityUtility_properties.1
  obtain ⟨hrep, husc⟩ := problem_2_15 μ hpos hr hc
  refine ⟨μ, inferInstance, hpos, hrep, husc, ?_⟩
  intro hcont
  exact measureUtility_add_dirac_not_continuousAt ν' hr OneCommodityUnit
    OneCommodityApproach oneCommodityApproach_tendsto oneCommodityApproach_strict hcont.continuousAt

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A common interval for three nontrivial score blocks

The original preference hypotheses supply an interior reference bundle and
an open numerical interval shared by the three selected block-score ranges.
The scalar restriction has normalized axes on precisely that common scale.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- Three nontrivial blocks admit a common open interval around one reference utility. -/
theorem exists_common_baseline_score_interval [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) (i j l : I)
    (hi : NontrivialBlock r i) (hj : NontrivialBlock r j) (hl : NontrivialBlock r l) :
    ∃ (t : ∀ i, B i) (L R : ℝ), u t ∈ Set.Ioo L R ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t i) ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t j) ∧
      Set.Ioo L R ⊆ Set.range (BaselineScores u t l) := by
  obtain ⟨t, ht⟩ := exists_interior_baseline_scores hr hu hs hc z
  have hni := mem_interior_iff_mem_nhds.mp (ht i hi)
  have hnj := mem_interior_iff_mem_nhds.mp (ht j hj)
  have hnl := mem_interior_iff_mem_nhds.mp (ht l hl)
  obtain ⟨L, R, hLR, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hni (Filter.inter_mem hnj hnl))
  exact ⟨t, L, R, hLR, fun x hx => (hsub hx).1,
    fun x hx => (hsub hx).2.1, fun x hx => (hsub hx).2.2⟩

/-- The original scalar-score construction supplies normalized common axes. -/
theorem scoreAggregator_commonThree_axes [Finite I] (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ Set.range (BaselineScores u z i))
    (hj : J ⊆ Set.range (BaselineScores u z j))
    (hl : J ⊆ Set.range (BaselineScores u z l)) (e : J) (he : e.val = u z) :
    NormalizedThreeAxes
      (CommonThreeScoreUtility (ScoreAggregator u z) (BlockScores (BaselineScores u z) z)
        i j l hi hj hl) Subtype.val e := by
  apply commonThreeScoreUtility_axes _ (scoreAggregator_reference_axis hu hs z)
    hij hil hjl hi hj hl e
  intro k
  exact (baselineScores_reference u z k).trans he.symm

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One common pair operation on all normalized active axes

Independence transports a one-axis indifference through a held-fixed second
coordinate. With three active axes, repeated transports identify every ordered
pair with a fixed anchor pair, including pairs that share an anchor coordinate.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*} {D : Type*}

/-- Utility on two selected coordinates of one fixed surrounding bundle. -/
def CoordinatePairUtility (V : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (k : ∀ i, D → B i) (i j : I) (x y : D) : ℝ :=
  V (Function.update (Function.update z i (k i x)) j (k j y))

/-- All selected axes use the same normalized numerical scale. -/
def NormalizedCoordinateAxes (V : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (k : ∀ i, D → B i) (f : D → ℝ) (T : Set I) : Prop :=
  ∀ i ∈ T, ∀ x, V (Function.update z i (k i x)) = f x

/-- Changing a coordinate that is common to two bundles preserves utility equality. -/
theorem stronglySeparable_common_update_utility_eq [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) {i : I} {x y : ∀ i, B i}
    (hxy : x i = y i) (a : B i) :
    V x = V y ↔ V (Function.update x i a) = V (Function.update y i a) := by
  have h₁ := stronglySeparable_common_update_iff hs hxy a
  have h₂ := stronglySeparable_common_update_iff hs hxy.symm a
  change (V y ≤ V x ↔ _) at h₁
  change (V x ≤ V y ↔ _) at h₂
  constructor
  · intro h
    exact le_antisymm (h₂.mp h.le) (h₁.mp h.ge)
  · intro h
    exact le_antisymm (h₂.mpr h.le) (h₁.mpr h.ge)

/-- The first occupied score can move to any coordinate distinct from the held second one. -/
theorem coordinatePairUtility_move_first [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {i j p : I} (hji : j ≠ i) (hjp : j ≠ p)
    (hi : ∀ x, V (Function.update z i (k i x)) = f x)
    (hp : ∀ x, V (Function.update z p (k p x)) = f x) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k p j x y := by
  apply (stronglySeparable_common_update_utility_eq hs
    (show Function.update z i (k i x) j = Function.update z p (k p x) j by
      simp only [Function.update_of_ne hji, Function.update_of_ne hjp]) (k j y)).mp
  exact (hi x).trans (hp x).symm

/-- The second occupied score can move while the first coordinate is held fixed. -/
theorem coordinatePairUtility_move_second [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {i j q : I} (hij : i ≠ j) (hiq : i ≠ q)
    (hj : ∀ y, V (Function.update z j (k j y)) = f y)
    (hq : ∀ y, V (Function.update z q (k q y)) = f y) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k i q x y := by
  unfold CoordinatePairUtility
  rw [Function.update_comm hij, Function.update_comm hiq]
  exact coordinatePairUtility_move_first hs z k hij hiq hj hq y x

/-- Three distinct active indices provide a spare coordinate outside any occupied pair. -/
theorem three_members_spare {K : Type*} {T : Set K}
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c) (i j : K) :
    ∃ k ∈ T, k ≠ i ∧ k ≠ j := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := ht
  by_cases ha' : a ≠ i ∧ a ≠ j
  · exact ⟨a, ha, ha'⟩
  by_cases hb' : b ≠ i ∧ b ≠ j
  · exact ⟨b, hb, hb'⟩
  refine ⟨c, hc, ?_⟩
  aesop

/-- All ordered pairs of distinct normalized active coordinates have the same pair utility. -/
theorem coordinatePairUtility_same [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {T : Set I} (hn : NormalizedCoordinateAxes V z k f T)
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {i j p q : I} (hi : i ∈ T) (hj : j ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hij : i ≠ j) (hpq : p ≠ q) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k p q x y := by
  by_cases hjp : j ≠ p
  · exact (coordinatePairUtility_move_first hs z k hij.symm hjp (hn i hi) (hn p hp) x y).trans
      (coordinatePairUtility_move_second hs z k hjp.symm hpq (hn j hj) (hn q hq) x y)
  · have hjp' : j = p := not_ne_iff.mp hjp
    obtain ⟨l, hl, hli, hlj⟩ := three_members_spare ht i j
    have hlp : l ≠ p := hjp' ▸ hlj
    calc
      CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k i l x y :=
        coordinatePairUtility_move_second hs z k hij hli.symm (hn j hj) (hn l hl) x y
      _ = CoordinatePairUtility V z k p l x y :=
        coordinatePairUtility_move_first hs z k hli hlp (hn i hi) (hn p hp) x y
      _ = CoordinatePairUtility V z k p q x y :=
        coordinatePairUtility_move_second hs z k hlp.symm hpq (hn l hl) (hn q hq) x y

/-- Replacing the selected pair of a two-coordinate bundle changes only its surrounding context. -/
theorem piecewise_pair_updates (z t : ∀ i, B i) {i j : I} (hij : i ≠ j)
    (a : B i) (b : B j) :
    ({i, j} : Finset I).piecewise (Function.update (Function.update z i a) j b) t =
      Function.update (Function.update t i a) j b := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [hij, Finset.piecewise]
  by_cases hlj : l = j
  · subst l
    simp [Finset.piecewise]
  · simp [hli, hlj, Finset.piecewise]

/-- Pair comparisons on the reference slice hold in every surrounding context. -/
theorem coordinatePairUtility_context_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) (k : ∀ i, D → B i)
    {i j : I} (hij : i ≠ j) (x y x' y' : D) :
    CoordinatePairUtility V z k i j x y ≤ CoordinatePairUtility V z k i j x' y' ↔
      CoordinatePairUtility V t k i j x y ≤ CoordinatePairUtility V t k i j x' y' := by
  have h := hs {i, j}
    (Function.update (Function.update z i (k i x')) j (k j y'))
    (Function.update (Function.update z i (k i x)) j (k j y)) z t
  simpa only [piecewise_pair_updates _ _ hij, UtilityPref, CoordinatePairUtility] using h

/-- One anchor-pair additive scale represents every active pair in every surrounding context. -/
theorem coordinatePairUtility_all_comparisons [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f φ : D → ℝ} {T : Set I} (hn : NormalizedCoordinateAxes V z k f T)
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {p q : I} (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (hφ : ∀ x y x' y', CoordinatePairUtility V z k p q x y ≤
      CoordinatePairUtility V z k p q x' y' ↔ φ x + φ y ≤ φ x' + φ y')
    (t : ∀ i, B i) {i j : I} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (x y x' y' : D) :
    CoordinatePairUtility V t k i j x y ≤ CoordinatePairUtility V t k i j x' y' ↔
      φ x + φ y ≤ φ x' + φ y' := by
  rw [← coordinatePairUtility_context_iff hs z t k hij,
    coordinatePairUtility_same hs z k hn ht hi hj hp hq hij hpq x y,
    coordinatePairUtility_same hs z k hn ht hi hj hp hq hij hpq x' y']
  exact hφ x y x' y'

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A compact interval with attainable pair values

Continuity at an interior normalized baseline supplies a smaller closed
interval whose two-factor utility values remain in the common open score
domain. The midpoint construction can therefore use the derived medial law.
-/

namespace Kreps.PreferenceProperties

/-- Close enough to the normalized baseline, all pair values stay in the common score domain. -/
theorem exists_small_pair_interval {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) (e : J) (he : v (e, e, e) = e.val) :
    ∃ a b : ℝ, a < e.val ∧ e.val < b ∧ Set.Icc a b ⊆ J ∧
      ∀ x y : J, x.val ∈ Set.Icc a b → y.val ∈ Set.Icc a b → v (x, y, e) ∈ J := by
  have hpc : Continuous (fun p : J × J => v (p.1, p.2, e)) :=
    hc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hmem : v (e, e, e) ∈ J := by rw [he]; exact e.property
  have hn := (hJ.preimage hpc).mem_nhds
    (show (e, e) ∈ (fun p : J × J => v (p.1, p.2, e)) ⁻¹' J from hmem)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨W, hW, hWsub⟩ := (mem_nhds_subtype J e (U ∩ V)).mp (Filter.inter_mem hU hV)
  obtain ⟨L, R, heLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hW (hJ.mem_nhds e.property))
  let a := (L + e.val) / 2
  let b := (e.val + R) / 2
  have hal : L < a := by dsimp [a]; linarith [heLR.1]
  have hae : a < e.val := by dsimp [a]; linarith [heLR.1]
  have heb : e.val < b := by dsimp [b]; linarith [heLR.2]
  have hbr : b < R := by dsimp [b]; linarith [heLR.2]
  have hab : Set.Icc a b ⊆ Set.Ioo L R :=
    fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hbr⟩
  refine ⟨a, b, hae, heb, fun x hx => (hLR (hab hx)).2, ?_⟩
  intro x y hx hy
  have hxu : x ∈ U := (hWsub (show x.val ∈ W from (hLR (hab hx)).1)).1
  have hyv : y ∈ V := (hWsub (show y.val ∈ W from (hLR (hab hy)).1)).2
  exact hUV (show (x, y) ∈ U ×ˢ V from ⟨hxu, hyv⟩)

/-- Normalized axes give the baseline identity needed for the compact-interval construction. -/
theorem normalizedThreeAxes_small_pair_interval {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) {e : J}
    (hn : NormalizedThreeAxes v Subtype.val e) :
    ∃ a b : ℝ, a < e.val ∧ e.val < b ∧ Set.Icc a b ⊆ J ∧
      ∀ x y : J, x.val ∈ Set.Icc a b → y.val ∈ Set.Icc a b → v (x, y, e) ∈ J :=
  exists_small_pair_interval hJ hc e (hn.1 e)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Compatibility of pair sums in local additive charts

Strong separability transports two-coordinate comparisons between the centers
of different additive charts. Their remaining coordinate contributions cancel,
so the charts preserve equal pair sums wherever both coordinate domains overlap.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B C : I → Type*}

/-- In a fixed context the unchanged additive contributions cancel from pair indifferences. -/
theorem additiveUtility_pair_eq_iff [Fintype I] (w : ∀ i, B i → ℝ) (z : ∀ i, B i)
    {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    AdditiveUtility w (Function.update (Function.update z i a) j b) =
      AdditiveUtility w (Function.update (Function.update z i a') j b') ↔
        w i a + w j b = w i a' + w j b' := by
  have hformula (p : B i) (q : B j) :
      AdditiveUtility w (Function.update (Function.update z i p) j q) =
        w i p + w j q + ∑ k ∈ ({i, j} : Finset I)ᶜ, w k (z k) := by
    have h := additiveUtility_piecewise w {i, j}
      (Function.update (Function.update z i p) j q) z
    rw [piecewise_pair_updates z z hij p q] at h
    simpa [hij, hij.symm] using h
  rw [hformula, hformula, add_left_inj]

/-- Pair comparisons are independent of the surrounding context, for arbitrary block types. -/
theorem stronglySeparable_pair_comparison_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) {i j : I}
    (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update z i a) j b) ≤
        V (Function.update (Function.update z i a') j b') ↔
      V (Function.update (Function.update t i a) j b) ≤
        V (Function.update (Function.update t i a') j b') := by
  have h := hs {i, j} (Function.update (Function.update z i a') j b')
    (Function.update (Function.update z i a) j b) z t
  simpa only [piecewise_pair_updates _ _ hij, UtilityPref] using h

/-- Pair indifferences are independent of every unvaried coordinate. -/
theorem stronglySeparable_pair_equality_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) {i j : I}
    (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update z i a) j b) =
        V (Function.update (Function.update z i a') j b') ↔
      V (Function.update (Function.update t i a) j b) =
        V (Function.update (Function.update t i a') j b') := by
  simp only [le_antisymm_iff,
    stronglySeparable_pair_comparison_iff hs z t hij a a' b b',
    stronglySeparable_pair_comparison_iff hs z t hij a' a b' b]

/-- A represented additive chart identifies pair indifference with equality of its pair sums. -/
theorem represented_additive_pair_eq_iff [Fintype I]
    (w : ∀ i, B i → ℝ) (e : ∀ i, B i → C i) {V : (∀ i, C i) → ℝ}
    (hu : Represents (AdditiveUtility w) (UtilityPref (fun x => V (fun i => e i (x i)))))
    (z : ∀ i, B i) {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update (fun k => e k (z k)) i (e i a)) j (e j b)) =
        V (Function.update (Function.update (fun k => e k (z k)) i (e i a')) j (e j b')) ↔
      w i a + w j b = w i a' + w j b' := by
  have hv : Represents (fun x : ∀ i, B i => V (fun i => e i (x i)))
      (UtilityPref (fun x : ∀ i, B i => V (fun i => e i (x i)))) := fun _ _ => Iff.rfl
  have h : V (fun k => e k (Function.update (Function.update z i a) j b k)) =
        V (fun k => e k (Function.update (Function.update z i a') j b' k)) ↔
      AdditiveUtility w (Function.update (Function.update z i a) j b) =
        AdditiveUtility w (Function.update (Function.update z i a') j b') :=
    ⟨same_utility_fibers hv hu, same_utility_fibers hu hv⟩
  simpa only [coordinateMap_update] using h.trans (additiveUtility_pair_eq_iff w z hij a a' b b')

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local additive scales from the original preference assumptions

The common-score restriction, attainable compact pair domain and explicit
bisymmetric cardinal construction combine to give a continuous additive scale
for local pair comparisons. No cancellation or representation premise is added.
-/

namespace Kreps.PreferenceProperties

/-- A normalized continuous additive scale on a compact interval around the reference score. -/
def HasLocalCommonPairScale {J : Set ℝ} (v : J × J × J → ℝ) (e : J) : Prop :=
  ∃ (a b : ℝ) (hab : a < b) (hsub : Set.Icc a b ⊆ J) (φ : Set.Icc a b → ℝ),
    a < e.val ∧ e.val < b ∧ Continuous φ ∧ StrictMono φ ∧
      φ ⟨a, le_rfl, hab.le⟩ = 0 ∧ φ ⟨b, hab.le, le_rfl⟩ = 1 ∧
      ∀ x y z w : Set.Icc a b,
        v (Set.inclusion hsub x, Set.inclusion hsub y, e) ≤
          v (Set.inclusion hsub z, Set.inclusion hsub w, e) ↔
          φ x + φ y ≤ φ z + φ w

/-- Normalized continuous independent factors have an actual local additive pair scale. -/
theorem normalizedThreeAxes_local_pair_scale {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) {e : J}
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v Subtype.val e)
    (hleft : ∀ y, StrictMono (fun x => v (x, y, e)))
    (hright : ∀ x, StrictMono (fun y => v (x, y, e))) :
    HasLocalCommonPairScale v e := by
  obtain ⟨a, b, hae, heb, hsub, hsmall⟩ := normalizedThreeAxes_small_pair_interval hJ hc hn
  have hab : a < b := hae.trans heb
  let : PreconnectedSpace (Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let lo : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let up : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let k : Set.Icc a b → J := Set.inclusion hsub
  have hk : StrictMono k := fun _ _ h => h
  have hl : ∀ y, StrictMono (fun x => v (k x, k y, e)) :=
    fun y => (hleft (k y)).comp hk
  have hr : ∀ x, StrictMono (fun y => v (k x, k y, e)) :=
    fun x => (hright (k x)).comp hk
  have hkc : Continuous k := continuous_inclusion hsub
  have hpc : Continuous (fun p : Set.Icc a b × Set.Icc a b => v (k p.1, k p.2, e)) :=
    hc.comp ((hkc.comp continuous_fst).prodMk
      ((hkc.comp continuous_snd).prodMk continuous_const))
  have hdiag : StrictMono (fun p : J => v (p, p, e)) := by
    intro x y hxy
    exact (hleft x hxy).trans (hright y hxy)
  have hpair : ∀ x y, ∃ p : J, v (k x, k y, e) = p.val := by
    intro x y
    exact ⟨⟨v (k x, k y, e), hsmall (k x) (k y) x.property y.property⟩, rfl⟩
  obtain ⟨φ, hφc, hφm, hφlo, hφup, hφpair⟩ :=
    exists_pair_additive_scale_of_partialMedial (fun x y => v (x, y, e)) Subtype.val k
      (lo := lo) (hi := up) hab (fun x => x.property.1) (fun x => x.property.2)
      hl hr hpc (fun x y => normalized_threeFactor_pair_symmetric hi hn (k x) (k y))
      hpair (normalized_threeFactor_partialMedial hi hn) hdiag.injective
  exact ⟨a, b, hab, hsub, φ, hae, heb, hφc, hφm, hφlo, hφup, hφpair⟩

variable {I : Type*} [DecidableEq I] [Finite I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- The original preference assumptions imply a common local additive pair representation. -/
theorem exists_common_local_pair_scale (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : NontrivialBlock r i) (hj : NontrivialBlock r j) (hl : NontrivialBlock r l) :
    ∃ (t : ∀ i, B i) (L R : ℝ)
      (hsi : Set.Ioo L R ⊆ Set.range (BaselineScores u t i))
      (hsj : Set.Ioo L R ⊆ Set.range (BaselineScores u t j))
      (hsl : Set.Ioo L R ⊆ Set.range (BaselineScores u t l)) (e : Set.Ioo L R),
      e.val = u t ∧ HasLocalCommonPairScale
        (CommonThreeScoreUtility (ScoreAggregator u t) (BlockScores (BaselineScores u t) t)
          i j l hsi hsj hsl) e := by
  obtain ⟨t, L, R, he, hsi, hsj, hsl⟩ :=
    exists_common_baseline_score_interval hr hu hs hc z i j l hi hj hl
  let e : Set.Ioo L R := ⟨u t, he⟩
  let q := BlockScores (BaselineScores u t) t
  refine ⟨t, L, R, hsi, hsj, hsl, e, rfl, ?_⟩
  apply normalizedThreeAxes_local_pair_scale isOpen_Ioo
    (commonThreeScoreUtility_continuous (scoreAggregator_continuous hu hs hc t)
      q i j l hsi hsj hsl)
    (commonThreeScoreUtility_independent (scoreAggregator_stronglySeparable hu hs t)
      q hij hil hjl hsi hsj hsl)
    (scoreAggregator_commonThree_axes hu hs t hij hil hjl hsi hsj hsl e rfl)
  · intro y
    exact commonThreeScoreUtility_first_strictMono (scoreAggregator_strictMono hu hs t)
      q hij hil hsi hsj hsl y e
  · intro x
    exact commonThreeScoreUtility_second_strictMono (scoreAggregator_strictMono hu hs t)
      q hjl hsi hsj hsl x e

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# From reference pair comparisons to the full additive representation

Strong separability transports pair indifferences from one reference bundle to
every surrounding context. The finite pair-transfer argument then represents
the entire preference by the sum of those same coordinate scales.
-/

namespace Kreps.PreferenceProperties

/-- Reference pair comparisons in continuous increasing scales determine full additive utility. -/
theorem represents_additive_of_reference_pair_comparisons
    {I : Type*} [DecidableEq I] [Fintype I] {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (z : ∀ i, B i)
    (w : ∀ i, B i → ℝ) (hwc : ∀ i, Continuous (w i)) (hwm : ∀ i, StrictMono (w i))
    (hp : ∀ i j, i ≠ j → ∀ (a a' : B i) (b b' : B j),
      V (Function.update (Function.update z i a) j b) ≤
          V (Function.update (Function.update z i a') j b') ↔
        w i a + w j b ≤ w i a' + w j b') :
    Represents (AdditiveUtility w) (UtilityPref V) := by
  apply represents_additive_of_pair_scale_invariance hm w hwc hwm
  intro x i j a b hij he
  have hpair : V (Function.update (Function.update z i a) j b) =
      V (Function.update (Function.update z i (x i)) j (x j)) :=
    le_antisymm ((hp i j hij a (x i) b (x j)).mpr he.le)
      ((hp i j hij (x i) a (x j) b).mpr he.ge)
  have hcontext := (stronglySeparable_pair_equality_iff hs z x hij a (x i) b (x j)).mp hpair
  simpa only [Function.update_eq_self] using hcontext

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A common interval for all active score coordinates

Finite intersection gives one score neighborhood at every specified interior
reference value. Its coordinate embeddings leave inactive coordinates at their
reference values, so singleton score ranges impose no restriction on the interval.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Finitely many active score ranges have a common interval at any common interior value. -/
theorem exists_all_active_score_interval [Finite I] {T : Set I} {c : ℝ}
    (hc : ∀ i ∈ T, c ∈ interior (S i)) :
    ∃ L R, c ∈ Set.Ioo L R ∧ ∀ i ∈ T, Set.Ioo L R ⊆ S i := by
  classical
  have hn : ∀ᶠ x in nhds c, ∀ i ∈ T, x ∈ S i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ T
    · exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp (hc i hi))
        (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  obtain ⟨L, R, hcLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  exact ⟨L, R, hcLR, fun i hi x hx => hLR hx i hi⟩

/-- Embed a common score in each active coordinate and retain all inactive reference scores. -/
noncomputable def CommonActiveScoreEmbedding (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) (i : I) (x : J) : S i := by
  classical
  exact if hi : i ∈ T then ⟨x.val, hJ i hi x.property⟩ else z i

/-- On active coordinates the common embedding is the ordinary set inclusion. -/
theorem commonActiveScoreEmbedding_active (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) {i : I} (hi : i ∈ T) (x : J) :
    CommonActiveScoreEmbedding z T hJ i x = Set.inclusion (hJ i hi) x := by
  simp only [CommonActiveScoreEmbedding, dite_eq_left hi]

/-- On inactive coordinates the common embedding leaves the reference score fixed. -/
theorem commonActiveScoreEmbedding_inactive (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) {i : I} (hi : i ∉ T) (x : J) :
    CommonActiveScoreEmbedding z T hJ i x = z i := by
  simp only [CommonActiveScoreEmbedding, dite_eq_right hi]

/-- The common embedding is continuous in every coordinate. -/
theorem commonActiveScoreEmbedding_continuous (z : ∀ i, S i) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) (i : I) :
    Continuous (CommonActiveScoreEmbedding z T hJ i) := by
  classical
  by_cases hi : i ∈ T
  · have he : CommonActiveScoreEmbedding z T hJ i = Set.inclusion (hJ i hi) :=
      funext (commonActiveScoreEmbedding_active z T hJ hi)
    rw [he]
    exact continuous_inclusion _
  · have he : CommonActiveScoreEmbedding z T hJ i = fun _ => z i :=
      funext (commonActiveScoreEmbedding_inactive z T hJ hi)
    rw [he]
    exact continuous_const

/-- Numerical axis normalization survives restriction to the common active interval. -/
theorem commonActiveScoreEmbedding_axes [DecidableEq I] {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (hv : ∀ i (q : S i), V (Function.update z i q) = q.val) (T : Set I)
    {J : Set ℝ} (hJ : ∀ i ∈ T, J ⊆ S i) :
    NormalizedCoordinateAxes V z (CommonActiveScoreEmbedding z T hJ) Subtype.val T := by
  intro i hi x
  rw [hv, commonActiveScoreEmbedding_active z T hJ hi]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One local cardinal scale for every active pair

At each specified interior reference value, one compact common score interval
has one continuous strict cardinal scale. Every pair of active coordinates
uses that scale, and independence extends its comparisons to every context.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- A common normalized local scale represents all active pairs in all contexts. -/
def HasAllPairsLocalScale (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) (T : Set I) (c : ℝ) : Prop :=
  ∃ (a b : ℝ) (hab : a < b) (hsub : ∀ i ∈ T, Set.Icc a b ⊆ S i)
    (φ : Set.Icc a b → ℝ), a < c ∧ c < b ∧ Continuous φ ∧ StrictMono φ ∧
      φ ⟨a, le_rfl, hab.le⟩ = 0 ∧ φ ⟨b, hab.le, le_rfl⟩ = 1 ∧
      ∀ (t : ∀ i, S i) (i : I), i ∈ T → ∀ j, j ∈ T → i ≠ j →
        ∀ x y x' y' : Set.Icc a b,
          CoordinatePairUtility V t (CommonActiveScoreEmbedding z T hsub) i j x y ≤
            CoordinatePairUtility V t (CommonActiveScoreEmbedding z T hsub) i j x' y' ↔
            φ x + φ y ≤ φ x' + φ y'

/-- Every specified interior reference admits one cardinal chart for all active coordinate pairs. -/
theorem exists_all_pairs_local_scale [Finite I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hv : ∀ i (q : S i), V (Function.update z i q) = q.val)
    {T : Set I} {c : ℝ} (hz : ∀ i, (z i).val = c)
    (hint : ∀ i ∈ T, c ∈ interior (S i))
    (ht : ∃ p ∈ T, ∃ q ∈ T, ∃ l ∈ T, p ≠ q ∧ p ≠ l ∧ q ≠ l) :
    HasAllPairsLocalScale V z T c := by
  obtain ⟨p, hp, q, hq, l, hl, hpq, hpl, hql⟩ := ht
  obtain ⟨L, R, hcLR, hJ⟩ := exists_all_active_score_interval hint
  let e : Set.Ioo L R := ⟨c, hcLR⟩
  let v := CommonThreeScoreUtility V z p q l (hJ p hp) (hJ q hq) (hJ l hl)
  have hvc : Continuous v := commonThreeScoreUtility_continuous hc z p q l _ _ _
  have hvi : ThreeFactorIndependent (UtilityPref v) :=
    commonThreeScoreUtility_independent hs z hpq hpl hql _ _ _
  have hvn : NormalizedThreeAxes v Subtype.val e :=
    commonThreeScoreUtility_axes z hv hpq hpl hql _ _ _ e hz
  have hvl : ∀ y, StrictMono (fun x => v (x, y, e)) :=
    fun y => commonThreeScoreUtility_first_strictMono hm z hpq hpl _ _ _ y e
  have hvr : ∀ x, StrictMono (fun y => v (x, y, e)) :=
    fun x => commonThreeScoreUtility_second_strictMono hm z hql _ _ _ x e
  obtain ⟨a, b, hab, habJ, φ, hae, heb, hφc, hφm, hφa, hφb, hφpair⟩ :=
    normalizedThreeAxes_local_pair_scale isOpen_Ioo hvc hvi hvn hvl hvr
  have hsub : ∀ i ∈ T, Set.Icc a b ⊆ S i := fun i hi => (habJ.trans (hJ i hi))
  let k := CommonActiveScoreEmbedding z T hsub
  have hpair (x y : Set.Icc a b) : CoordinatePairUtility V z k p q x y =
      v (Set.inclusion habJ x, Set.inclusion habJ y, e) := by
    have hkp : k p x = Set.inclusion (hJ p hp) (Set.inclusion habJ x) := by
      exact commonActiveScoreEmbedding_active z T hsub hp x
    have hkq : k q y = Set.inclusion (hJ q hq) (Set.inclusion habJ y) := by
      exact commonActiveScoreEmbedding_active z T hsub hq y
    have hel : Set.inclusion (hJ l hl) e = z l := Subtype.ext (hz l).symm
    change V (Function.update (Function.update z p (k p x)) q (k q y)) =
      V (ThreeCoordinateBundle z p q l _ _ _)
    rw [hkp, hkq]
    unfold ThreeCoordinateBundle
    rw [hel]
    have heval :
        Function.update (Function.update z p (Set.inclusion (hJ p hp) (Set.inclusion habJ x)))
          q (Set.inclusion (hJ q hq) (Set.inclusion habJ y)) l = z l := by
      simp only [Function.update_of_ne hql.symm, Function.update_of_ne hpl.symm]
    rw [← heval, Function.update_eq_self]
  have hanchor : ∀ x y x' y', CoordinatePairUtility V z k p q x y ≤
      CoordinatePairUtility V z k p q x' y' ↔ φ x + φ y ≤ φ x' + φ y' := by
    intro x y x' y'
    rw [hpair, hpair]
    exact hφpair x y x' y'
  refine ⟨a, b, hab, hsub, φ, hae, heb, hφc, hφm, hφa, hφb, ?_⟩
  intro t i hi j hj hij x y x' y'
  exact coordinatePairUtility_all_comparisons hs z k
    (commonActiveScoreEmbedding_axes z hv T hsub)
    ⟨p, hp, q, hq, l, hl, hpq, hpl, hql⟩ hp hq hpq hanchor t hi hj hij x y x' y'

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local additive charts in the original scalar coordinates

Renormalizing at a specified interior bundle gives a common cardinal scale.
Pulling it back through the baseline coordinate utilities produces open interval
neighborhoods in the original coordinates and a full finite additive chart.
-/

namespace Kreps.PreferenceProperties

/-- An order-connected subset of a real interval is preconnected in its subtype topology. -/
theorem ordConnected_subtype_preconnected {S : Set ℝ} (hS : S.OrdConnected)
    {U : Set S} (hU : U.OrdConnected) : IsPreconnected U := by
  have himage : (Subtype.val '' U).OrdConnected := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    let q : S := ⟨z, hS.out x.property y.property hz⟩
    exact ⟨q, hU.out hx hy hz, rfl⟩
  exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp himage.isPreconnected

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- A local additive chart has open interval coordinate domains containing the reference bundle. -/
def HasLocalScalarAdditiveChart [Fintype I] (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) : Prop :=
  ∃ U : ∀ i, Set (S i), (∀ i, IsOpen (U i) ∧ z i ∈ U i ∧ (U i).OrdConnected) ∧
    ∃ ψ : ∀ i, U i → ℝ, (∀ i, Continuous (ψ i) ∧ StrictMono (ψ i)) ∧
      Represents (AdditiveUtility ψ) (UtilityPref (fun x => V (fun i => (x i).val)))

/-- An interior reference bundle has a full local additive chart
in the original scalar coordinates. -/
theorem exists_local_scalar_additive_chart [Fintype I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i)
    (hint : ∀ i, V z ∈ interior (Set.range (BaselineScores V z i)))
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    HasLocalScalarAdditiveChart V z := by
  let : ∀ i, PreconnectedSpace (S i) :=
    fun i => isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  have hu : Represents V (UtilityPref V) := fun _ _ => Iff.rfl
  let w := BaselineScores V z
  let A := ScoreAggregator V z
  let q₀ := BlockScores w z
  have ht : ∃ i ∈ (Set.univ : Set I), ∃ j ∈ Set.univ, ∃ l ∈ Set.univ,
      i ≠ j ∧ i ≠ l ∧ j ≠ l := by
    obtain ⟨i, j, l, hij, hil, hjl⟩ := hthree
    exact ⟨i, Set.mem_univ i, j, Set.mem_univ j, l, Set.mem_univ l, hij, hil, hjl⟩
  have hlocal := exists_all_pairs_local_scale
    (scoreAggregator_stronglySeparable hu hs z) (scoreAggregator_strictMono hu hs z)
    (scoreAggregator_continuous hu hs hc z) q₀ (scoreAggregator_reference_axis hu hs z)
    (baselineScores_reference V z) (fun i _ => hint i) ht
  obtain ⟨a, b, hab, hsub, φ, hac, hcb, hφc, hφm, _, _, hpair⟩ := hlocal
  let U (i : I) : Set (S i) := (w i) ⁻¹' Set.Ioo a b
  have hwc (i : I) : Continuous (w i) := baselineScores_continuous hc z i
  have hwm (i : I) : StrictMono (w i) := by
    intro x y hxy
    exact hm (Function.update_strictMono hxy)
  have hUo (i : I) : IsOpen (U i) := isOpen_Ioo.preimage (hwc i)
  have hzU (i : I) : z i ∈ U i := by
    change BaselineScores V z i (z i) ∈ Set.Ioo a b
    rw [baselineScores_reference]
    exact ⟨hac, hcb⟩
  have hUc (i : I) : (U i).OrdConnected := Set.ordConnected_Ioo.preimage_mono (hwm i).monotone
  let : ∀ i, PreconnectedSpace (U i) := fun i =>
    isPreconnected_iff_preconnectedSpace.mp (ordConnected_subtype_preconnected (hS i) (hUc i))
  let s (i : I) (x : U i) : Set.Icc a b :=
    ⟨w i x.val, x.property.1.le, x.property.2.le⟩
  let ψ (i : I) (x : U i) : ℝ := φ (s i x)
  have hψc (i : I) : Continuous (ψ i) :=
    hφc.comp (((hwc i).comp continuous_subtype_val).subtype_mk _)
  have hψm (i : I) : StrictMono (ψ i) := by
    intro x y hxy
    exact hφm (hwm i hxy)
  let F (x : ∀ i, U i) : ℝ := V (fun i => (x i).val)
  have hFm : StrictMono F := by
    intro x y hxy
    apply hm
    exact ⟨fun i => hxy.le i, fun h => hxy.not_ge (fun i => h i)⟩
  have hp : ∀ (x : ∀ i, U i) (i j : I) (u : U i) (v : U j), i ≠ j →
      ψ i u + ψ j v = ψ i (x i) + ψ j (x j) →
        F (Function.update (Function.update x i u) j v) = F x := by
    intro x i j u v hij he
    let y : ∀ i, S i := fun i => (x i).val
    let Q := BlockScores w y
    let k := CommonActiveScoreEmbedding q₀ Set.univ hsub
    have hki (t : U i) : k i (s i t) =
        (⟨w i t.val, t.val, rfl⟩ : Set.range (w i)) := by
      exact commonActiveScoreEmbedding_active q₀ Set.univ hsub (Set.mem_univ i) (s i t)
    have hkj (t : U j) : k j (s j t) =
        (⟨w j t.val, t.val, rfl⟩ : Set.range (w j)) := by
      exact commonActiveScoreEmbedding_active q₀ Set.univ hsub (Set.mem_univ j) (s j t)
    have hle := (hpair Q i (Set.mem_univ i) j (Set.mem_univ j) hij
      (s i u) (s j v) (s i (x i)) (s j (x j))).2 he.le
    have hge := (hpair Q i (Set.mem_univ i) j (Set.mem_univ j) hij
      (s i (x i)) (s j (x j)) (s i u) (s j v)).2 he.ge
    have heq := le_antisymm hle hge
    change CoordinatePairUtility A Q k i j (s i u) (s j v) =
      CoordinatePairUtility A Q k i j (s i (x i)) (s j (x j)) at heq
    unfold CoordinatePairUtility at heq
    rw [hki, hkj, hki, hkj] at heq
    have hqi : (⟨w i (x i).val, (x i).val, rfl⟩ : Set.range (w i)) = Q i := rfl
    have hqj : (⟨w j (x j).val, (x j).val, rfl⟩ : Set.range (w j)) = Q j := rfl
    rw [hqi, Function.update_eq_self, hqj, Function.update_eq_self] at heq
    change V (fun l => (Function.update (Function.update x i u) j v l).val) = V y
    rw [coordinateMap_update, coordinateMap_update]
    rw [scoreAggregator_factors hu hs z, scoreAggregator_factors hu hs z]
    rw [blockScores_update, blockScores_update]
    exact heq
  exact ⟨U, fun i => ⟨hUo i, hzU i, hUc i⟩, ψ, fun i => ⟨hψc i, hψm i⟩,
    represents_additive_of_pair_scale_invariance hFm ψ hψc hψm hp⟩

/-- At a point of an open interval product, every strictly increasing baseline score is interior. -/
theorem baselineScores_interior_of_open_strictMono {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i) (i : I) :
    V z ∈ interior (Set.range (BaselineScores V z i)) := by
  let : PreconnectedSpace (S i) :=
    isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  obtain ⟨L, R, hzLR, hLR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((ho i).mem_nhds (z i).property)
  obtain ⟨lo, hLlo, hloz⟩ := exists_between hzLR.1
  obtain ⟨up, hzup, hupR⟩ := exists_between hzLR.2
  let low : S i := ⟨lo, hLR ⟨hLlo, hloz.trans hzLR.2⟩⟩
  let high : S i := ⟨up, hLR ⟨hzLR.1.trans hzup, hupR⟩⟩
  have hlow : BaselineScores V z i low < BaselineScores V z i (z i) :=
    hm (Function.update_strictMono hloz)
  have hhigh : BaselineScores V z i (z i) < BaselineScores V z i high :=
    hm (Function.update_strictMono hzup)
  rw [baselineScores_reference] at hlow hhigh
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds hlow hhigh)
  intro x hx
  exact (baselineScores_ordConnected hc z i).out ⟨low, rfl⟩ ⟨high, rfl⟩
    ⟨hx.1.le, hx.2.le⟩

/-- Every point of an open interval product has an open local additive chart. -/
theorem exists_local_scalar_additive_chart_of_open [Fintype I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    HasLocalScalarAdditiveChart V z :=
  exists_local_scalar_additive_chart hS hs hm hc z
    (baselineScores_interior_of_open_strictMono hS ho hm hc z) hthree

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive charts with ambient real coordinate functions

Open subtype neighborhoods become real interval domains. Their cardinal
functions extend arbitrarily outside those domains, while retaining continuity,
strict increase and the represented preference wherever the chart applies.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] {S : I → Set ℝ}

/-- An additive coordinate chart on an open interval box of the scalar commodity domain. -/
structure ScalarAdditiveChart (V : (∀ i, S i) → ℝ) where
  domain : I → Set ℝ
  coord : I → ℝ → ℝ
  open_domain : ∀ i, IsOpen (domain i)
  interval : ∀ i, (domain i).OrdConnected
  subset : ∀ i, domain i ⊆ S i
  continuous : ∀ i, ContinuousOn (coord i) (domain i)
  increasing : ∀ i, StrictMonoOn (coord i) (domain i)
  represents : Represents (AdditiveUtility (fun i (x : domain i) => coord i x.val))
    (UtilityPref (fun x => V (fun i => Set.inclusion (subset i) (x i))))

/-- Every subtype additive chart gives a chart with ambient real domains
and coordinate functions. -/
theorem localScalarChart_to_scalarAdditiveChart {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i)) (z : ∀ i, S i)
    (h : HasLocalScalarAdditiveChart V z) :
    ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i := by
  classical
  obtain ⟨U, hU, ψ, hψ, hrep⟩ := h
  let D (i : I) : Set ℝ := Subtype.val '' U i
  let f (i : I) (x : U i) : ℝ := x.val.val
  have hfi (i : I) : Function.Injective (f i) :=
    Subtype.val_injective.comp Subtype.val_injective
  let w (i : I) : ℝ → ℝ := Function.extend (f i) (ψ i) (fun _ => 0)
  have hwe (i : I) (x : U i) : w i (f i x) = ψ i x :=
    (hfi i).extend_apply (ψ i) (fun _ => 0) x
  have hDo (i : I) : IsOpen (D i) := (ho i).isOpenMap_subtype_val _ (hU i).1
  have hDi (i : I) : (D i).OrdConnected := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ r hr
    let q : S i := ⟨r, (hS i).out x.property y.property hr⟩
    exact ⟨q, (hU i).2.2.out hx hy hr, rfl⟩
  have hDs (i : I) : D i ⊆ S i := by
    rintro r ⟨x, _, rfl⟩
    exact x.property
  have hwi (i : I) : StrictMonoOn (w i) (D i) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hxw := hwe i ⟨x, hx⟩
    have hyw := hwe i ⟨y, hy⟩
    change w i x.val = _ at hxw
    change w i y.val = _ at hyw
    rw [hxw, hyw]
    exact (hψ i).2 hxy
  have hwc (i : I) : ContinuousOn (w i) (D i) := by
    have hfind : Topology.IsInducing (f i) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    have hrange : f i '' Set.univ = D i := by
      ext r
      constructor
      · rintro ⟨x, _, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    rw [← hrange]
    apply hfind.continuousOn_image_iff.mpr
    have he : w i ∘ f i = ψ i := funext (hwe i)
    rw [he]
    exact (hψ i).1.continuousOn
  let lift (i : I) (x : D i) : U i := ⟨x.property.choose, x.property.choose_spec.1⟩
  have hlift (i : I) (x : D i) : f i (lift i x) = x.val := x.property.choose_spec.2
  have hwL (i : I) (x : D i) : w i x.val = ψ i (lift i x) := by
    rw [← hlift i x]
    exact hwe i (lift i x)
  have hV (x : ∀ i, D i) : (fun i => (lift i (x i)).val) =
      (fun i => Set.inclusion (hDs i) (x i)) := by
    funext i
    exact Subtype.ext (hlift i (x i))
  have hwrep : Represents (AdditiveUtility (fun i (x : D i) => w i x.val))
      (UtilityPref (fun x => V (fun i => Set.inclusion (hDs i) (x i)))) := by
    intro x y
    have hh := hrep (fun i => lift i (x i)) (fun i => lift i (y i))
    simp only [UtilityPref, AdditiveUtility] at hh ⊢
    rw [hV x, hV y] at hh
    simpa only [hwL] using hh
  exact ⟨⟨D, w, hDo, hDi, hDs, hwc, hwi, hwrep⟩,
    fun i => ⟨z i, (hU i).2.1, rfl⟩⟩

/-- Continuous strongly separable utility on open intervals has an additive chart at every point. -/
theorem exists_scalarAdditiveChart_at_of_open [DecidableEq I] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i :=
  localScalarChart_to_scalarAdditiveChart hS ho z
    (exists_local_scalar_additive_chart_of_open hS ho hs hm hc z hthree)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Pair compatibility of scalar additive charts

Charts centered at unrelated bundles give the same pair indifferences on
overlapping coordinate domains. Strong separability transports the comparison
between their centers; the finite additive representations cancel their fixed
coordinate contributions.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

/-- Equal pair sums in one local chart remain equal in every overlapping local chart. -/
theorem ScalarAdditiveChart.pair_compatible (C D : ScalarAdditiveChart V)
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, C.domain i) (t : ∀ i, D.domain i)
    {i j : I} (hij : i ≠ j)
    (x : ℝ) (hx : x ∈ C.domain i ∩ D.domain i)
    (x' : ℝ) (hx' : x' ∈ C.domain i ∩ D.domain i)
    (y : ℝ) (hy : y ∈ C.domain j ∩ D.domain j)
    (y' : ℝ) (hy' : y' ∈ C.domain j ∩ D.domain j)
    (he : C.coord i x + C.coord j y = C.coord i x' + C.coord j y') :
    D.coord i x + D.coord j y = D.coord i x' + D.coord j y' := by
  have hC := represented_additive_pair_eq_iff
    (fun p (q : C.domain p) => C.coord p q.val) (fun p => Set.inclusion (C.subset p))
    C.represents z hij ⟨x, hx.1⟩ ⟨x', hx'.1⟩ ⟨y, hy.1⟩ ⟨y', hy'.1⟩
  have hD := represented_additive_pair_eq_iff
    (fun p (q : D.domain p) => D.coord p q.val) (fun p => Set.inclusion (D.subset p))
    D.represents t hij ⟨x, hx.2⟩ ⟨x', hx'.2⟩ ⟨y, hy.2⟩ ⟨y', hy'.2⟩
  apply hD.mp
  exact (stronglySeparable_pair_equality_iff hs
    (fun p => Set.inclusion (C.subset p) (z p)) (fun p => Set.inclusion (D.subset p) (t p))
    hij ⟨x, C.subset i hx.1⟩ ⟨x', C.subset i hx'.1⟩
    ⟨y, C.subset j hy.1⟩ ⟨y', C.subset j hy'.1⟩).mp (hC.mpr he)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Actual coordinate chart families from strong separability

Fix a reference bundle and one seed additive chart. For each target coordinate,
choose local additive charts along its entire reference slice, preserving that
seed at the reference value. Two other essential coordinates remain fixed and
therefore supply the companion domains needed for cardinal calibration.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

variable (V) (z : ∀ i, S i) (seed : ScalarAdditiveChart V)

/-- Local additive charts along one coordinate slice, with a prescribed common seed chart. -/
structure CoordinateChartFamily (i : I) where
  chart : S i → ScalarAdditiveChart V
  center : ∀ x p, (Function.update z i x p).val ∈ (chart x).domain p
  seed_eq : chart (z i) = seed

variable {V}

/-- Pointwise local additive existence supplies charts along every reference slice. -/
theorem exists_coordinateChartFamily
    (hl : ∀ z : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i)
    (z : ∀ i, S i) (seed : ScalarAdditiveChart V) (hz : ∀ i, (z i).val ∈ seed.domain i)
    (i : I) : Nonempty (CoordinateChartFamily V z seed i) := by
  classical
  choose C hC using hl
  let f (x : S i) := if x = z i then seed else C (Function.update z i x)
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro x p
    by_cases hx : x = z i
    · subst x
      simpa [f] using hz p
    · simpa only [f, ite_eq_right hx] using hC (Function.update z i x) p
  · simp [f]

/-- The target and its ordered pair of companion indices. -/
def companionCoordinateIndex (i j k : I) : Fin 3 → I := ![i, j, k]

omit [DecidableEq I] [Fintype I] in
/-- Distinct selected coordinates give an injective three-coordinate index map. -/
theorem companionCoordinateIndex_injective {i j k : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (companionCoordinateIndex i j k) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [companionCoordinateIndex]

/-- Two fixed companion coordinates turn the actual local charts into a calibration family. -/
def CoordinateChartFamily.toCompanionFamily {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
    {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CompanionChartFamily (S i) where
  domain x p := (F.chart x).domain (companionCoordinateIndex i j k p)
  coord x p := (F.chart x).coord (companionCoordinateIndex i j k p)
  open_domain x p := (F.chart x).open_domain _
  interval x p := (F.chart x).interval _
  continuous x p := (F.chart x).continuous _
  increasing x p := (F.chart x).increasing _
  firstReference := (z j).val
  secondReference := (z k).val
  first_mem x := by
    simpa [companionCoordinateIndex, hij.symm] using F.center x j
  second_mem x := by
    simpa [companionCoordinateIndex, hik.symm] using F.center x k
  pair_compatible x y p q hpq := (F.chart x).pair_compatible (F.chart y) hs
    (fun n => ⟨(Function.update z i x n).val, F.center x n⟩)
    (fun n => ⟨(Function.update z i y n).val, F.center y n⟩)
    ((companionCoordinateIndex_injective hij hik hjk).ne hpq)

/-- The target domains of the companion family stay inside the original coordinate interval. -/
theorem CoordinateChartFamily.companion_target_subset {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ x, (F.toCompanionFamily hs hij hik hjk).domain x 0 ⊆ S i := by
  intro x
  exact (F.chart x).subset i

/-- These actual charts cover the entire target coordinate interval. -/
theorem CoordinateChartFamily.companion_target_cover {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ x ∈ S i, ∃ p, x ∈ (F.toCompanionFamily hs hij hik hjk).domain p 0 := by
  intro x hx
  refine ⟨⟨x, hx⟩, ?_⟩
  simpa [toCompanionFamily, companionCoordinateIndex] using F.center ⟨x, hx⟩ i

/-- The companion-family seed is the originally prescribed target chart. -/
theorem CoordinateChartFamily.companion_seed {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : Fin 3) :
    (F.toCompanionFamily hs hij hik hjk).domain (z i) p =
        seed.domain (companionCoordinateIndex i j k p) ∧
      (F.toCompanionFamily hs hij hik hjk).coord (z i) p =
        seed.coord (companionCoordinateIndex i j k p) := by
  simp [toCompanionFamily, F.seed_eq]

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Ordered pair comparisons in scalar additive charts

The unchanged coordinate contributions cancel from weak comparisons as well
as indifference. Strong separability then transports the local pair formula to
any surrounding context, even when that context is outside the chart.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {B C : I → Type*}

/-- The unvaried additive contributions cancel from a weak pair comparison. -/
theorem additiveUtility_pair_le_iff (w : ∀ i, B i → ℝ) (z : ∀ i, B i)
    {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    AdditiveUtility w (Function.update (Function.update z i a) j b) ≤
      AdditiveUtility w (Function.update (Function.update z i a') j b') ↔
        w i a + w j b ≤ w i a' + w j b' := by
  have hformula (p : B i) (q : B j) :
      AdditiveUtility w (Function.update (Function.update z i p) j q) =
        w i p + w j q + ∑ k ∈ ({i, j} : Finset I)ᶜ, w k (z k) := by
    have h := additiveUtility_piecewise w {i, j}
      (Function.update (Function.update z i p) j q) z
    rw [piecewise_pair_updates z z hij p q] at h
    simpa [hij, hij.symm] using h
  rw [hformula, hformula, add_le_add_iff_right]

/-- A local additive chart compares pairs by their two-coordinate sums. -/
theorem represented_additive_pair_le_iff
    (w : ∀ i, B i → ℝ) (e : ∀ i, B i → C i) {V : (∀ i, C i) → ℝ}
    (hu : Represents (AdditiveUtility w) (UtilityPref (fun x => V (fun i => e i (x i)))))
    (z : ∀ i, B i) {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update (fun k => e k (z k)) i (e i a)) j (e j b)) ≤
        V (Function.update (Function.update (fun k => e k (z k)) i (e i a')) j (e j b')) ↔
      w i a + w j b ≤ w i a' + w j b' := by
  have h := hu (Function.update (Function.update z i a') j b')
    (Function.update (Function.update z i a) j b)
  simp only [UtilityPref, coordinateMap_update] at h
  exact h.trans (additiveUtility_pair_le_iff w z hij a a' b b')

/-- A scalar chart's pair formula holds in every surrounding context. -/
theorem ScalarAdditiveChart.pair_comparison_iff {S : I → Set ℝ} {V : (∀ i, S i) → ℝ}
    (C : ScalarAdditiveChart V) (hs : StronglySeparable (UtilityPref V))
    (center : ∀ p, C.domain p) (t : ∀ p, S p) {i j : I} (hij : i ≠ j)
    (x : ℝ) (hx : x ∈ C.domain i) (x' : ℝ) (hx' : x' ∈ C.domain i)
    (y : ℝ) (hy : y ∈ C.domain j) (y' : ℝ) (hy' : y' ∈ C.domain j) :
    V (Function.update (Function.update t i ⟨x, C.subset i hx⟩) j ⟨y, C.subset j hy⟩) ≤
        V (Function.update (Function.update t i ⟨x', C.subset i hx'⟩) j ⟨y', C.subset j hy'⟩) ↔
      C.coord i x + C.coord j y ≤ C.coord i x' + C.coord j y' := by
  have h := represented_additive_pair_le_iff
    (fun p (q : C.domain p) => C.coord p q.val) (fun p => Set.inclusion (C.subset p))
    C.represents center hij ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩ ⟨y', hy'⟩
  exact (stronglySeparable_pair_comparison_iff hs t
    (fun p => Set.inclusion (C.subset p) (center p)) hij
    ⟨x, C.subset i hx⟩ ⟨x', C.subset i hx'⟩ ⟨y, C.subset j hy⟩ ⟨y', C.subset j hy'⟩).trans h

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Global coordinate scales in common companion units

Pointwise local additive existence, fixed companions and translation gluing
produce a continuous strictly increasing scale on an entire open coordinate
interval. The accompanying chart and companion identities retain the common
cardinal unit needed to synchronize different coordinates.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

variable (V) (z : ∀ i, S i) (seed : ScalarAdditiveChart V)

/-- A global coordinate scale, with its actual local charts and two companion calibrations. -/
structure GlobalCoordinateScale (i j k : I) where
  family : CoordinateChartFamily V z seed i
  slope : S i → ℝ
  positive : ∀ x, 0 < slope x
  seed_unit : slope (z i) = 1
  scale : ℝ → ℝ
  continuous : ContinuousOn scale (S i)
  increasing : StrictMonoOn scale (S i)
  seed_agrees : ∀ x ∈ seed.domain i, scale x = seed.coord i x
  chart_agrees : ∀ p, ∃ B : ℝ, ∀ x ∈ (family.chart p).domain i,
    scale x = (family.chart p).coord i x / slope p + B
  companion_calibration : ∀ q, q = j ∨ q = k → ∀ p, ∃ B : ℝ,
    ∀ x ∈ seed.domain q ∩ (family.chart p).domain q,
      (family.chart p).coord q x = slope p * seed.coord q x + B

variable {V}

/-- All local additive charts glue to a target scale while retaining both fixed companions. -/
theorem exists_globalCoordinateScale
    (hl : ∀ z : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i)
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (z : ∀ i, S i) (seed : ScalarAdditiveChart V) (hz : ∀ i, (z i).val ∈ seed.domain i)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nonempty (GlobalCoordinateScale V z seed i j k) := by
  classical
  obtain ⟨F⟩ := exists_coordinateChartFamily hl z seed hz i
  let G := F.toCompanionFamily hs hij hik hjk
  obtain ⟨slope, β, γ, hpos, hunit, hf, hg⟩ := G.exists_calibration (z i)
  have hne : (G.domain (z i) 0).Nonempty := by
    refine ⟨(z i).val, ?_⟩
    change (z i).val ∈ (F.chart (z i)).domain i
    rw [F.seed_eq]
    exact hz i
  obtain ⟨f, hfc, hfm, hseed, hchart⟩ := G.globalize_target_of_calibration (hS i)
    (F.companion_target_subset hs hij hik hjk) (F.companion_target_cover hs hij hik hjk)
    (z i) hne hpos hunit hf
  refine ⟨{
    family := F
    slope := slope
    positive := hpos
    seed_unit := hunit
    scale := f
    continuous := hfc
    increasing := hfm
    seed_agrees := ?_
    chart_agrees := hchart
    companion_calibration := ?_ }⟩
  · simpa only [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex,
      Matrix.cons_val_zero, F.seed_eq] using hseed
  · intro q hq p
    rcases hq with rfl | rfl
    · refine ⟨β p, ?_⟩
      simpa [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex, F.seed_eq]
        using hf p
    · refine ⟨γ p, ?_⟩
      simpa [G, CoordinateChartFamily.toCompanionFamily, companionCoordinateIndex, F.seed_eq]
        using hg p

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Aligning a new chart through a shared fixed companion

A chart that meets a global coordinate scale and contains the reference value
of one of its calibrated companions has one positive affine slope relative to
both that global coordinate and the companion's seed scale. Two target
coordinates sharing that companion therefore have the same local cardinal unit.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ} {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
  {i j k q : I}

/-- A new local chart aligns simultaneously with a global target scale and a seed companion. -/
theorem GlobalCoordinateScale.align_chart (G : GlobalCoordinateScale V z seed i j k)
    (hs : StronglySeparable (UtilityPref V)) (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hq : q = j ∨ q = k) (hiq : i ≠ q) (C : ScalarAdditiveChart V)
    (center : ∀ p, C.domain p) (x : S i)
    (hx : x.val ∈ C.domain i) (href : (z q).val ∈ C.domain q) :
    ∃ A B D : ℝ, 0 < A ∧
      (∀ r ∈ C.domain i ∩ (G.family.chart x).domain i,
        C.coord i r = A * G.scale r + B) ∧
      ∀ r ∈ (seed.domain q ∩ C.domain q) ∩ (G.family.chart x).domain q,
        C.coord q r = A * seed.coord q r + D := by
  let L := G.family.chart x
  have hxl : x.val ∈ L.domain i := by simpa using G.family.center x i
  have hql : (z q).val ∈ L.domain q := by
    simpa [hiq.symm] using G.family.center x q
  obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair
    ((C.open_domain i).inter (L.open_domain i)) ⟨hx, hxl⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := open_real_set_has_pair
    (((seed.open_domain q).inter (C.open_domain q)).inter (L.open_domain q))
    ⟨⟨hz q, href⟩, hql⟩
  have hp : ∀ a ∈ C.domain i ∩ L.domain i, ∀ b ∈ C.domain i ∩ L.domain i,
      ∀ c ∈ (seed.domain q ∩ C.domain q) ∩ L.domain q,
      ∀ d ∈ (seed.domain q ∩ C.domain q) ∩ L.domain q,
      L.coord i a + L.coord q c = L.coord i b + L.coord q d →
        C.coord i a + C.coord q c = C.coord i b + C.coord q d := by
    intro a ha b hb c hc d hd he
    exact L.pair_compatible C hs
      (fun p => ⟨(Function.update z i x p).val, G.family.center x p⟩) center hiq
      a ⟨ha.2, ha.1⟩ b ⟨hb.2, hb.1⟩ c ⟨hc.2, hc.1.2⟩ d ⟨hd.2, hd.1.2⟩ he
  obtain ⟨A, B, D, hA, htarget, hcompanion⟩ := pair_chart_positive_affine_unique_on
    ((C.interval i).inter (L.interval i))
    (((seed.interval q).inter (C.interval q)).inter (L.interval q))
    ((L.continuous i).mono Set.inter_subset_right)
    ((C.continuous i).mono Set.inter_subset_left)
    ((L.continuous q).mono (fun _ hr => hr.2))
    ((C.continuous q).mono (fun _ hr => hr.1.2))
    ((L.increasing i).mono Set.inter_subset_right)
    ((C.increasing i).mono Set.inter_subset_left)
    ((L.increasing q).mono (fun _ hr => hr.2))
    ((C.increasing q).mono (fun _ hr => hr.1.2)) hp ha hb hab hc hd hcd
  obtain ⟨β, hβ⟩ := G.chart_agrees x
  obtain ⟨γ, hγ⟩ := G.companion_calibration q hq x
  refine ⟨A * G.slope x, B - A * G.slope x * β, A * γ + D,
    mul_pos hA (G.positive x), ?_, ?_⟩
  · intro r hr
    rw [htarget r hr, hβ r hr.2]
    field_simp [(G.positive x).ne']
    ring
  · intro r hr
    rw [hcompanion r hr, hγ r ⟨hr.1.1, hr.2⟩]
    ring

/-- Two positive affine descriptions of the same strict companion have equal slopes. -/
theorem common_companion_affine_slopes_equal {T : Set ℝ} (hT : IsOpen T)
    {x : ℝ} (hx : x ∈ T) {f g : ℝ → ℝ} (hm : StrictMonoOn f T)
    {A B C D : ℝ} (h₁ : ∀ r ∈ T, g r = A * f r + B)
    (h₂ : ∀ r ∈ T, g r = C * f r + D) : A = C := by
  obtain ⟨a, ha, b, hb, hab⟩ := open_real_set_has_pair hT hx
  have hlt := hm ha hb hab
  have h₁a := h₁ a ha
  have h₁b := h₁ b hb
  have h₂a := h₂ a ha
  have h₂b := h₂ b hb
  nlinarith

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Synchronizing global coordinate scales through a common companion

At any pair of coordinate values, a new additive chart overlaps each global
coordinate's slice chart. A shared fixed companion forces their two affine
slopes to agree. The resulting local pair representations globalize along
continuous paths in the two score intervals.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ} {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
  {i j a b c d q : I}

/-- Shared companions synchronize the two global scales on a neighborhood of every pair. -/
theorem globalCoordinateScale_local_pair_comparison
    (G : GlobalCoordinateScale V z seed i a b) (H : GlobalCoordinateScale V z seed j c d)
    (hl : ∀ t : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i)
    (hs : StronglySeparable (UtilityPref V)) (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q)
    (hqG : q = a ∨ q = b) (hqH : q = c ∨ q = d) (p : S i × S j) :
    ∃ N : Set (S i × S j), IsOpen N ∧ p ∈ N ∧
      ∀ r ∈ N, ∀ s ∈ N,
        V (Function.update (Function.update z i r.1) j r.2) ≤
            V (Function.update (Function.update z i s.1) j s.2) ↔
          G.scale r.1.val + H.scale r.2.val ≤ G.scale s.1.val + H.scale s.2.val := by
  let t := Function.update (Function.update z i p.1) j p.2
  obtain ⟨C, hC⟩ := hl t
  let center : ∀ n, C.domain n := fun n => ⟨(t n).val, hC n⟩
  have hiC : p.1.val ∈ C.domain i := by simpa [t, hij] using hC i
  have hjC : p.2.val ∈ C.domain j := by simpa [t] using hC j
  have hqC : (z q).val ∈ C.domain q := by simpa [t, hiq.symm, hjq.symm] using hC q
  obtain ⟨A, B, D, hA, hiA, hqA⟩ := G.align_chart hs hz hqG hiq C center p.1 hiC hqC
  obtain ⟨A', B', D', _, hjA, hqA'⟩ := H.align_chart hs hz hqH hjq C center p.2 hjC hqC
  let L := G.family.chart p.1
  let R := H.family.chart p.2
  have hqL : (z q).val ∈ L.domain q := by simpa [hiq.symm] using G.family.center p.1 q
  have hqR : (z q).val ∈ R.domain q := by simpa [hjq.symm] using H.family.center p.2 q
  let T := ((seed.domain q ∩ C.domain q) ∩ L.domain q) ∩ R.domain q
  have hTo : IsOpen T := (((seed.open_domain q).inter (C.open_domain q)).inter
    (L.open_domain q)).inter (R.open_domain q)
  have hTm : StrictMonoOn (seed.coord q) T :=
    (seed.increasing q).mono (fun _ hr => hr.1.1.1)
  have hAA : A = A' := common_companion_affine_slopes_equal hTo
    ⟨⟨⟨hz q, hqC⟩, hqL⟩, hqR⟩ hTm
    (fun r hr => hqA r hr.1) (fun r hr => hqA' r ⟨hr.1.1, hr.2⟩)
  subst A'
  let U := C.domain i ∩ L.domain i
  let W := C.domain j ∩ R.domain j
  let N : Set (S i × S j) := {r | r.1.val ∈ U ∧ r.2.val ∈ W}
  have hNo : IsOpen N :=
    (((C.open_domain i).inter (L.open_domain i)).preimage
      (continuous_subtype_val.comp continuous_fst)).inter
      (((C.open_domain j).inter (R.open_domain j)).preimage
        (continuous_subtype_val.comp continuous_snd))
  have hpN : p ∈ N := by
    refine ⟨⟨hiC, ?_⟩, ⟨hjC, ?_⟩⟩
    · simpa using G.family.center p.1 i
    · simpa using H.family.center p.2 j
  refine ⟨N, hNo, hpN, ?_⟩
  intro r hr s hsN
  have h := C.pair_comparison_iff hs center z hij
    r.1.val hr.1.1 s.1.val hsN.1.1 r.2.val hr.2.1 s.2.val hsN.2.1
  rw [hiA r.1.val hr.1, hiA s.1.val hsN.1, hjA r.2.val hr.2, hjA s.2.val hsN.2] at h
  refine h.trans ?_
  have he (u : S i × S j) :
      (A * G.scale u.1.val + B) + (A * H.scale u.2.val + B') =
        A * (G.scale u.1.val + H.scale u.2.val) + (B + B') := by ring
  rw [he r, he s, add_le_add_iff_right, mul_le_mul_iff_right₀ hA]

/-- Every pair of global coordinate scales with a common companion represents its full slice. -/
theorem globalCoordinateScale_pair_comparison
    (G : GlobalCoordinateScale V z seed i a b) (H : GlobalCoordinateScale V z seed j c d)
    (hl : ∀ t : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i)
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hz : ∀ p, (z p).val ∈ seed.domain p)
    (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q)
    (hqG : q = a ∨ q = b) (hqH : q = c ∨ q = d) :
    ∀ p r : S i × S j,
      V (Function.update (Function.update z i p.1) j p.2) ≤
          V (Function.update (Function.update z i r.1) j r.2) ↔
        G.scale p.1.val + H.scale p.2.val ≤ G.scale r.1.val + H.scale r.2.val := by
  exact pair_global_order_of_local_comparisons (hS i) (hS j)
    (continuousOn_iff_continuous_domRestrict.mp G.continuous)
    (continuousOn_iff_continuous_domRestrict.mp H.continuous)
    (fun x y hxy => G.increasing x.property y.property hxy)
    (fun x y hxy => H.increasing x.property y.property hxy)
    (globalCoordinateScale_local_pair_comparison G H hl hs hz hij hiq hjq hqG hqH)

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive existence on open scalar intervals

Pointwise additive charts supply coordinate scales. Two companions for each
coordinate synchronize their units, with a common companion for every pair.
The resulting pair comparisons determine the complete additive representation.
No additive representation or cardinal scale is assumed in the hypotheses.
-/

namespace Kreps.PreferenceProperties

/-- Strong separability on at least three open scalar intervals gives
continuous additive utility. -/
theorem exists_open_scalar_additive_representation
    {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (ho : ∀ i, IsOpen (S i))
    {V : (∀ i, S i) → ℝ} (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V) (z : ∀ i, S i)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  classical
  let : ∀ i, PreconnectedSpace (S i) :=
    fun i => isPreconnected_iff_preconnectedSpace.mp (hS i).isPreconnected
  have hl (t : ∀ i, S i) :
      ∃ C : ScalarAdditiveChart V, ∀ i, (t i).val ∈ C.domain i :=
    exists_scalarAdditiveChart_at_of_open hS ho hs hm hc t hthree
  obtain ⟨seed, hz⟩ := hl z
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hthree
  obtain ⟨first, second, hdistinct, hshared⟩ := exists_shared_companions hab hac hbc
  let G (i : I) : GlobalCoordinateScale V z seed i (first i) (second i) :=
    Classical.choice (exists_globalCoordinateScale hl hS hs z seed hz
      (hdistinct i).1.symm (hdistinct i).2.1.symm (hdistinct i).2.2)
  let w (i : I) (x : S i) : ℝ := (G i).scale x.val
  have hwc (i : I) : Continuous (w i) :=
    continuousOn_iff_continuous_domRestrict.mp (G i).continuous
  have hwm (i : I) : StrictMono (w i) :=
    fun x y hxy => (G i).increasing x.property y.property hxy
  refine ⟨w, hwc, hwm, represents_additive_of_reference_pair_comparisons hs hm z w hwc hwm ?_⟩
  intro i j hij a a' b b'
  obtain ⟨q, hqi, hqj, hqG, hqH⟩ := hshared i j hij
  exact globalCoordinateScale_pair_comparison (G i) (G j) hl hS hs hz hij
    hqi.symm hqj.symm hqG hqH (a, b) (a', b')

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive existence on nondegenerate real interval products

The scalar form of Kreps I, Proposition 2.14, p. 42. Continuous strong
separability and strict increase give an actual continuous additive
representation on every finite product of nondegenerate real intervals with
at least three coordinates. The intervals may include either endpoint and
need not be bounded. No local or global additive representation is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Strong separability gives continuous additive scales on full nondegenerate intervals. -/
theorem exists_nondegenerate_scalar_additive {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} [∀ i, Nontrivial (S i)] {V : (∀ i, S i) → ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hs : StronglySeparable (UtilityPref V))
    (hm : StrictMono V) (hc : Continuous V)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l) :
    ∃ g : ∀ i, S i → ℝ, (∀ i, Continuous (g i)) ∧ (∀ i, StrictMono (g i)) ∧
      Represents (AdditiveUtility g) (UtilityPref V) := by
  classical
  have hne (i : I) : (interior (S i)).Nonempty :=
    nontrivial_interval_interior_nonempty (hS i)
  let : Nontrivial I := by
    obtain ⟨i, j, _, hij, _, _⟩ := hthree
    exact ⟨⟨i, j, hij⟩⟩
  let z : ∀ i, interior (S i) := fun i => ⟨(hne i).choose, (hne i).choose_spec⟩
  obtain ⟨f, hf, hfm, hr⟩ := exists_open_scalar_additive_representation
    (fun i => (hS i).interior) (fun _ => isOpen_interior)
    (interiorScalarInclusion_stronglySeparable hs)
    (hm.comp interiorScalarInclusion_strictMono)
    (hc.comp interiorScalarInclusion_continuous) z hthree
  obtain ⟨g, hg, hgm, hgr, _⟩ :=
    exists_full_interval_additive_extension hS hne hc hm hf hfm hr
  exact ⟨g, hg, hgm, hgr⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuous additive utility from primitive preference assumptions

**Proposition 2.14**, p. 42: continuous strongly separable rational preferences
with at least three nontrivial blocks have continuous additive block utilities.
The blocks may contain indifferent alternatives and inessential blocks. A
continuous ordinal representation is first derived from preference continuity;
its block scores reduce the problem to real intervals. Singleton score factors
are removed before the nondegenerate theorem and restored with zero utilities.
-/

namespace Kreps.PreferenceProperties

/-- Three nondegenerate factors suffice even when other scalar factors are singletons. -/
theorem exists_scalar_additive_of_three_nontrivial {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i)
    (hthree : ∃ i j l : I, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      Nontrivial (S i) ∧ Nontrivial (S j) ∧ Nontrivial (S l)) :
    ∃ w : ∀ i, S i → ℝ, (∀ i, Continuous (w i)) ∧ (∀ i, StrictMono (w i)) ∧
      Represents (AdditiveUtility w) (UtilityPref V) := by
  classical
  let : ∀ i : NontrivialScalarIndices S, Nontrivial (S i.val) := fun i => i.property
  apply continuous_additive_of_activeScalar z
  exact exists_nondegenerate_scalar_additive (fun i => hS i.val)
    (activeScalarUtility_stronglySeparable hs z) (activeScalarUtility_strictMono hm z)
    (activeScalarUtility_continuous hc z) (three_nontrivialScalarIndices hthree)

variable {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- A continuous ordinal representation yields additive block utilities by scalar reduction. -/
theorem continuous_additive_of_continuous_represents (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (hthree : ThreeNontrivialBlocks r) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  have hz : Nonempty (∀ i, B i) := by
    obtain ⟨_, _, _, _, _, _, hi, _⟩ := hthree
    obtain ⟨_, _, z, _⟩ := hi
    exact ⟨z⟩
  obtain ⟨z⟩ := hz
  apply continuous_additive_of_scoreAggregator hu hs hc z
  obtain ⟨w, hwc, _, hwr⟩ := exists_scalar_additive_of_three_nontrivial
    (fun i => baselineScores_ordConnected hc z i) (scoreAggregator_stronglySeparable hu hs z)
    (scoreAggregator_strictMono hu hs z) (scoreAggregator_continuous hu hs hc z)
    (BlockScores (BaselineScores u z) z) (threeNontrivialBlocks_baselineScores hu hs z hthree)
  exact ⟨w, hwc, hwr⟩

/-- **Proposition 2.14**, existence, from rationality, continuity and strong separability. -/
theorem proposition_2_14_exists [TopologicalSpace.SeparableSpace (∀ i, B i)]
    (hr : Rational r) (hc : ContinuousPreference r) (hs : StronglySeparable r)
    (hthree : ThreeNontrivialBlocks r) :
    ∃ w : ∀ i, B i → ℝ, (∀ i, Continuous (w i)) ∧ Represents (AdditiveUtility w) r := by
  obtain ⟨u, hu, huc, _⟩ := continuous_represents_of_continuous_connected hr hc
  exact continuous_additive_of_continuous_represents hu hs huc hthree

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The additive existence entry in Table 2.1

Kreps I, Problem 2.1 and Table 2.1, p. 45. With continuity and three nontrivial
blocks, strong separability has the indicated `some` additive representation.
The forward implication uses the fully constructed Proposition 2.14 theorem;
the backward implication uses cancellation of unchanged additive contributions.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
  [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
  [TopologicalSpace.SeparableSpace (∀ i, B i)]
  {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- Table 2.1, strong separability: `some` additive representation under the book's hypotheses. -/
theorem table_additive (hr : Rational r) (hc : ContinuousPreference r)
    (hthree : ThreeNontrivialBlocks r) :
    StronglySeparable r ↔ SomeRepresentation r AdditiveForm := by
  constructor
  · intro hs
    obtain ⟨w, _, hw⟩ := proposition_2_14_exists hr hc hs hthree
    exact ⟨AdditiveUtility w, hw, w, rfl⟩
  · exact table_additive_converse

/-- Continuity and strong separability admit a continuous additive representation. -/
theorem table_continuous_additive (hr : Rational r) (hthree : ThreeNontrivialBlocks r) :
    (ContinuousPreference r ∧ StronglySeparable r) ↔
      SomeRepresentation r (fun u => Continuous u ∧ AdditiveForm u) := by
  constructor
  · rintro ⟨hc, hs⟩
    obtain ⟨w, hwc, hwr⟩ := proposition_2_14_exists hr hc hs hthree
    exact ⟨AdditiveUtility w, hwr, additiveUtility_continuous hwc, w, rfl⟩
  · rintro ⟨u, hu, huc, w, rfl⟩
    exact ⟨proposition_2_9_forward hu huc, proposition_2_14_additive hu⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Additive utility on the original partitioned commodity orthant

**Proposition 2.14**, p. 42, on the book's original nonnegative commodity
orthant. A total assignment `owner` specifies the full partition: each good
belongs to exactly one block. Grouping quantities is a homeomorphism, so the
primitive preference assumptions give continuous functions of the original
block quantities whose sum represents preference. Empty or inessential blocks
are allowed; only three blocks are required to be nontrivial.
-/

namespace Kreps.PreferenceProperties

variable {k n : ℕ}

/-- Original preference expressed in the quantities of a full commodity partition. -/
def PartitionPreference (owner : Fin k → Fin n)
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop)
    (x y : ∀ i, PartitionBlock owner i) : Prop :=
  r (PartitionUngroup owner x) (PartitionUngroup owner y)

/-- Sum the block utilities at the original commodity bundle. -/
def PartitionAdditiveUtility (owner : Fin k → Fin n)
    (w : ∀ i, PartitionBlock owner i → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  AdditiveUtility w (PartitionGroup owner x)

/-- Rationality is unchanged when the original quantities are grouped into blocks. -/
theorem partitionPreference_rational (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    Rational (PartitionPreference owner r) :=
  ⟨fun x y => hr.1 (PartitionUngroup owner x) (PartitionUngroup owner y),
    fun x y z => hr.2 (PartitionUngroup owner x) (PartitionUngroup owner y)
      (PartitionUngroup owner z)⟩

/-- Continuity of preference survives the homeomorphic regrouping of commodity quantities. -/
theorem partitionPreference_continuous (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hc : ContinuousPreference r) :
    ContinuousPreference (PartitionPreference owner r) :=
  hc.preimage (((partitionUngroup_continuous owner).comp continuous_fst).prodMk
    ((partitionUngroup_continuous owner).comp continuous_snd))

/-- Continuous block utility functions give a continuous utility of the original commodities. -/
theorem partitionAdditiveUtility_continuous (owner : Fin k → Fin n)
    {w : ∀ i, PartitionBlock owner i → ℝ} (hw : ∀ i, Continuous (w i)) :
    Continuous (PartitionAdditiveUtility owner w) :=
  (additiveUtility_continuous hw).comp (partitionGroup_continuous owner)

/-- **Proposition 2.14**, existence on the original nonnegative commodity orthant. -/
theorem proposition_2_14_orthant (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r)
    (hs : StronglySeparable (PartitionPreference owner r))
    (hthree : ThreeNontrivialBlocks (PartitionPreference owner r)) :
    ∃ w : ∀ i, PartitionBlock owner i → ℝ, (∀ i, Continuous (w i)) ∧
      Represents (PartitionAdditiveUtility owner w) r := by
  obtain ⟨w, hwc, hwr⟩ := proposition_2_14_exists (partitionPreference_rational owner hr)
    (partitionPreference_continuous owner hc) hs hthree
  refine ⟨w, hwc, fun x y => ?_⟩
  simpa only [PartitionPreference, partitionUngroup_group, PartitionAdditiveUtility] using
    hwr (PartitionGroup owner x) (PartitionGroup owner y)

/-- **Proposition 2.14**, converse on the original orthant, without continuity assumptions. -/
theorem proposition_2_14_orthant_additive (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    {w : ∀ i, PartitionBlock owner i → ℝ}
    (hw : Represents (PartitionAdditiveUtility owner w) r) :
    StronglySeparable (PartitionPreference owner r) := by
  apply proposition_2_14_additive (w := w)
  intro x y
  simpa only [PartitionPreference, PartitionAdditiveUtility, partitionGroup_ungroup] using
    hw (PartitionUngroup owner x) (PartitionUngroup owner y)

/-- The full additive characterization for a partition of the original commodity orthant. -/
theorem proposition_2_14_orthant_iff (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r)
    (hthree : ThreeNontrivialBlocks (PartitionPreference owner r)) :
    StronglySeparable (PartitionPreference owner r) ↔
      ∃ w : ∀ i, PartitionBlock owner i → ℝ, (∀ i, Continuous (w i)) ∧
        Represents (PartitionAdditiveUtility owner w) r := by
  constructor
  · intro hs
    exact proposition_2_14_orthant owner hr hc hs hthree
  · rintro ⟨_, _, hw⟩
    exact proposition_2_14_orthant_additive owner hw

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Food rankings independent of clothing

Kreps I, Section 2.5, p. 39. Food coordinates are steaks, corn, potatoes and
lettuce, in that order. The printed alternatives are `(2,2,3,0)` and `(1,5,0,3)`.
Weak separability makes their comparison independent of clothing. The book's
ranking is conditional: no particular ranking is imposed on every consumer.

We encode the skirt and jeans contexts by `(1,0)` and `(0,1)` in a nonnegative
two-good clothing block. Those numeric clothing encodings are ours; the book
names the contexts without assigning coordinates. Food is the single selected
block and clothing is the leftover block in `WeaklySeparable`.

The final utility is a constructed witness, not a utility specified by Kreps.
It gives all six goods positive weights and satisfies the illustrated ranking.
-/

namespace Kreps.PreferenceProperties

/-- Four food quantities in one selected block, together with two clothing quantities. -/
abbrev FoodClothingBundle :=
  BlockBundle (fun _ : Fin 1 => NonnegativeOrthant 4) (NonnegativeOrthant 2)

/-- Combine a food bundle with its clothing context. -/
def FoodWithClothing (food : NonnegativeOrthant 4) (clothing : NonnegativeOrthant 2) :
    FoodClothingBundle := (fun _ => food, clothing)

/-- The first printed food bundle: two steaks, two corn, three potatoes and no lettuce. -/
def FirstFoodBundle : NonnegativeOrthant 4 :=
  ⟨![2, 2, 3, 0], by intro j; fin_cases j <;> norm_num⟩

/-- The second printed bundle: one steak, five corn, no potatoes and three kilograms of lettuce. -/
def SecondFoodBundle : NonnegativeOrthant 4 :=
  ⟨![1, 5, 0, 3], by intro j; fin_cases j <;> norm_num⟩

/-- Our nonnegative two-good encoding of wearing a skirt. -/
def SkirtContext : NonnegativeOrthant 2 :=
  ⟨![1, 0], by intro j; fin_cases j <;> norm_num⟩

/-- Our nonnegative two-good encoding of wearing jeans. -/
def JeansContext : NonnegativeOrthant 2 :=
  ⟨![0, 1], by intro j; fin_cases j <;> norm_num⟩

/-- Replacing the selected block replaces precisely the food and keeps the clothing. -/
theorem replaceFoodBlock (s : FoodClothingBundle) (food : NonnegativeOrthant 4) :
    ReplaceBlock s 0 food = FoodWithClothing food s.2 := by
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [ReplaceBlock, FoodWithClothing]
  · rfl

/-- Weak separability preserves any food comparison between arbitrary clothing contexts. -/
theorem foodClothing_comparison_iff {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) (a b : NonnegativeOrthant 4) (c d : NonnegativeOrthant 2) :
    r (FoodWithClothing a c) (FoodWithClothing b c) ↔
      r (FoodWithClothing a d) (FoodWithClothing b d) := by
  simpa only [replaceFoodBlock, FoodWithClothing] using
    hs 0 a b (FoodWithClothing a c) (FoodWithClothing a d)

/-- Strict food comparisons are also independent of the surrounding clothing quantities. -/
theorem foodClothing_strict_iff {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) (a b : NonnegativeOrthant 4) (c d : NonnegativeOrthant 2) :
    Strict r (FoodWithClothing a c) (FoodWithClothing b c) ↔
      Strict r (FoodWithClothing a d) (FoodWithClothing b d) := by
  simpa only [replaceFoodBlock, FoodWithClothing] using
    weaklySeparable_strict hs 0 a b (FoodWithClothing a c) (FoodWithClothing a d)

/-- The p. 39 food bundles have the same weak comparison in the skirt and jeans contexts. -/
theorem foodClothing_printed_comparison {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) :
    r (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) ↔
    r (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  foodClothing_comparison_iff hs FirstFoodBundle SecondFoodBundle SkirtContext JeansContext

/-- If the first printed bundle is strictly preferred in a skirt, it is preferred in jeans. -/
theorem foodClothing_printed_strict {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r)
    (hfood : Strict r (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext)) :
    Strict r (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  (foodClothing_strict_iff hs FirstFoodBundle SecondFoodBundle SkirtContext JeansContext).mp hfood

/-- A constructed additive witness: steaks have weight four and every other good weight one. -/
def FoodClothingWitnessUtility (x : FoodClothingBundle) : ℝ :=
  4 * (x.1 0).val 0 + (x.1 0).val 1 + (x.1 0).val 2 + (x.1 0).val 3 +
    x.2.val 0 + x.2.val 1

/-- The constructed utility satisfies food separability on the full nonnegative domain. -/
theorem foodClothingWitness_separable :
    WeaklySeparable (UtilityPref FoodClothingWitnessUtility) := by
  intro i a b s t
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [replaceFoodBlock, UtilityPref, FoodClothingWitnessUtility, FoodWithClothing]
  constructor <;> intro h <;> linarith

/-- The constructed witness ranks the first food bundle strictly above the second in a skirt. -/
theorem foodClothingWitness_initial_ranking :
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) := by
  norm_num [Strict, UtilityPref, FoodClothingWitnessUtility, FoodWithClothing,
    FirstFoodBundle, SecondFoodBundle, SkirtContext]

/-- A rational, separable preference realizes the book's conditional ranking in both contexts. -/
theorem foodClothingWitness_properties :
    Rational (UtilityPref FoodClothingWitnessUtility) ∧
    WeaklySeparable (UtilityPref FoodClothingWitnessUtility) ∧
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) ∧
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  ⟨proposition_1_3a _, foodClothingWitness_separable, foodClothingWitness_initial_ranking,
    foodClothing_printed_strict foodClothingWitness_separable foodClothingWitness_initial_ranking⟩

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The beer, wine and bread projection

Kreps I, p. 40. The full bundle consists of four beers, three wines and five loaves
of bread. Selecting commodities `{1,3}` gives the beer-and-bread sub-bundle `(4,5)`;
the complementary wine quantity is three. The book uses one-based commodity names.
Here `Fin 3` uses zero-based coordinates, so the selected set is `{0,2}` and wine
has coordinate one. The example uses the chapter's actual `orthantGrouping`
equivalence, including its leftover block and reconstruction of the original bundle.
-/

namespace Kreps.PreferenceProperties

/-- The full printed bundle `(4,3,5)`, in beer, wine and bread order. -/
def BeerWineBreadBundle : NonnegativeOrthant 3 :=
  ⟨![4, 3, 5], by intro j; fin_cases j <;> norm_num⟩

/-- Assign beer and bread to block zero, leaving wine outside the selected block. -/
def BeerBreadOwner (j : Fin 3) : Option (Fin 1) := if j = 1 then none else some 0

/-- The selected coordinates are exactly `{0,2}`, the printed commodity names `{1,3}`. -/
theorem beerBreadOwner_selected :
    {j | BeerBreadOwner j = some 0} = ({0, 2} : Set (Fin 3)) := by
  ext j
  fin_cases j <;> norm_num [BeerBreadOwner]

/-- The complementary commodity is exactly wine, with zero-based coordinate one. -/
theorem beerBreadOwner_leftover :
    {j | BeerBreadOwner j = none} = ({1} : Set (Fin 3)) := by
  ext j
  fin_cases j <;> norm_num [BeerBreadOwner]

/-- Reading beer and bread from the actual selected block gives the printed pair `(4,5)`. -/
theorem beerWineBread_projection :
    (((orthantGrouping BeerBreadOwner BeerWineBreadBundle).1 0
        ⟨0, by norm_num [BeerBreadOwner]⟩ : ℝ),
      ((orthantGrouping BeerBreadOwner BeerWineBreadBundle).1 0
        ⟨2, by norm_num [BeerBreadOwner]⟩ : ℝ)) = (4, 5) := by
  rfl

/-- Reading the actual leftover block gives the original wine quantity, three. -/
theorem beerWineBread_leftover :
    ((orthantGrouping BeerBreadOwner BeerWineBreadBundle).2
      ⟨1, by norm_num [BeerBreadOwner]⟩ : ℝ) = 3 := by
  rfl

/-- The selected sub-bundle and its complement reconstruct the complete printed bundle. -/
theorem beerWineBread_reconstruction :
    (orthantGrouping BeerBreadOwner).symm
      (orthantGrouping BeerBreadOwner BeerWineBreadBundle) = BeerWineBreadBundle :=
  (orthantGrouping BeerBreadOwner).symm_apply_apply BeerWineBreadBundle

end Kreps.PreferenceProperties

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The ten-dollar trade at two wealth levels

Kreps I, Section 2.6, p. 43. A consumer accepts exchanging goods `x` and ten
dollars for goods `x'` at zero money left over exactly when the same exchange
is acceptable at one hundred thousand dollars left over. Both comparisons are
conditional on preference: quasi-linearity does not assert that the trade is
accepted. All money amounts belong to the nonnegative domain.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}

/-- The exact p. 43 comparison follows from common-addition invariance alone. -/
theorem moneyTranslation_wealth_example (ht : MoneyTranslation r) (x x' : X) :
    r (x', 0) (x, 10) ↔ r (x', 100000) (x, 100010) := by
  convert ht x' x 0 10 100000 using 1
  norm_num

/-- Quasi-linear preferences preserve the book's ten-dollar trade at both wealth levels. -/
theorem quasiLinear_wealth_example (hq : QuasiLinear r) (x x' : X) :
    r (x', 0) (x, 10) ↔ r (x', 100000) (x, 100010) := by
  obtain ⟨u, hu⟩ := hq
  exact moneyTranslation_wealth_example (quasiLinear_moneyTranslation hu) x x'

end Kreps.PreferenceProperties

set_option linter.style.longLine false
#print axioms Kreps.PreferenceProperties.FullMenus
#print axioms Kreps.PreferenceProperties.ChoiceRule
#print axioms Kreps.PreferenceProperties.FeasibleOn
#print axioms Kreps.PreferenceProperties.Feasible
#print axioms Kreps.PreferenceProperties.FiniteNonempty
#print axioms Kreps.PreferenceProperties.CoherentOn
#print axioms Kreps.PreferenceProperties.Coherent
#print axioms Kreps.PreferenceProperties.Complete
#print axioms Kreps.PreferenceProperties.TransitivePref
#print axioms Kreps.PreferenceProperties.Rational
#print axioms Kreps.PreferenceProperties.PrefChoice
#print axioms Kreps.PreferenceProperties.UtilityPref
#print axioms Kreps.PreferenceProperties.UtilityChoice
#print axioms Kreps.PreferenceProperties.Represents
#print axioms Kreps.PreferenceProperties.Revealed
#print axioms Kreps.PreferenceProperties.Strict
#print axioms Kreps.PreferenceProperties.Indifferent
#print axioms Kreps.PreferenceProperties.NoBetterThan
#print axioms Kreps.PreferenceProperties.complete_refl
#print axioms Kreps.PreferenceProperties.prefChoice_feasible
#print axioms Kreps.PreferenceProperties.feasible_empty
#print axioms Kreps.PreferenceProperties.represents_choice
#print axioms Kreps.PreferenceProperties.coherent_iff_on_full
#print axioms Kreps.PreferenceProperties.upperSemicontinuous_of_tendstoUniformly
#print axioms Kreps.PreferenceProperties.upperSemicontinuous_tsum_of_norm_le
#print axioms Kreps.PreferenceProperties.LowerDistribution
#print axioms Kreps.PreferenceProperties.lowerDistribution_monotone
#print axioms Kreps.PreferenceProperties.lowerDistribution_tendsto_above
#print axioms Kreps.PreferenceProperties.lowerDistribution_upperSemicontinuous
#print axioms Kreps.PreferenceProperties.lowerDistribution_tendsto_below
#print axioms Kreps.PreferenceProperties.lowerDistribution_lowerSemicontinuousAt
#print axioms Kreps.PreferenceProperties.lowerDistribution_continuousAt
#print axioms Kreps.PreferenceProperties.CommodityEuclidean
#print axioms Kreps.PreferenceProperties.definition_A2_1
#print axioms Kreps.PreferenceProperties.euclidean_distance_properties
#print axioms Kreps.PreferenceProperties.euclidean_distance_translation
#print axioms Kreps.PreferenceProperties.euclideanProductHomeomorph
#print axioms Kreps.PreferenceProperties.definition_A2_2
#print axioms Kreps.PreferenceProperties.appendix2_open_ball
#print axioms Kreps.PreferenceProperties.definition_A2_3_open
#print axioms Kreps.PreferenceProperties.definition_A2_3_closed
#print axioms Kreps.PreferenceProperties.appendix2_empty_univ_clopen
#print axioms Kreps.PreferenceProperties.proposition_A2_4_open_union
#print axioms Kreps.PreferenceProperties.proposition_A2_4_open_inter
#print axioms Kreps.PreferenceProperties.proposition_A2_4_closed_union
#print axioms Kreps.PreferenceProperties.proposition_A2_4_closed_inter
#print axioms Kreps.PreferenceProperties.appendix2_relative_open
#print axioms Kreps.PreferenceProperties.appendix2_relative_closed
#print axioms Kreps.PreferenceProperties.definition_A2_5_closure
#print axioms Kreps.PreferenceProperties.definition_A2_5_interior
#print axioms Kreps.PreferenceProperties.appendix2_closure_intersection
#print axioms Kreps.PreferenceProperties.appendix2_interior_union
#print axioms Kreps.PreferenceProperties.appendix2_interior_ball
#print axioms Kreps.PreferenceProperties.appendix2_closure_interior_complement
#print axioms Kreps.PreferenceProperties.appendix2_relative_interior_self
#print axioms Kreps.PreferenceProperties.continuous_lower_level_bound
#print axioms Kreps.PreferenceProperties.finite_coordinate_lower_bound
#print axioms Kreps.PreferenceProperties.finiteProductMonotone_isOpen_lt
#print axioms Kreps.PreferenceProperties.finiteProductMonotone_continuous
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.mk
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.mean
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.reflexive
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.symmetric
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.bisymmetric
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.strictMono_left
#print axioms Kreps.PreferenceProperties.OrderedBisymmetricMean.strictMono_right
#print axioms Kreps.PreferenceProperties.MeanDyadicGrid
#print axioms Kreps.PreferenceProperties.orderedMean_between
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_even
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_odd
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_left
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_right
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_near
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_midpoint
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_lt_succ
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_strictMonoOn
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_refine
#print axioms Kreps.PreferenceProperties.MeanDyadicPoints
#print axioms Kreps.PreferenceProperties.meanDyadicPoints_mean
#print axioms Kreps.PreferenceProperties.definition_A3_1
#print axioms Kreps.PreferenceProperties.proposition_A3_2
#print axioms Kreps.PreferenceProperties.proposition_A3_3
#print axioms Kreps.PreferenceProperties.definition_A3_4_convexHull
#print axioms Kreps.PreferenceProperties.proposition_A3_4
#print axioms Kreps.PreferenceProperties.proposition_A3_5
#print axioms Kreps.PreferenceProperties.definition_A3_4_closedConvexHull
#print axioms Kreps.PreferenceProperties.proposition_A3_7_closure
#print axioms Kreps.PreferenceProperties.proposition_A3_7_closedHull
#print axioms Kreps.PreferenceProperties.intervalValues_update
#print axioms Kreps.PreferenceProperties.sum_interval_update
#print axioms Kreps.PreferenceProperties.finite_sum_opposite_coordinates
#print axioms Kreps.PreferenceProperties.PairSumInvariant
#print axioms Kreps.PreferenceProperties.pairSumInvariant_eq_of_sum_eq_on
#print axioms Kreps.PreferenceProperties.pairSumInvariant_eq_of_sum_eq
#print axioms Kreps.PreferenceProperties.LocallyPositiveAffineOn
#print axioms Kreps.PreferenceProperties.affine_coefficients_unique
#print axioms Kreps.PreferenceProperties.locallyPositiveAffineOn_global
#print axioms Kreps.PreferenceProperties.locallyPositiveAffineOn_of_affine
#print axioms Kreps.PreferenceProperties.locallyPositiveAffineOn_mono
#print axioms Kreps.PreferenceProperties.strictMonoOn_union_intervals
#print axioms Kreps.PreferenceProperties.interval_order_of_local_comparisons
#print axioms Kreps.PreferenceProperties.interval_strict_order_of_local_comparisons
#print axioms Kreps.PreferenceProperties.path_order_of_local_comparisons
#print axioms Kreps.PreferenceProperties.global_order_of_local_comparisons
#print axioms Kreps.PreferenceProperties.additive_scale_bddBelow_at_least
#print axioms Kreps.PreferenceProperties.additive_scale_bddAbove_at_greatest
#print axioms Kreps.PreferenceProperties.tendsto_dense_comap_atBot
#print axioms Kreps.PreferenceProperties.tendsto_dense_comap_atTop
#print axioms Kreps.PreferenceProperties.exists_continuous_endpoint_extension
#print axioms Kreps.PreferenceProperties.continuous_extension_le_dense
#print axioms Kreps.PreferenceProperties.dense_le_continuous_extension
#print axioms Kreps.PreferenceProperties.continuous_extension_strictMono
#print axioms Kreps.PreferenceProperties.exists_continuous_strictMono_endpoint_extension
#print axioms Kreps.PreferenceProperties.dense_comparison_strict_implies_le
#print axioms Kreps.PreferenceProperties.exists_product_improvement_below
#print axioms Kreps.PreferenceProperties.dense_product_strict_comparison
#print axioms Kreps.PreferenceProperties.dense_product_comparison
#print axioms Kreps.PreferenceProperties.exists_shared_companions
#print axioms Kreps.PreferenceProperties.proposition_1_3a
#print axioms Kreps.PreferenceProperties.prefChoice_finiteNonempty
#print axioms Kreps.PreferenceProperties.prefChoice_coherent
#print axioms Kreps.PreferenceProperties.proposition_1_3b
#print axioms Kreps.PreferenceProperties.proposition_1_4
#print axioms Kreps.PreferenceProperties.coherent_exchange
#print axioms Kreps.PreferenceProperties.revealed_of_chosen
#print axioms Kreps.PreferenceProperties.chosen_of_revealed
#print axioms Kreps.PreferenceProperties.revealed_complete
#print axioms Kreps.PreferenceProperties.revealed_transitive
#print axioms Kreps.PreferenceProperties.choice_eq_revealed_of_nonempty
#print axioms Kreps.PreferenceProperties.proposition_1_5
#print axioms Kreps.PreferenceProperties.AsymmetricPref
#print axioms Kreps.PreferenceProperties.NegativelyTransitive
#print axioms Kreps.PreferenceProperties.WeakFromStrict
#print axioms Kreps.PreferenceProperties.IndifferenceFromStrict
#print axioms Kreps.PreferenceProperties.proposition_1_9a
#print axioms Kreps.PreferenceProperties.proposition_1_9b
#print axioms Kreps.PreferenceProperties.strict_weak_trans
#print axioms Kreps.PreferenceProperties.weak_strict_trans
#print axioms Kreps.PreferenceProperties.proposition_1_9c
#print axioms Kreps.PreferenceProperties.proposition_1_9d
#print axioms Kreps.PreferenceProperties.proposition_1_9e
#print axioms Kreps.PreferenceProperties.proposition_1_9f
#print axioms Kreps.PreferenceProperties.proposition_1_9g
#print axioms Kreps.PreferenceProperties.proposition_1_9h
#print axioms Kreps.PreferenceProperties.proposition_1_10
#print axioms Kreps.PreferenceProperties.problem_1_9
#print axioms Kreps.PreferenceProperties.definition_A2_24_upper
#print axioms Kreps.PreferenceProperties.definition_A2_24_lower
#print axioms Kreps.PreferenceProperties.proposition_A2_26
#print axioms Kreps.PreferenceProperties.upperSemicontinuous_compact_choice
#print axioms Kreps.PreferenceProperties.ClosedIndicatorSeries
#print axioms Kreps.PreferenceProperties.appendix2_diagnostic_nonnegative
#print axioms Kreps.PreferenceProperties.DiagnosticNegativeWeights
#print axioms Kreps.PreferenceProperties.DiagnosticClosedSets
#print axioms Kreps.PreferenceProperties.diagnosticNegativeWeights_summable
#print axioms Kreps.PreferenceProperties.diagnosticNegative_formula
#print axioms Kreps.PreferenceProperties.diagnosticNegative_not_upperSemicontinuousAt
#print axioms Kreps.PreferenceProperties.appendix2_diagnostic_counterexample
#print axioms Kreps.PreferenceProperties.definition_A2_6
#print axioms Kreps.PreferenceProperties.proposition_A2_7
#print axioms Kreps.PreferenceProperties.proposition_A2_8
#print axioms Kreps.PreferenceProperties.definition_A2_9
#print axioms Kreps.PreferenceProperties.appendix2_accumulation_strict_index
#print axioms Kreps.PreferenceProperties.appendix2_accumulation_subsequence
#print axioms Kreps.PreferenceProperties.appendix2_closure_sequence
#print axioms Kreps.PreferenceProperties.appendix2_set_accumulation_self
#print axioms Kreps.PreferenceProperties.definition_A2_11
#print axioms Kreps.PreferenceProperties.proposition_A2_12
#print axioms Kreps.PreferenceProperties.appendix2_cauchy_criterion
#print axioms Kreps.PreferenceProperties.appendix2_euclidean_complete
#print axioms Kreps.PreferenceProperties.definition_A2_13
#print axioms Kreps.PreferenceProperties.corollary_A2_14
#print axioms Kreps.PreferenceProperties.appendix2_finite_compact
#print axioms Kreps.PreferenceProperties.appendix2_compact_open_cover
#print axioms Kreps.PreferenceProperties.meanDyadicPoints_closure_mean
#print axioms Kreps.PreferenceProperties.meanDyadicPoints_dense
#print axioms Kreps.PreferenceProperties.utilityDiagonal_strictMono
#print axioms Kreps.PreferenceProperties.utilityDiagonal_attains_pair
#print axioms Kreps.PreferenceProperties.DiagonalUtilityMean
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_spec
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_reflexive
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_symmetric
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_strictMono_left
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_strictMono_right
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_comparison
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_continuous
#print axioms Kreps.PreferenceProperties.PartialUtilityMedial
#print axioms Kreps.PreferenceProperties.diagonalUtilityMean_bisymmetric
#print axioms Kreps.PreferenceProperties.OrderedUtilityMean
#print axioms Kreps.PreferenceProperties.FiniteMixtureSet
#print axioms Kreps.PreferenceProperties.finiteMixtureSet_subset_convexHull
#print axioms Kreps.PreferenceProperties.mem_finiteMixtureSet_of_mem_finset_hull
#print axioms Kreps.PreferenceProperties.convexHull_eq_finite_mixture_union
#print axioms Kreps.PreferenceProperties.finiteMixtureSet_isCompact
#print axioms Kreps.PreferenceProperties.proposition_A3_6
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.mk
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.domain
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.coord
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.isOpen
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.interval
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.subset
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.cover
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.continuous
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.increasing
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.transition
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible
#print axioms Kreps.PreferenceProperties.AffineIntervalSection
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.mk
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.domain
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.isOpen
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.interval
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.subset
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.value
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.continuous
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.increasing
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.compatible
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.seed_subset
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.seed_eq
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.compatible_chart
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.seedSection
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible.affine
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible.local_relation
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.unique
#print axioms Kreps.PreferenceProperties.interval_interior_dense
#print axioms Kreps.PreferenceProperties.interval_outside_interior_extreme
#print axioms Kreps.PreferenceProperties.interval_exists_continuous_strictMono_extension
#print axioms Kreps.PreferenceProperties.exists_affine_score_path
#print axioms Kreps.PreferenceProperties.pair_global_order_of_local_comparisons
#print axioms Kreps.PreferenceProperties.mem_noBetterThan_self
#print axioms Kreps.PreferenceProperties.pref_iff_noBetterThan_subset
#print axioms Kreps.PreferenceProperties.strict_iff_noBetterThan_ssubset
#print axioms Kreps.PreferenceProperties.proposition_1_7
#print axioms Kreps.PreferenceProperties.FiniteUtility
#print axioms Kreps.PreferenceProperties.proposition_1_8
#print axioms Kreps.PreferenceProperties.proposition_1_2b
#print axioms Kreps.PreferenceProperties.finite_choice_eq_revealed
#print axioms Kreps.PreferenceProperties.proposition_1_2a
#print axioms Kreps.PreferenceProperties.proposition_1_2c
#print axioms Kreps.PreferenceProperties.problem_1_8
#print axioms Kreps.PreferenceProperties.OrderSeparating
#print axioms Kreps.PreferenceProperties.exists_positive_summable
#print axioms Kreps.PreferenceProperties.WeightedUtility
#print axioms Kreps.PreferenceProperties.weightedTerm_le
#print axioms Kreps.PreferenceProperties.weightedUtility_mono
#print axioms Kreps.PreferenceProperties.weightedUtility_strict
#print axioms Kreps.PreferenceProperties.weightedUtility_represents
#print axioms Kreps.PreferenceProperties.represents_of_countable_separating
#print axioms Kreps.PreferenceProperties.proposition_1_11
#print axioms Kreps.PreferenceProperties.strict_iff_utility_lt
#print axioms Kreps.PreferenceProperties.countable_separating_of_represents
#print axioms Kreps.PreferenceProperties.proposition_1_12
#print axioms Kreps.PreferenceProperties.Assumption116
#print axioms Kreps.PreferenceProperties.proposition_1_17
#print axioms Kreps.PreferenceProperties.proposition_1_18
#print axioms Kreps.PreferenceProperties.EmptyMenus
#print axioms Kreps.PreferenceProperties.emptyMenus_feasible
#print axioms Kreps.PreferenceProperties.emptyMenus_finiteNonempty
#print axioms Kreps.PreferenceProperties.emptyMenus_coherent
#print axioms Kreps.PreferenceProperties.empty_infinite_menus_preserves_choice
#print axioms Kreps.PreferenceProperties.QuasiLinearUtility
#print axioms Kreps.PreferenceProperties.QuasiLinear
#print axioms Kreps.PreferenceProperties.OwnMoneyOrder
#print axioms Kreps.PreferenceProperties.MoneyTranslation
#print axioms Kreps.PreferenceProperties.MoneyCompensable
#print axioms Kreps.PreferenceProperties.indifferent_compare_iff
#print axioms Kreps.PreferenceProperties.moneyTranslation_indifferent
#print axioms Kreps.PreferenceProperties.quasiLinear_ownMoneyOrder
#print axioms Kreps.PreferenceProperties.quasiLinear_moneyTranslation
#print axioms Kreps.PreferenceProperties.quasiLinear_moneyCompensable
#print axioms Kreps.PreferenceProperties.quasiLinear_of_money_properties
#print axioms Kreps.PreferenceProperties.proposition_2_16
#print axioms Kreps.PreferenceProperties.problem_2_11
#print axioms Kreps.PreferenceProperties.QuasiLinearDifference
#print axioms Kreps.PreferenceProperties.quasiLinear_compensation
#print axioms Kreps.PreferenceProperties.quasiLinear_compensation_of_preferred
#print axioms Kreps.PreferenceProperties.printed_compensation_bundle_counterexample
#print axioms Kreps.PreferenceProperties.definition_A2_15
#print axioms Kreps.PreferenceProperties.appendix2_uniform_continuity
#print axioms Kreps.PreferenceProperties.appendix2_lipschitz_uniform
#print axioms Kreps.PreferenceProperties.proposition_A2_15a
#print axioms Kreps.PreferenceProperties.proposition_A2_15b_open
#print axioms Kreps.PreferenceProperties.proposition_A2_15b_closed
#print axioms Kreps.PreferenceProperties.proposition_A2_16a
#print axioms Kreps.PreferenceProperties.proposition_A2_16b
#print axioms Kreps.PreferenceProperties.proposition_A2_16c
#print axioms Kreps.PreferenceProperties.proposition_A2_16d
#print axioms Kreps.PreferenceProperties.definition_A2_17
#print axioms Kreps.PreferenceProperties.proposition_A2_18
#print axioms Kreps.PreferenceProperties.StrictlyPositiveOrthant
#print axioms Kreps.PreferenceProperties.appendix2_nonnegative_coordinates
#print axioms Kreps.PreferenceProperties.appendix2_nonnegative_orthant_closed
#print axioms Kreps.PreferenceProperties.appendix2_positive_orthant_open
#print axioms Kreps.PreferenceProperties.euclidean_norm_le_sum_abs
#print axioms Kreps.PreferenceProperties.appendix2_norm_comparison
#print axioms Kreps.PreferenceProperties.sumEuclideanHomeomorph
#print axioms Kreps.PreferenceProperties.sumEuclideanHomeomorph_apply
#print axioms Kreps.PreferenceProperties.appendix2_bounded_coordinates
#print axioms Kreps.PreferenceProperties.AppendixDistancePointA
#print axioms Kreps.PreferenceProperties.AppendixDistancePointB
#print axioms Kreps.PreferenceProperties.appendix2_example_euclidean_distance
#print axioms Kreps.PreferenceProperties.appendix2_example_supremum_distance
#print axioms Kreps.PreferenceProperties.appendix2_example_sum_distance
#print axioms Kreps.PreferenceProperties.MeanDyadicRank
#print axioms Kreps.PreferenceProperties.meanDyadicRank_mem
#print axioms Kreps.PreferenceProperties.meanDyadicGrid_le_iff_rank
#print axioms Kreps.PreferenceProperties.MeanRankCut
#print axioms Kreps.PreferenceProperties.meanRankCut_nonempty
#print axioms Kreps.PreferenceProperties.meanRankCut_bddAbove
#print axioms Kreps.PreferenceProperties.MeanCardinalScale
#print axioms Kreps.PreferenceProperties.meanCardinalScale_mem
#print axioms Kreps.PreferenceProperties.meanCardinalScale_mono
#print axioms Kreps.PreferenceProperties.meanCardinalScale_grid
#print axioms Kreps.PreferenceProperties.meanCardinalScale_strictMono
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible.congr
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible.union
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.Compatible.positive_affine
#print axioms Kreps.PreferenceProperties.AffineIntervalSection.extend
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.sections_cover
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.exists_global_section
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.globalize
#print axioms Kreps.PreferenceProperties.sum_coordinate_scores_update
#print axioms Kreps.PreferenceProperties.interior_product_inclusion_update
#print axioms Kreps.PreferenceProperties.interior_additive_pair_comparison
#print axioms Kreps.PreferenceProperties.interior_additive_scale_bounds
#print axioms Kreps.PreferenceProperties.proposition_1_20
#print axioms Kreps.PreferenceProperties.same_utility_fibers
#print axioms Kreps.PreferenceProperties.UtilityTransform
#print axioms Kreps.PreferenceProperties.utilityTransform_apply
#print axioms Kreps.PreferenceProperties.utilityTransform_strictMonoOn
#print axioms Kreps.PreferenceProperties.represents_of_transform_on_range
#print axioms Kreps.PreferenceProperties.proposition_1_21
#print axioms Kreps.PreferenceProperties.ExtendedUtilityTransform
#print axioms Kreps.PreferenceProperties.extendedUtilityTransform_monotone
#print axioms Kreps.PreferenceProperties.extendedUtilityTransform_apply
#print axioms Kreps.PreferenceProperties.extendedUtilityTransform_strictMonoOn
#print axioms Kreps.PreferenceProperties.proposition_1_21_extension
#print axioms Kreps.PreferenceProperties.problem_1_14a
#print axioms Kreps.PreferenceProperties.problem_1_14b
#print axioms Kreps.PreferenceProperties.problem_1_14d
#print axioms Kreps.PreferenceProperties.NoWorseThan
#print axioms Kreps.PreferenceProperties.StrictlyBetterThan
#print axioms Kreps.PreferenceProperties.StrictlyWorseThan
#print axioms Kreps.PreferenceProperties.ContinuousPreference
#print axioms Kreps.PreferenceProperties.MetricContinuousPreference
#print axioms Kreps.PreferenceProperties.continuousPreference_iff_metric
#print axioms Kreps.PreferenceProperties.continuousPreference_of_continuous_utility
#print axioms Kreps.PreferenceProperties.ClosedContours
#print axioms Kreps.PreferenceProperties.OpenStrictContours
#print axioms Kreps.PreferenceProperties.continuousPreference_openStrictContours
#print axioms Kreps.PreferenceProperties.closedContours_iff_openStrictContours
#print axioms Kreps.PreferenceProperties.openStrictContours_continuousPreference
#print axioms Kreps.PreferenceProperties.proposition_1_14c
#print axioms Kreps.PreferenceProperties.proposition_1_14d
#print axioms Kreps.PreferenceProperties.SequenceWeakContinuity
#print axioms Kreps.PreferenceProperties.SequenceStrictContinuity
#print axioms Kreps.PreferenceProperties.proposition_1_14a
#print axioms Kreps.PreferenceProperties.proposition_1_14b
#print axioms Kreps.PreferenceProperties.problem_1_11
#print axioms Kreps.PreferenceProperties.UnitSegment
#print axioms Kreps.PreferenceProperties.LexicographicPreference
#print axioms Kreps.PreferenceProperties.lexicographic_rational
#print axioms Kreps.PreferenceProperties.lexicographic_not_representable
#print axioms Kreps.PreferenceProperties.problem_1_10
#print axioms Kreps.PreferenceProperties.RankPreserving
#print axioms Kreps.PreferenceProperties.rankPreserving_lt
#print axioms Kreps.PreferenceProperties.PreviousLowerRanks
#print axioms Kreps.PreferenceProperties.PreviousUpperRanks
#print axioms Kreps.PreferenceProperties.InsertedRank
#print axioms Kreps.PreferenceProperties.insertedRank_tie
#print axioms Kreps.PreferenceProperties.insertedRank_above
#print axioms Kreps.PreferenceProperties.insertedRank_below
#print axioms Kreps.PreferenceProperties.insertedRank_between
#print axioms Kreps.PreferenceProperties.previousRanks_gap
#print axioms Kreps.PreferenceProperties.insertedRank_gt
#print axioms Kreps.PreferenceProperties.insertedRank_lt
#print axioms Kreps.PreferenceProperties.insertedRank_compare
#print axioms Kreps.PreferenceProperties.definition_A2_19a
#print axioms Kreps.PreferenceProperties.definition_A2_19b
#print axioms Kreps.PreferenceProperties.definition_A2_19c
#print axioms Kreps.PreferenceProperties.definition_A2_19d_max
#print axioms Kreps.PreferenceProperties.definition_A2_19d_min
#print axioms Kreps.PreferenceProperties.appendix2_extended_sup_finite
#print axioms Kreps.PreferenceProperties.appendix2_extended_inf_finite
#print axioms Kreps.PreferenceProperties.appendix2_extended_sup_unbounded
#print axioms Kreps.PreferenceProperties.appendix2_extended_inf_unbounded
#print axioms Kreps.PreferenceProperties.proposition_A2_20a
#print axioms Kreps.PreferenceProperties.proposition_A2_20b
#print axioms Kreps.PreferenceProperties.proposition_A2_20c
#print axioms Kreps.PreferenceProperties.appendix2_empty_extrema
#print axioms Kreps.PreferenceProperties.proposition_A2_21
#print axioms Kreps.PreferenceProperties.appendix2_half_open_interval
#print axioms Kreps.PreferenceProperties.appendix2_infinite_open_intersection
#print axioms Kreps.PreferenceProperties.appendix2_relative_open_ambient
#print axioms Kreps.PreferenceProperties.appendix2_relative_closed_ambient
#print axioms Kreps.PreferenceProperties.appendix2_relative_closure
#print axioms Kreps.PreferenceProperties.appendix2_pointwise_lipschitz_rule
#print axioms Kreps.PreferenceProperties.appendix2_pointwise_lipschitz_continuousAt
#print axioms Kreps.PreferenceProperties.UnitArithmeticMean
#print axioms Kreps.PreferenceProperties.unitArithmeticMean_continuous
#print axioms Kreps.PreferenceProperties.unitArithmeticMean_grid
#print axioms Kreps.PreferenceProperties.unitArithmeticMean_dense
#print axioms Kreps.PreferenceProperties.open_cover_constants_eq
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.slopes_eq_one
#print axioms Kreps.PreferenceProperties.PositiveAffineIntervalAtlas.globalize_translations
#print axioms Kreps.PreferenceProperties.exists_strict_between
#print axioms Kreps.PreferenceProperties.dense_orderSeparating
#print axioms Kreps.PreferenceProperties.represents_of_continuous_connected
#print axioms Kreps.PreferenceProperties.NonnegativeOrthant
#print axioms Kreps.PreferenceProperties.proposition_1_15
#print axioms Kreps.PreferenceProperties.proposition_1_15_metric
#print axioms Kreps.PreferenceProperties.compact_prefChoice_nonempty
#print axioms Kreps.PreferenceProperties.proposition_1_19
#print axioms Kreps.PreferenceProperties.problem_1_13_direct
#print axioms Kreps.PreferenceProperties.JumpUtility
#print axioms Kreps.PreferenceProperties.jumpUtility_strictMono
#print axioms Kreps.PreferenceProperties.jumpUtility_represents
#print axioms Kreps.PreferenceProperties.problem_1_14c
#print axioms Kreps.PreferenceProperties.FractionUtility
#print axioms Kreps.PreferenceProperties.fractionUtility_lt_one
#print axioms Kreps.PreferenceProperties.fractionUtility_nonneg
#print axioms Kreps.PreferenceProperties.fractionUtility_represents
#print axioms Kreps.PreferenceProperties.problem_1_14d_top
#print axioms Kreps.PreferenceProperties.problem_1_14d_bot
#print axioms Kreps.PreferenceProperties.problem_1_14d_no_real_extension
#print axioms Kreps.PreferenceProperties.finite_coordinate_mono
#print axioms Kreps.PreferenceProperties.finite_coordinate_eq
#print axioms Kreps.PreferenceProperties.finite_coordinate_strict
#print axioms Kreps.PreferenceProperties.RecursiveRankStage
#print axioms Kreps.PreferenceProperties.recursiveRankStage_castSucc
#print axioms Kreps.PreferenceProperties.recursiveRankStage_last
#print axioms Kreps.PreferenceProperties.recursiveRankStage_preserving
#print axioms Kreps.PreferenceProperties.RecursiveRank
#print axioms Kreps.PreferenceProperties.recursiveRank_zero
#print axioms Kreps.PreferenceProperties.recursiveRankStage_eq_rank
#print axioms Kreps.PreferenceProperties.recursiveRank_succ
#print axioms Kreps.PreferenceProperties.recursiveRank_preserving
#print axioms Kreps.PreferenceProperties.recursiveRank_eq_iff
#print axioms Kreps.PreferenceProperties.recursiveRank_lt_iff
#print axioms Kreps.PreferenceProperties.problem_2_14d_sequence
#print axioms Kreps.PreferenceProperties.problem_2_14d_exists
#print axioms Kreps.PreferenceProperties.RecursiveRangeUtility
#print axioms Kreps.PreferenceProperties.recursiveRangeUtility_apply
#print axioms Kreps.PreferenceProperties.problem_2_14d
#print axioms Kreps.PreferenceProperties.SequenceTailSup
#print axioms Kreps.PreferenceProperties.SequenceTailInf
#print axioms Kreps.PreferenceProperties.sequenceTailSup_antitone
#print axioms Kreps.PreferenceProperties.sequenceTailInf_monotone
#print axioms Kreps.PreferenceProperties.definition_A2_22_limsup
#print axioms Kreps.PreferenceProperties.definition_A2_22_liminf
#print axioms Kreps.PreferenceProperties.sequenceTailSup_tendsto
#print axioms Kreps.PreferenceProperties.sequenceTailInf_tendsto
#print axioms Kreps.PreferenceProperties.appendix2_limsup_greatest_accumulation
#print axioms Kreps.PreferenceProperties.appendix2_liminf_least_accumulation
#print axioms Kreps.PreferenceProperties.proposition_A2_23
#print axioms Kreps.PreferenceProperties.appendix2_finite_limit
#print axioms Kreps.PreferenceProperties.appendix2_positive_infinite_limit
#print axioms Kreps.PreferenceProperties.appendix2_negative_infinite_limit
#print axioms Kreps.PreferenceProperties.sequenceTailSup_unbounded
#print axioms Kreps.PreferenceProperties.appendix2_limsup_unbounded
#print axioms Kreps.PreferenceProperties.sequenceTailInf_unbounded
#print axioms Kreps.PreferenceProperties.appendix2_liminf_unbounded
#print axioms Kreps.PreferenceProperties.MeanUnitScale
#print axioms Kreps.PreferenceProperties.meanUnitScale_denseRange
#print axioms Kreps.PreferenceProperties.meanCardinalScale_continuous
#print axioms Kreps.PreferenceProperties.meanCardinalScale_grid_mean
#print axioms Kreps.PreferenceProperties.meanCardinalScale_mean
#print axioms Kreps.PreferenceProperties.exists_continuous_bisymmetricMean_scale
#print axioms Kreps.PreferenceProperties.local_midpoint_nonpos
#print axioms Kreps.PreferenceProperties.local_midpoint_affine_Icc
#print axioms Kreps.PreferenceProperties.local_midpoint_affine_interval
#print axioms Kreps.PreferenceProperties.intervalProductPath
#print axioms Kreps.PreferenceProperties.intervalProductPath_continuous
#print axioms Kreps.PreferenceProperties.intervalProductPath_endpoints
#print axioms Kreps.PreferenceProperties.intervalProductPath_sum_monotone
#print axioms Kreps.PreferenceProperties.sum_represents_of_locally_represents
#print axioms Kreps.PreferenceProperties.MonotonePreference
#print axioms Kreps.PreferenceProperties.StrictlyMonotonePreference
#print axioms Kreps.PreferenceProperties.StrictAllIncreasePreference
#print axioms Kreps.PreferenceProperties.GloballyInsatiable
#print axioms Kreps.PreferenceProperties.LocallyInsatiable
#print axioms Kreps.PreferenceProperties.proposition_2_2_monotone
#print axioms Kreps.PreferenceProperties.proposition_2_2_strict
#print axioms Kreps.PreferenceProperties.monotone_all_representations
#print axioms Kreps.PreferenceProperties.monotone_of_some_representation
#print axioms Kreps.PreferenceProperties.strict_all_representations
#print axioms Kreps.PreferenceProperties.strict_of_some_representation
#print axioms Kreps.PreferenceProperties.strictlyMonotone_monotone
#print axioms Kreps.PreferenceProperties.strictlyMonotone_strictAllIncrease
#print axioms Kreps.PreferenceProperties.locallyInsatiable_iff_open
#print axioms Kreps.PreferenceProperties.locallyInsatiable_global
#print axioms Kreps.PreferenceProperties.globallyInsatiable_iff_utility
#print axioms Kreps.PreferenceProperties.locallyInsatiable_iff_utility
#print axioms Kreps.PreferenceProperties.RaisedBundle
#print axioms Kreps.PreferenceProperties.raisedBundle_dist_le
#print axioms Kreps.PreferenceProperties.strictAllIncrease_locallyInsatiable
#print axioms Kreps.PreferenceProperties.monotone_locallyInsatiable_strictAllIncrease
#print axioms Kreps.PreferenceProperties.continuous_strictAllIncrease_monotone
#print axioms Kreps.PreferenceProperties.problem_2_6
#print axioms Kreps.PreferenceProperties.Mix
#print axioms Kreps.PreferenceProperties.mix_zero
#print axioms Kreps.PreferenceProperties.mix_one
#print axioms Kreps.PreferenceProperties.mix_self
#print axioms Kreps.PreferenceProperties.mix_swap
#print axioms Kreps.PreferenceProperties.ConvexMenu
#print axioms Kreps.PreferenceProperties.convexMenu_iff
#print axioms Kreps.PreferenceProperties.ConvexPreference
#print axioms Kreps.PreferenceProperties.StrictlyConvexPreference
#print axioms Kreps.PreferenceProperties.SemiStrictlyConvexPreference
#print axioms Kreps.PreferenceProperties.strictlyConvex_convex
#print axioms Kreps.PreferenceProperties.strictlyConvex_semiStrict
#print axioms Kreps.PreferenceProperties.convexPreference_iff_contours
#print axioms Kreps.PreferenceProperties.proposition_2_5
#print axioms Kreps.PreferenceProperties.proposition_2_6_convex
#print axioms Kreps.PreferenceProperties.proposition_2_6_unique
#print axioms Kreps.PreferenceProperties.problem_2_4
#print axioms Kreps.PreferenceProperties.BlockBundle
#print axioms Kreps.PreferenceProperties.ReplaceBlock
#print axioms Kreps.PreferenceProperties.WeaklySeparable
#print axioms Kreps.PreferenceProperties.weaklySeparable_strict
#print axioms Kreps.PreferenceProperties.BaselineSubutility
#print axioms Kreps.PreferenceProperties.baseline_comparison_iff
#print axioms Kreps.PreferenceProperties.BlockScores
#print axioms Kreps.PreferenceProperties.blockScores_update
#print axioms Kreps.PreferenceProperties.ScoreRepresentative
#print axioms Kreps.PreferenceProperties.scoreRepresentative_spec
#print axioms Kreps.PreferenceProperties.SubutilityAggregator
#print axioms Kreps.PreferenceProperties.IncreasingAggregator
#print axioms Kreps.PreferenceProperties.WeakSeparabilityRepresentation
#print axioms Kreps.PreferenceProperties.aggregator_coordinate_comparison
#print axioms Kreps.PreferenceProperties.weaklySeparable_of_representation
#print axioms Kreps.PreferenceProperties.subutilityAggregator_factors
#print axioms Kreps.PreferenceProperties.subutilityAggregator_increasing
#print axioms Kreps.PreferenceProperties.weakSeparabilityRepresentation_of_separable
#print axioms Kreps.PreferenceProperties.proposition_2_12
#print axioms Kreps.PreferenceProperties.SampledWeightedUtility
#print axioms Kreps.PreferenceProperties.sampledWeightedTerm_upperSemicontinuous
#print axioms Kreps.PreferenceProperties.sampledWeightedUtility_upperSemicontinuous
#print axioms Kreps.PreferenceProperties.weightedUtility_upperSemicontinuous
#print axioms Kreps.PreferenceProperties.sampledWeightedTerm_mono
#print axioms Kreps.PreferenceProperties.sampledWeightedUtility_mono
#print axioms Kreps.PreferenceProperties.sampledWeightedUtility_strict
#print axioms Kreps.PreferenceProperties.sampledWeightedUtility_represents
#print axioms Kreps.PreferenceProperties.DyadicWeight
#print axioms Kreps.PreferenceProperties.dyadicWeight_formula
#print axioms Kreps.PreferenceProperties.dyadicWeight_pos
#print axioms Kreps.PreferenceProperties.dyadicWeight_summable
#print axioms Kreps.PreferenceProperties.sampledDyadicUtility_formula
#print axioms Kreps.PreferenceProperties.problem_2_10
#print axioms Kreps.PreferenceProperties.problem_2_10_representation
#print axioms Kreps.PreferenceProperties.upperSemicontinuousAt_real_coe
#print axioms Kreps.PreferenceProperties.lowerSemicontinuousAt_real_coe
#print axioms Kreps.PreferenceProperties.appendix2_upper_sequence_iff
#print axioms Kreps.PreferenceProperties.appendix2_lower_sequence_iff
#print axioms Kreps.PreferenceProperties.proposition_A2_25_upper
#print axioms Kreps.PreferenceProperties.proposition_A2_25_lower
#print axioms Kreps.PreferenceProperties.TenSequence
#print axioms Kreps.PreferenceProperties.tenSequence_tendsto
#print axioms Kreps.PreferenceProperties.tenSequence_no_accumulation
#print axioms Kreps.PreferenceProperties.tenSequence_no_limit
#print axioms Kreps.PreferenceProperties.AlternatingDecimalSequence
#print axioms Kreps.PreferenceProperties.alternatingDecimal_even
#print axioms Kreps.PreferenceProperties.alternatingDecimal_odd
#print axioms Kreps.PreferenceProperties.decimalPerturbation_tendsto
#print axioms Kreps.PreferenceProperties.alternatingDecimal_subsequence_limits
#print axioms Kreps.PreferenceProperties.appendix2_alternating_accumulation
#print axioms Kreps.PreferenceProperties.appendix2_alternating_no_limit
#print axioms Kreps.PreferenceProperties.PreservesPairSumEquality
#print axioms Kreps.PreferenceProperties.preservesPairSumEquality_symm
#print axioms Kreps.PreferenceProperties.preservesPairSumEquality_midpoint
#print axioms Kreps.PreferenceProperties.preservesPairSumEquality_affine_left
#print axioms Kreps.PreferenceProperties.pair_additive_affine_unique
#print axioms Kreps.PreferenceProperties.pair_additive_positive_affine_unique
#print axioms Kreps.PreferenceProperties.family_additive_positive_affine_unique
#print axioms Kreps.PreferenceProperties.normalized_additive_scales_unique
#print axioms Kreps.PreferenceProperties.ConcaveUtility
#print axioms Kreps.PreferenceProperties.StrictlyConcaveUtility
#print axioms Kreps.PreferenceProperties.QuasiConcaveUtility
#print axioms Kreps.PreferenceProperties.SemiStrictlyQuasiConcaveUtility
#print axioms Kreps.PreferenceProperties.StrictlyQuasiConcaveUtility
#print axioms Kreps.PreferenceProperties.concaveUtility_iff_concaveOn
#print axioms Kreps.PreferenceProperties.strictlyConcaveUtility_iff_strictConcaveOn
#print axioms Kreps.PreferenceProperties.quasiConcaveUtility_iff_quasiconcaveOn
#print axioms Kreps.PreferenceProperties.concaveUtility_quasi
#print axioms Kreps.PreferenceProperties.concaveUtility_semiStrict
#print axioms Kreps.PreferenceProperties.strictlyConcaveUtility_strictQuasi
#print axioms Kreps.PreferenceProperties.proposition_2_8b_quasi
#print axioms Kreps.PreferenceProperties.proposition_2_8b_strict
#print axioms Kreps.PreferenceProperties.proposition_2_8b_semiStrict
#print axioms Kreps.PreferenceProperties.proposition_2_8a_concave
#print axioms Kreps.PreferenceProperties.proposition_2_8a_strict
#print axioms Kreps.PreferenceProperties.quasiConcave_strictMono_transform
#print axioms Kreps.PreferenceProperties.PairBundle
#print axioms Kreps.PreferenceProperties.ReverseTiePreference
#print axioms Kreps.PreferenceProperties.reverseTie_rational
#print axioms Kreps.PreferenceProperties.reverseTie_strictAllIncrease
#print axioms Kreps.PreferenceProperties.reverseTie_not_monotone
#print axioms Kreps.PreferenceProperties.reverseTie_locallyInsatiable
#print axioms Kreps.PreferenceProperties.reverseTie_not_continuous
#print axioms Kreps.PreferenceProperties.problem_2_6_without_continuity
#print axioms Kreps.PreferenceProperties.mix_dist
#print axioms Kreps.PreferenceProperties.problem_2_3_implication
#print axioms Kreps.PreferenceProperties.strictlyConvex_global_local
#print axioms Kreps.PreferenceProperties.proposition_2_9_forward
#print axioms Kreps.PreferenceProperties.compact_choice_of_continuous_utility
#print axioms Kreps.PreferenceProperties.indifference_on_connected_image
#print axioms Kreps.PreferenceProperties.lemma_2_10
#print axioms Kreps.PreferenceProperties.monotone_path_crossing
#print axioms Kreps.PreferenceProperties.AssignedBlock
#print axioms Kreps.PreferenceProperties.LeftoverBlock
#print axioms Kreps.PreferenceProperties.GroupCommodities
#print axioms Kreps.PreferenceProperties.UngroupCommodities
#print axioms Kreps.PreferenceProperties.ungroupCommodities_some
#print axioms Kreps.PreferenceProperties.ungroupCommodities_none
#print axioms Kreps.PreferenceProperties.ungroup_groupCommodities
#print axioms Kreps.PreferenceProperties.group_ungroupCommodities
#print axioms Kreps.PreferenceProperties.commodityGroupingEquiv
#print axioms Kreps.PreferenceProperties.orthantNNRealEquiv
#print axioms Kreps.PreferenceProperties.orthantGrouping
#print axioms Kreps.PreferenceProperties.orthantGrouping_block
#print axioms Kreps.PreferenceProperties.orthantGrouping_leftover
#print axioms Kreps.PreferenceProperties.ungroup_replace_in_block
#print axioms Kreps.PreferenceProperties.ungroup_replace_outside
#print axioms Kreps.PreferenceProperties.assigned_blocks_disjoint
#print axioms Kreps.PreferenceProperties.assigned_leftover_iff
#print axioms Kreps.PreferenceProperties.exists_commodity_assignment
#print axioms Kreps.PreferenceProperties.proposition_2_12_orthant
#print axioms Kreps.PreferenceProperties.PolygonalCurve
#print axioms Kreps.PreferenceProperties.polygonalCurve_int
#print axioms Kreps.PreferenceProperties.polygonalCurve_formula
#print axioms Kreps.PreferenceProperties.integer_unit_intervals_locallyFinite
#print axioms Kreps.PreferenceProperties.polygonalCurve_continuous
#print axioms Kreps.PreferenceProperties.polygonalCurve_range_preconnected
#print axioms Kreps.PreferenceProperties.SequenceCurve
#print axioms Kreps.PreferenceProperties.sequenceCurve_nat
#print axioms Kreps.PreferenceProperties.sequenceCurve_continuous
#print axioms Kreps.PreferenceProperties.sequenceCurve_contains_range
#print axioms Kreps.PreferenceProperties.UtilityRangeOrderIso
#print axioms Kreps.PreferenceProperties.utilityTransform_continuous_range
#print axioms Kreps.PreferenceProperties.replaceBlock_continuous
#print axioms Kreps.PreferenceProperties.baselineSubutility_continuous
#print axioms Kreps.PreferenceProperties.baselineSubutility_ordConnected
#print axioms Kreps.PreferenceProperties.baselineSubutility_represents_context
#print axioms Kreps.PreferenceProperties.baselineSubutility_transform_continuous
#print axioms Kreps.PreferenceProperties.scoreRepresentatives_update
#print axioms Kreps.PreferenceProperties.subutilityAggregator_coordinate_continuous
#print axioms Kreps.PreferenceProperties.OneGood
#print axioms Kreps.PreferenceProperties.NonattainingUtility
#print axioms Kreps.PreferenceProperties.nonattainingUtility_strictQuasi
#print axioms Kreps.PreferenceProperties.nonattainingPreference_strictConvex
#print axioms Kreps.PreferenceProperties.UnitMenu
#print axioms Kreps.PreferenceProperties.unitMenu_nonempty
#print axioms Kreps.PreferenceProperties.unitMenu_image
#print axioms Kreps.PreferenceProperties.unitMenu_compact
#print axioms Kreps.PreferenceProperties.unitMenu_convex
#print axioms Kreps.PreferenceProperties.nonattainingUtility_empty
#print axioms Kreps.PreferenceProperties.problem_2_2
#print axioms Kreps.PreferenceProperties.FlatUtility
#print axioms Kreps.PreferenceProperties.flatUtility_monotone
#print axioms Kreps.PreferenceProperties.flatUtility_quasi
#print axioms Kreps.PreferenceProperties.flatUtility_globallyInsatiable
#print axioms Kreps.PreferenceProperties.flatUtility_not_locallyInsatiable
#print axioms Kreps.PreferenceProperties.problem_2_3_counterexample
#print axioms Kreps.PreferenceProperties.Diagonal
#print axioms Kreps.PreferenceProperties.diagonal_continuous
#print axioms Kreps.PreferenceProperties.MinCoordinate
#print axioms Kreps.PreferenceProperties.MaxCoordinate
#print axioms Kreps.PreferenceProperties.minCoordinate_nonneg
#print axioms Kreps.PreferenceProperties.minCoordinate_le
#print axioms Kreps.PreferenceProperties.le_maxCoordinate
#print axioms Kreps.PreferenceProperties.maxCoordinate_nonneg
#print axioms Kreps.PreferenceProperties.diagonal_indifference_exists
#print axioms Kreps.PreferenceProperties.diagonal_weak_iff
#print axioms Kreps.PreferenceProperties.diagonal_indifferent_iff
#print axioms Kreps.PreferenceProperties.IndifferenceClass
#print axioms Kreps.PreferenceProperties.indifferenceClass_no_ball
#print axioms Kreps.PreferenceProperties.indifferenceClass_interior_empty
#print axioms Kreps.PreferenceProperties.indifferenceCurve_decreasing
#print axioms Kreps.PreferenceProperties.indifference_mixture_strict
#print axioms Kreps.PreferenceProperties.NetUtility
#print axioms Kreps.PreferenceProperties.netUtility_continuous
#print axioms Kreps.PreferenceProperties.netPreference_locallyInsatiable
#print axioms Kreps.PreferenceProperties.AvoidingPath
#print axioms Kreps.PreferenceProperties.avoidingPath_continuous
#print axioms Kreps.PreferenceProperties.PathMiddle
#print axioms Kreps.PreferenceProperties.avoidingPath_coordinate_bounds
#print axioms Kreps.PreferenceProperties.avoidingPath_no_indifference
#print axioms Kreps.PreferenceProperties.problem_2_7
#print axioms Kreps.PreferenceProperties.netPreference_not_monotone
#print axioms Kreps.PreferenceProperties.StrictRankSeparator
#print axioms Kreps.PreferenceProperties.dense_strictRankSeparator
#print axioms Kreps.PreferenceProperties.InteriorRankSet
#print axioms Kreps.PreferenceProperties.interiorRank_witness
#print axioms Kreps.PreferenceProperties.interiorRank_between
#print axioms Kreps.PreferenceProperties.interiorRankSet_countable
#print axioms Kreps.PreferenceProperties.RationalUnit
#print axioms Kreps.PreferenceProperties.interiorRanks_orderIso
#print axioms Kreps.PreferenceProperties.StronglySeparable
#print axioms Kreps.PreferenceProperties.NontrivialBlock
#print axioms Kreps.PreferenceProperties.ThreeNontrivialBlocks
#print axioms Kreps.PreferenceProperties.stronglySeparable_weakly
#print axioms Kreps.PreferenceProperties.nontrivialBlock_iff_every_context
#print axioms Kreps.PreferenceProperties.threeNontrivialBlocks_card
#print axioms Kreps.PreferenceProperties.AdditiveUtility
#print axioms Kreps.PreferenceProperties.AdditivelyRepresentable
#print axioms Kreps.PreferenceProperties.additiveUtility_piecewise
#print axioms Kreps.PreferenceProperties.proposition_2_14_additive
#print axioms Kreps.PreferenceProperties.additiveUtility_continuous
#print axioms Kreps.PreferenceProperties.continuousPreference_of_additive
#print axioms Kreps.PreferenceProperties.LiftedUtility
#print axioms Kreps.PreferenceProperties.liftedUtility_represents
#print axioms Kreps.PreferenceProperties.liftedUtility_agrees
#print axioms Kreps.PreferenceProperties.liftedUtility_range
#print axioms Kreps.PreferenceProperties.continuous_of_ordConnected_range
#print axioms Kreps.PreferenceProperties.liftedUtility_continuous
#print axioms Kreps.PreferenceProperties.problem_2_14c
#print axioms Kreps.PreferenceProperties.TwoGoodProduct
#print axioms Kreps.PreferenceProperties.product_mix_ge_average_of_cross
#print axioms Kreps.PreferenceProperties.product_mix_ge_min
#print axioms Kreps.PreferenceProperties.twoGoodProduct_continuous
#print axioms Kreps.PreferenceProperties.twoGoodProduct_quasiConcave
#print axioms Kreps.PreferenceProperties.product_mix_gt_average_of_cross
#print axioms Kreps.PreferenceProperties.product_mix_gt_lower
#print axioms Kreps.PreferenceProperties.twoGoodProduct_pos_iff
#print axioms Kreps.PreferenceProperties.twoGoodProduct_mix_strict
#print axioms Kreps.PreferenceProperties.twoGoodProduct_mix_pos
#print axioms Kreps.PreferenceProperties.proposition_A3_17a
#print axioms Kreps.PreferenceProperties.proposition_A3_17b_min
#print axioms Kreps.PreferenceProperties.proposition_A3_17c_max
#print axioms Kreps.PreferenceProperties.concaveOn_finite_sum
#print axioms Kreps.PreferenceProperties.convexOn_finite_sum
#print axioms Kreps.PreferenceProperties.proposition_A3_17b_sum
#print axioms Kreps.PreferenceProperties.proposition_A3_17c_sum
#print axioms Kreps.PreferenceProperties.proposition_A3_17d
#print axioms Kreps.PreferenceProperties.proposition_A3_17e
#print axioms Kreps.PreferenceProperties.proposition_A3_17f
#print axioms Kreps.PreferenceProperties.proposition_A3_23
#print axioms Kreps.PreferenceProperties.convexOn_iff_convex_epigraph_appendix
#print axioms Kreps.PreferenceProperties.proposition_A3_17g_concave
#print axioms Kreps.PreferenceProperties.proposition_A3_17g_convex
#print axioms Kreps.PreferenceProperties.QuasiConvexUtility
#print axioms Kreps.PreferenceProperties.StrictlyQuasiConvexUtility
#print axioms Kreps.PreferenceProperties.proposition_A3_19
#print axioms Kreps.PreferenceProperties.proposition_A3_19_quasiConvex
#print axioms Kreps.PreferenceProperties.proposition_A3_20
#print axioms Kreps.PreferenceProperties.proposition_A3_20_strict
#print axioms Kreps.PreferenceProperties.proposition_A3_21
#print axioms Kreps.PreferenceProperties.proposition_A3_21_unique
#print axioms Kreps.PreferenceProperties.proposition_A3_21_ambient
#print axioms Kreps.PreferenceProperties.proposition_A3_22_concave
#print axioms Kreps.PreferenceProperties.proposition_A3_22_strict
#print axioms Kreps.PreferenceProperties.strictMono_coordinate_represents
#print axioms Kreps.PreferenceProperties.pair_chart_positive_affine_unique
#print axioms Kreps.PreferenceProperties.common_affine_slope_eq_one
#print axioms Kreps.PreferenceProperties.pair_chart_translation_of_companion_increment
#print axioms Kreps.PreferenceProperties.pair_chart_identity_of_companion_and_baseline
#print axioms Kreps.PreferenceProperties.ConvexWarp
#print axioms Kreps.PreferenceProperties.convexWarp_strictMono
#print axioms Kreps.PreferenceProperties.identityUtility_concave
#print axioms Kreps.PreferenceProperties.convexWarp_not_concave
#print axioms Kreps.PreferenceProperties.problem_2_5a
#print axioms Kreps.PreferenceProperties.jumpUtility_not_continuous
#print axioms Kreps.PreferenceProperties.problem_2_5b
#print axioms Kreps.PreferenceProperties.diagonal_indifference_unique
#print axioms Kreps.PreferenceProperties.diagonal_indifference_existsUnique
#print axioms Kreps.PreferenceProperties.DiagonalCoordinate
#print axioms Kreps.PreferenceProperties.diagonalCoordinate_spec
#print axioms Kreps.PreferenceProperties.DiagonalUtility
#print axioms Kreps.PreferenceProperties.diagonalUtility_nonneg
#print axioms Kreps.PreferenceProperties.diagonalUtility_represents
#print axioms Kreps.PreferenceProperties.diagonalUtility_diagonal
#print axioms Kreps.PreferenceProperties.continuous_of_full_nonnegative_range
#print axioms Kreps.PreferenceProperties.diagonalUtility_continuous
#print axioms Kreps.PreferenceProperties.proposition_2_9_monotone
#print axioms Kreps.PreferenceProperties.continuous_representation_strictAllIncrease
#print axioms Kreps.PreferenceProperties.RationalRankValue
#print axioms Kreps.PreferenceProperties.rationalRankValue_bounds
#print axioms Kreps.PreferenceProperties.rationalRankValue_strictMono
#print axioms Kreps.PreferenceProperties.RankCutSet
#print axioms Kreps.PreferenceProperties.rankCutSet_nonempty
#print axioms Kreps.PreferenceProperties.rankCutSet_bddAbove
#print axioms Kreps.PreferenceProperties.RankCutUtility
#print axioms Kreps.PreferenceProperties.rankCutUtility_nonneg
#print axioms Kreps.PreferenceProperties.rankCutUtility_le_one
#print axioms Kreps.PreferenceProperties.rankCutUtility_mono
#print axioms Kreps.PreferenceProperties.rankCutUtility_upper
#print axioms Kreps.PreferenceProperties.rankCutUtility_lower
#print axioms Kreps.PreferenceProperties.rankCutUtility_at_rank
#print axioms Kreps.PreferenceProperties.rankCutUtility_strict
#print axioms Kreps.PreferenceProperties.rankCutUtility_represents
#print axioms Kreps.PreferenceProperties.rankCutUtility_attains_rationals
#print axioms Kreps.PreferenceProperties.OpenIntervalMenu
#print axioms Kreps.PreferenceProperties.UpperRayMenu
#print axioms Kreps.PreferenceProperties.openIntervalMenu_convex
#print axioms Kreps.PreferenceProperties.upperRayMenu_convex
#print axioms Kreps.PreferenceProperties.strictlyMonotone_openInterval_empty
#print axioms Kreps.PreferenceProperties.strictlyMonotone_upperRay_empty
#print axioms Kreps.PreferenceProperties.problem_2_2_intervals
#print axioms Kreps.PreferenceProperties.ProductPlateau
#print axioms Kreps.PreferenceProperties.productPlateau_below
#print axioms Kreps.PreferenceProperties.productPlateau_middle
#print axioms Kreps.PreferenceProperties.productPlateau_above
#print axioms Kreps.PreferenceProperties.productPlateau_monotone
#print axioms Kreps.PreferenceProperties.productPlateau_continuous
#print axioms Kreps.PreferenceProperties.PlateauProductUtility
#print axioms Kreps.PreferenceProperties.plateauProductUtility_continuous
#print axioms Kreps.PreferenceProperties.plateauProductUtility_quasiConcave
#print axioms Kreps.PreferenceProperties.plateauProductUtility_not_semiStrict
#print axioms Kreps.PreferenceProperties.plateauProductPreference_not_semiStrict
#print axioms Kreps.PreferenceProperties.plateauProductPreference_no_concave_representation
#print axioms Kreps.PreferenceProperties.problem_2_8a_first
#print axioms Kreps.PreferenceProperties.SplitProductUtility
#print axioms Kreps.PreferenceProperties.splitProductUtility_below
#print axioms Kreps.PreferenceProperties.splitProductUtility_at_lower
#print axioms Kreps.PreferenceProperties.splitProductUtility_at_upper
#print axioms Kreps.PreferenceProperties.splitProductUtility_above
#print axioms Kreps.PreferenceProperties.splitProductUtility_zero
#print axioms Kreps.PreferenceProperties.splitProductUtility_nonneg
#print axioms Kreps.PreferenceProperties.splitProductUtility_strict_of_product_lt
#print axioms Kreps.PreferenceProperties.splitProductUtility_product_le
#print axioms Kreps.PreferenceProperties.splitProductPreference_convex
#print axioms Kreps.PreferenceProperties.splitProductPreference_semiStrict
#print axioms Kreps.PreferenceProperties.SplitProductApproach
#print axioms Kreps.PreferenceProperties.splitProductApproach_rank
#print axioms Kreps.PreferenceProperties.splitProductApproach_tendsto
#print axioms Kreps.PreferenceProperties.splitProductPreference_not_continuous
#print axioms Kreps.PreferenceProperties.recursiveRank_has_between
#print axioms Kreps.PreferenceProperties.recursiveRank_first_between
#print axioms Kreps.PreferenceProperties.recursiveRank_between_mem_closure
#print axioms Kreps.PreferenceProperties.RecursiveRankInterval
#print axioms Kreps.PreferenceProperties.recursiveRank_range_subset_interval
#print axioms Kreps.PreferenceProperties.recursiveRankInterval_ordConnected
#print axioms Kreps.PreferenceProperties.recursiveRankInterval_minimal
#print axioms Kreps.PreferenceProperties.recursiveRankInterval_subset_closure
#print axioms Kreps.PreferenceProperties.recursiveRank_dense_in_interval
#print axioms Kreps.PreferenceProperties.problem_2_14e
#print axioms Kreps.PreferenceProperties.RatioSumUtility
#print axioms Kreps.PreferenceProperties.RatioAxisBundle
#print axioms Kreps.PreferenceProperties.ratioSumUtility_axis
#print axioms Kreps.PreferenceProperties.ratioAxisBundle_mix
#print axioms Kreps.PreferenceProperties.concaveUtility_ratioAxis
#print axioms Kreps.PreferenceProperties.concaveUtility_ratioAxis_bound
#print axioms Kreps.PreferenceProperties.RatioRayBundle
#print axioms Kreps.PreferenceProperties.ratioSumUtility_ray
#print axioms Kreps.PreferenceProperties.ratioSumUtility_ray_mix
#print axioms Kreps.PreferenceProperties.stronglySeparable_complement_iff
#print axioms Kreps.PreferenceProperties.stronglySeparable_common_update_iff
#print axioms Kreps.PreferenceProperties.ThreeCoordinateBundle
#print axioms Kreps.PreferenceProperties.threeCoordinateBundle_update_first
#print axioms Kreps.PreferenceProperties.threeCoordinateBundle_update_second
#print axioms Kreps.PreferenceProperties.threeCoordinateBundle_update_third
#print axioms Kreps.PreferenceProperties.ThreeFactorIndependent
#print axioms Kreps.PreferenceProperties.stronglySeparable_threeFactor
#print axioms Kreps.PreferenceProperties.indifferent_transitive
#print axioms Kreps.PreferenceProperties.threeFactor_first_indifferent
#print axioms Kreps.PreferenceProperties.threeFactor_second_indifferent
#print axioms Kreps.PreferenceProperties.threeFactor_third_indifferent
#print axioms Kreps.PreferenceProperties.third_factor_hexagon
#print axioms Kreps.PreferenceProperties.third_factor_local_compensation
#print axioms Kreps.PreferenceProperties.third_factor_local_hexagon
#print axioms Kreps.PreferenceProperties.BaselineScores
#print axioms Kreps.PreferenceProperties.ScoreAggregator
#print axioms Kreps.PreferenceProperties.baselineScores_reference
#print axioms Kreps.PreferenceProperties.baselineScores_continuous
#print axioms Kreps.PreferenceProperties.baselineScores_ordConnected
#print axioms Kreps.PreferenceProperties.scoreAggregator_factors
#print axioms Kreps.PreferenceProperties.scoreAggregator_strictMono
#print axioms Kreps.PreferenceProperties.scoreAggregator_continuous
#print axioms Kreps.PreferenceProperties.scoreRepresentatives_piecewise
#print axioms Kreps.PreferenceProperties.scoreAggregator_stronglySeparable
#print axioms Kreps.PreferenceProperties.scoreAggregator_reference_axis
#print axioms Kreps.PreferenceProperties.exists_le_bundle_with_sum
#print axioms Kreps.PreferenceProperties.pairSumInvariant_lt_of_sum_lt
#print axioms Kreps.PreferenceProperties.pairSumInvariant_comparison
#print axioms Kreps.PreferenceProperties.pairSumInvariant_represents
#print axioms Kreps.PreferenceProperties.open_real_set_has_pair
#print axioms Kreps.PreferenceProperties.pair_chart_positive_affine_unique_on
#print axioms Kreps.PreferenceProperties.pair_chart_translation_on
#print axioms Kreps.PreferenceProperties.additiveUtility_strictMono
#print axioms Kreps.PreferenceProperties.additive_comparison_of_interior
#print axioms Kreps.PreferenceProperties.ActiveCoordinateExtend
#print axioms Kreps.PreferenceProperties.ActiveCoordinateRestrict
#print axioms Kreps.PreferenceProperties.activeCoordinateExtend_active
#print axioms Kreps.PreferenceProperties.activeCoordinateRestrict_extend
#print axioms Kreps.PreferenceProperties.activeCoordinateExtend_restrict
#print axioms Kreps.PreferenceProperties.activeCoordinateExtend_continuous
#print axioms Kreps.PreferenceProperties.ActiveCoordinateOrderIso
#print axioms Kreps.PreferenceProperties.activeCoordinateExtend_piecewise
#print axioms Kreps.PreferenceProperties.stronglySeparable_activeCoordinates
#print axioms Kreps.PreferenceProperties.ActiveCoordinateUtility
#print axioms Kreps.PreferenceProperties.additiveUtility_activeCoordinates
#print axioms Kreps.PreferenceProperties.activeCoordinateUtility_continuous
#print axioms Kreps.PreferenceProperties.activeCoordinateUtility_strictMono
#print axioms Kreps.PreferenceProperties.represents_activeCoordinates
#print axioms Kreps.PreferenceProperties.nontrivial_interval_interior_nonempty
#print axioms Kreps.PreferenceProperties.coordinateMap_piecewise
#print axioms Kreps.PreferenceProperties.stronglySeparable_coordinate_pullback
#print axioms Kreps.PreferenceProperties.InteriorScalarInclusion
#print axioms Kreps.PreferenceProperties.interiorScalarInclusion_continuous
#print axioms Kreps.PreferenceProperties.interiorScalarInclusion_strictMono
#print axioms Kreps.PreferenceProperties.interiorScalarInclusion_stronglySeparable
#print axioms Kreps.PreferenceProperties.continuous_of_dense_rational_range
#print axioms Kreps.PreferenceProperties.rankCutUtility_continuous
#print axioms Kreps.PreferenceProperties.continuous_represents_of_continuous_connected
#print axioms Kreps.PreferenceProperties.proposition_2_9
#print axioms Kreps.PreferenceProperties.proposition_2_9_metric
#print axioms Kreps.PreferenceProperties.splitProductPreference_no_concave_representation
#print axioms Kreps.PreferenceProperties.problem_2_8a_second
#print axioms Kreps.PreferenceProperties.ratioSum_rep_eq_of_value_eq
#print axioms Kreps.PreferenceProperties.ratioSum_concave_increment
#print axioms Kreps.PreferenceProperties.problem_2_8b_no_concave_representation
#print axioms Kreps.PreferenceProperties.SampleBrackets
#print axioms Kreps.PreferenceProperties.SampleContainsExtremes
#print axioms Kreps.PreferenceProperties.sampleBrackets_of_extremes
#print axioms Kreps.PreferenceProperties.SampleRankCut
#print axioms Kreps.PreferenceProperties.SampleRankExtension
#print axioms Kreps.PreferenceProperties.sampleRankCut_nonempty
#print axioms Kreps.PreferenceProperties.sampleRankCut_bddAbove
#print axioms Kreps.PreferenceProperties.sampleRankExtension_lower
#print axioms Kreps.PreferenceProperties.sampleRankExtension_upper
#print axioms Kreps.PreferenceProperties.sampleRankExtension_at_sample
#print axioms Kreps.PreferenceProperties.sampleRankExtension_mono
#print axioms Kreps.PreferenceProperties.sampleRankExtension_strict
#print axioms Kreps.PreferenceProperties.sampleRankExtension_represents
#print axioms Kreps.PreferenceProperties.continuous_of_interval_closure_range
#print axioms Kreps.PreferenceProperties.rational_preference_pullback
#print axioms Kreps.PreferenceProperties.continuousPreference_pullback
#print axioms Kreps.PreferenceProperties.threeCoordinateBundle_continuous
#print axioms Kreps.PreferenceProperties.ThreeCoordinatePreference
#print axioms Kreps.PreferenceProperties.third_factor_interior_rank
#print axioms Kreps.PreferenceProperties.third_factor_local_hexagon_of_nontrivial
#print axioms Kreps.PreferenceProperties.stronglySeparable_local_hexagon
#print axioms Kreps.PreferenceProperties.coordinateMap_update
#print axioms Kreps.PreferenceProperties.represents_additive_of_pair_scale_invariance
#print axioms Kreps.PreferenceProperties.CompanionChartFamily
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.mk
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.domain
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.coord
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.open_domain
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.interval
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.continuous
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.increasing
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.firstReference
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.secondReference
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.first_mem
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.second_mem
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.pair_compatible
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.exists_calibration
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.calibrated_companion
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.calibrated_target_transition
#print axioms Kreps.PreferenceProperties.NontrivialScalarIndices
#print axioms Kreps.PreferenceProperties.ActiveScalarUtility
#print axioms Kreps.PreferenceProperties.inactiveScalar_subsingleton
#print axioms Kreps.PreferenceProperties.activeScalarUtility_continuous
#print axioms Kreps.PreferenceProperties.activeScalarUtility_strictMono
#print axioms Kreps.PreferenceProperties.activeScalarUtility_stronglySeparable
#print axioms Kreps.PreferenceProperties.three_nontrivialScalarIndices
#print axioms Kreps.PreferenceProperties.continuous_additive_of_activeScalar
#print axioms Kreps.PreferenceProperties.nontrivialBlock_baselineScores_nontrivial
#print axioms Kreps.PreferenceProperties.threeNontrivialBlocks_baselineScores
#print axioms Kreps.PreferenceProperties.ScoreLiftedCoordinate
#print axioms Kreps.PreferenceProperties.scoreLiftedCoordinate_continuous
#print axioms Kreps.PreferenceProperties.represents_additive_of_scoreAggregator
#print axioms Kreps.PreferenceProperties.continuous_additive_of_scoreAggregator
#print axioms Kreps.PreferenceProperties.exists_full_interval_additive_extension
#print axioms Kreps.PreferenceProperties.NonnegativeCone
#print axioms Kreps.PreferenceProperties.ScaleInCone
#print axioms Kreps.PreferenceProperties.HomogeneousOfDegree
#print axioms Kreps.PreferenceProperties.homogeneousOfDegree_one_iff
#print axioms Kreps.PreferenceProperties.orthant_nonnegativeCone
#print axioms Kreps.PreferenceProperties.OrthantZero
#print axioms Kreps.PreferenceProperties.ScaleBundle
#print axioms Kreps.PreferenceProperties.scaleBundle_eq_cone
#print axioms Kreps.PreferenceProperties.scaleBundle_zero
#print axioms Kreps.PreferenceProperties.scaleBundle_one
#print axioms Kreps.PreferenceProperties.scaleBundle_origin
#print axioms Kreps.PreferenceProperties.scaleBundle_mul
#print axioms Kreps.PreferenceProperties.scaleBundle_inv
#print axioms Kreps.PreferenceProperties.scaleBundle_continuous
#print axioms Kreps.PreferenceProperties.scaleBundle_ray_continuous
#print axioms Kreps.PreferenceProperties.scaleBundle_pow_tendsto_zero
#print axioms Kreps.PreferenceProperties.HomotheticPreference
#print axioms Kreps.PreferenceProperties.homothetic_scale_iff
#print axioms Kreps.PreferenceProperties.homothetic_scale_strict_iff
#print axioms Kreps.PreferenceProperties.homothetic_scale_indifferent_iff
#print axioms Kreps.PreferenceProperties.HomogeneousUtility
#print axioms Kreps.PreferenceProperties.homogeneousUtility_iff_degree_one
#print axioms Kreps.PreferenceProperties.homogeneousUtility_origin
#print axioms Kreps.PreferenceProperties.homogeneous_represents_homothetic
#print axioms Kreps.PreferenceProperties.proposition_2_19_forward
#print axioms Kreps.PreferenceProperties.ratioSum_denominator_pos
#print axioms Kreps.PreferenceProperties.ratioSumUtility_low_le_one
#print axioms Kreps.PreferenceProperties.ratioSumUtility_nonneg
#print axioms Kreps.PreferenceProperties.RatioRankLinearForm
#print axioms Kreps.PreferenceProperties.ratioRankLinearForm_high
#print axioms Kreps.PreferenceProperties.ratioSumUtility_le_iff
#print axioms Kreps.PreferenceProperties.ratioSumUtility_lt_iff
#print axioms Kreps.PreferenceProperties.ratioSumUtility_boundary
#print axioms Kreps.PreferenceProperties.ratioRankLinearForm_self
#print axioms Kreps.PreferenceProperties.ratioRankLinearForm_mix
#print axioms Kreps.PreferenceProperties.ratioSumPreference_convex
#print axioms Kreps.PreferenceProperties.ratioSumPreference_semiStrict
#print axioms Kreps.PreferenceProperties.ratioRankLinearForm_continuous
#print axioms Kreps.PreferenceProperties.ratioSumPreference_continuous
#print axioms Kreps.PreferenceProperties.ratioSumUtility_continuous
#print axioms Kreps.PreferenceProperties.problem_2_8b
#print axioms Kreps.PreferenceProperties.RecursiveUtility
#print axioms Kreps.PreferenceProperties.recursiveUtility_at_sample
#print axioms Kreps.PreferenceProperties.recursiveUtility_represents
#print axioms Kreps.PreferenceProperties.recursiveUtility_mem_interval
#print axioms Kreps.PreferenceProperties.recursiveUtility_continuous
#print axioms Kreps.PreferenceProperties.recursiveUtility_sample_limit
#print axioms Kreps.PreferenceProperties.problem_2_14f
#print axioms Kreps.PreferenceProperties.recursiveUtility_limit_unique
#print axioms Kreps.PreferenceProperties.dense_sample_sequence
#print axioms Kreps.PreferenceProperties.SampleContainsPreferenceExtremes
#print axioms Kreps.PreferenceProperties.sampleContainsExtremes_of_preference
#print axioms Kreps.PreferenceProperties.problem_2_14g
#print axioms Kreps.PreferenceProperties.problem_2_14_recursive_completion
#print axioms Kreps.PreferenceProperties.nontrivialBlock_interior_rank_at
#print axioms Kreps.PreferenceProperties.exists_interior_reference
#print axioms Kreps.PreferenceProperties.baselineScores_reference_interior
#print axioms Kreps.PreferenceProperties.exists_interior_baseline_scores
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.globalize_target_of_calibration
#print axioms Kreps.PreferenceProperties.CompanionChartFamily.exists_global_target
#print axioms Kreps.PreferenceProperties.PartitionBlock
#print axioms Kreps.PreferenceProperties.PartitionGroup
#print axioms Kreps.PreferenceProperties.PartitionUngroup
#print axioms Kreps.PreferenceProperties.partitionUngroup_group
#print axioms Kreps.PreferenceProperties.partitionGroup_ungroup
#print axioms Kreps.PreferenceProperties.partitionGroup_continuous
#print axioms Kreps.PreferenceProperties.partitionUngroup_continuous
#print axioms Kreps.PreferenceProperties.partitionGroupingHomeomorph
#print axioms Kreps.PreferenceProperties.partitionBlock_preconnected
#print axioms Kreps.PreferenceProperties.partitionBlocks_separable
#print axioms Kreps.PreferenceProperties.exists_partition_assignment
#print axioms Kreps.PreferenceProperties.homothetic_iterate_above
#print axioms Kreps.PreferenceProperties.homothetic_iterate_below
#print axioms Kreps.PreferenceProperties.homothetic_contract_positive
#print axioms Kreps.PreferenceProperties.homothetic_contract_negative
#print axioms Kreps.PreferenceProperties.homothetic_origin_indifferent
#print axioms Kreps.PreferenceProperties.homothetic_positive_ray
#print axioms Kreps.PreferenceProperties.homothetic_negative_ray
#print axioms Kreps.PreferenceProperties.positive_ray_strictMono
#print axioms Kreps.PreferenceProperties.negative_ray_strictAnti
#print axioms Kreps.PreferenceProperties.positive_ray_cofinal
#print axioms Kreps.PreferenceProperties.negative_ray_coinitial
#print axioms Kreps.PreferenceProperties.positive_ray_indifference
#print axioms Kreps.PreferenceProperties.negative_ray_indifference
#print axioms Kreps.PreferenceProperties.MinimumUtility
#print axioms Kreps.PreferenceProperties.minimumUtility_le_component
#print axioms Kreps.PreferenceProperties.minimumUtility_exists_index
#print axioms Kreps.PreferenceProperties.minimumUtility_monotone
#print axioms Kreps.PreferenceProperties.minimumPreference_strictAllIncrease
#print axioms Kreps.PreferenceProperties.minimumPreference_not_strictlyMonotone
#print axioms Kreps.PreferenceProperties.minimumUtility_example
#print axioms Kreps.PreferenceProperties.CobbDouglasUtility
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_nonneg
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_pos
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_zero_coordinate
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_origin
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_monotone
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_strict_of_positive
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_strictMonoOn_positive
#print axioms Kreps.PreferenceProperties.cobbDouglasPreference_strictAllIncrease
#print axioms Kreps.PreferenceProperties.cobbDouglasPreference_not_strictlyMonotone
#print axioms Kreps.PreferenceProperties.cobbDouglasUtility_example
#print axioms Kreps.PreferenceProperties.WorstSamplePoint
#print axioms Kreps.PreferenceProperties.BestSamplePoint
#print axioms Kreps.PreferenceProperties.AugmentedPreferenceSample
#print axioms Kreps.PreferenceProperties.augmentedPreferenceSample_tail
#print axioms Kreps.PreferenceProperties.augmentedPreferenceSample_dense
#print axioms Kreps.PreferenceProperties.augmentedPreferenceSample_extremes
#print axioms Kreps.PreferenceProperties.augmentedPreferenceSample_brackets
#print axioms Kreps.PreferenceProperties.recursive_completion_of_dense_sample
#print axioms Kreps.PreferenceProperties.exists_dense_sample_with_extremes
#print axioms Kreps.PreferenceProperties.CodLiverMannaHealthBundle
#print axioms Kreps.PreferenceProperties.CodLiverMannaTasteBundle
#print axioms Kreps.PreferenceProperties.codLiverManna_health_scale_five
#print axioms Kreps.PreferenceProperties.codLiverManna_taste_scale_five
#print axioms Kreps.PreferenceProperties.codLiverManna_rank_reversal_not_homothetic
#print axioms Kreps.PreferenceProperties.CodLiverMannaUtility
#print axioms Kreps.PreferenceProperties.codLiverMannaUtility_continuous
#print axioms Kreps.PreferenceProperties.codLiverMannaUtility_values
#print axioms Kreps.PreferenceProperties.codLiverManna_example
#print axioms Kreps.PreferenceProperties.positive_ray_represents
#print axioms Kreps.PreferenceProperties.liftedUtility_homogeneous
#print axioms Kreps.PreferenceProperties.homogeneous_representation_above_origin
#print axioms Kreps.PreferenceProperties.reversePreference_rational
#print axioms Kreps.PreferenceProperties.reversePreference_continuous
#print axioms Kreps.PreferenceProperties.reversePreference_homothetic
#print axioms Kreps.PreferenceProperties.neg_utility_represents
#print axioms Kreps.PreferenceProperties.neg_utility_homogeneous
#print axioms Kreps.PreferenceProperties.homogeneous_representation_below_origin
#print axioms Kreps.PreferenceProperties.homogeneous_representation_indifferent
#print axioms Kreps.PreferenceProperties.sampleBrackets_of_dense_rank_range
#print axioms Kreps.PreferenceProperties.exists_sample_brackets
#print axioms Kreps.PreferenceProperties.exists_preference_bracketing_sequence
#print axioms Kreps.PreferenceProperties.SignedRay
#print axioms Kreps.PreferenceProperties.signedRay_nonneg
#print axioms Kreps.PreferenceProperties.signedRay_nonpos
#print axioms Kreps.PreferenceProperties.signedRay_zero
#print axioms Kreps.PreferenceProperties.signedRay_continuous
#print axioms Kreps.PreferenceProperties.signedRay_scale
#print axioms Kreps.PreferenceProperties.homothetic_signedRay_strict
#print axioms Kreps.PreferenceProperties.homothetic_signedRay_represents
#print axioms Kreps.PreferenceProperties.homothetic_signedRay_covers
#print axioms Kreps.PreferenceProperties.homogeneous_representation_both_sides
#print axioms Kreps.PreferenceProperties.proposition_2_19
#print axioms Kreps.PreferenceProperties.problem_2_12
#print axioms Kreps.PreferenceProperties.exists_bracketing_polygonal_curve
#print axioms Kreps.PreferenceProperties.ExtremeReferenceSegment
#print axioms Kreps.PreferenceProperties.extremeReferenceSegment_zero
#print axioms Kreps.PreferenceProperties.extremeReferenceSegment_one
#print axioms Kreps.PreferenceProperties.extremeReferenceSegment_continuous
#print axioms Kreps.PreferenceProperties.problem_2_14a_both_extrema
#print axioms Kreps.PreferenceProperties.extremeReferenceSegment_covers
#print axioms Kreps.PreferenceProperties.ExtremeReferenceSequence
#print axioms Kreps.PreferenceProperties.extremeReferenceSequence_curve_zero
#print axioms Kreps.PreferenceProperties.extremeReferenceSequence_curve_one
#print axioms Kreps.PreferenceProperties.extremeReferenceSequence_on_unit
#print axioms Kreps.PreferenceProperties.extremeReferenceSequence_range
#print axioms Kreps.PreferenceProperties.extremeReferenceSequence_brackets
#print axioms Kreps.PreferenceProperties.problem_2_14a
#print axioms Kreps.PreferenceProperties.problem_2_14b
#print axioms Kreps.PreferenceProperties.problem_2_14ab
#print axioms Kreps.PreferenceProperties.problem_2_14
#print axioms Kreps.PreferenceProperties.indifferent_iff_utility_eq
#print axioms Kreps.PreferenceProperties.homogeneous_unit_class_unique
#print axioms Kreps.PreferenceProperties.normalized_homogeneous_representation
#print axioms Kreps.PreferenceProperties.problem_2_13_homothetic
#print axioms Kreps.PreferenceProperties.strictlyMonotone_origin_class
#print axioms Kreps.PreferenceProperties.EveryRepresentation
#print axioms Kreps.PreferenceProperties.SomeRepresentation
#print axioms Kreps.PreferenceProperties.representation_quantifiers_of_invariance
#print axioms Kreps.PreferenceProperties.table_monotone
#print axioms Kreps.PreferenceProperties.table_strictlyMonotone
#print axioms Kreps.PreferenceProperties.table_quasiConcave
#print axioms Kreps.PreferenceProperties.table_semiStrictlyQuasiConcave
#print axioms Kreps.PreferenceProperties.table_strictlyQuasiConcave
#print axioms Kreps.PreferenceProperties.table_concave_converse
#print axioms Kreps.PreferenceProperties.table_strictlyConcave_converse
#print axioms Kreps.PreferenceProperties.table_continuous
#print axioms Kreps.PreferenceProperties.table_weaklySeparable
#print axioms Kreps.PreferenceProperties.AdditiveForm
#print axioms Kreps.PreferenceProperties.table_additive_converse
#print axioms Kreps.PreferenceProperties.some_additiveForm_iff
#print axioms Kreps.PreferenceProperties.QuasiLinearForm
#print axioms Kreps.PreferenceProperties.some_quasiLinearForm_iff
#print axioms Kreps.PreferenceProperties.table_quasiLinear
#print axioms Kreps.PreferenceProperties.table_homogeneous
#print axioms Kreps.PreferenceProperties.CurveGoods
#print axioms Kreps.PreferenceProperties.quasiLinear_class_iff
#print axioms Kreps.PreferenceProperties.curveGoods_iff_subutility_le
#print axioms Kreps.PreferenceProperties.quasiLinear_class_offset
#print axioms Kreps.PreferenceProperties.problem_2_13_quasiLinear_identified
#print axioms Kreps.PreferenceProperties.quasiLinear_identified_of_full_projection
#print axioms Kreps.PreferenceProperties.quasiLinear_outside_projection
#print axioms Kreps.PreferenceProperties.quasiLinearUtility_continuous
#print axioms Kreps.PreferenceProperties.quasiLinearUtility_strictMono
#print axioms Kreps.PreferenceProperties.TwoGoodLinearUtility
#print axioms Kreps.PreferenceProperties.twoGoodLinearUtility_mix
#print axioms Kreps.PreferenceProperties.twoGoodLinearUtility_concave
#print axioms Kreps.PreferenceProperties.twoGoodLinearUtility_continuous
#print axioms Kreps.PreferenceProperties.twoGoodLinearUtility_strictMono
#print axioms Kreps.PreferenceProperties.twoGoodLinearPreference_not_strictlyConvex
#print axioms Kreps.PreferenceProperties.twoGoodLinearUtility_homogeneous
#print axioms Kreps.PreferenceProperties.twoGoodLinear_indifference_curve
#print axioms Kreps.PreferenceProperties.problem_2_9a
#print axioms Kreps.PreferenceProperties.MeasureUtility
#print axioms Kreps.PreferenceProperties.measureUtility_mono
#print axioms Kreps.PreferenceProperties.measureUtility_strict
#print axioms Kreps.PreferenceProperties.measureUtility_represents
#print axioms Kreps.PreferenceProperties.measureUtility_eq_distribution
#print axioms Kreps.PreferenceProperties.measureUtility_upperSemicontinuous
#print axioms Kreps.PreferenceProperties.measureUtility_rank_atom
#print axioms Kreps.PreferenceProperties.measureUtility_continuousAt_of_null_class
#print axioms Kreps.PreferenceProperties.measureUtility_continuous_of_null_classes
#print axioms Kreps.PreferenceProperties.problem_2_15_openPos
#print axioms Kreps.PreferenceProperties.problem_2_15_continuity
#print axioms Kreps.PreferenceProperties.represents_add_constant
#print axioms Kreps.PreferenceProperties.represents_mul_positive
#print axioms Kreps.PreferenceProperties.table_concave_not_all
#print axioms Kreps.PreferenceProperties.table_convex_not_some_concave
#print axioms Kreps.PreferenceProperties.table_continuous_not_all
#print axioms Kreps.PreferenceProperties.doubled_quasiLinear_not_form
#print axioms Kreps.PreferenceProperties.table_quasiLinear_not_all
#print axioms Kreps.PreferenceProperties.shifted_homogeneous_not_homogeneous
#print axioms Kreps.PreferenceProperties.homogeneous_not_every_representation
#print axioms Kreps.PreferenceProperties.table_homogeneous_not_all
#print axioms Kreps.PreferenceProperties.ThreeCommodityTotal
#print axioms Kreps.PreferenceProperties.threeCommodityTotal_nonneg
#print axioms Kreps.PreferenceProperties.squared_threeCommodityTotal_represents
#print axioms Kreps.PreferenceProperties.squared_threeCommodityTotal_not_additive
#print axioms Kreps.PreferenceProperties.threeCommodityTotal_nontrivial
#print axioms Kreps.PreferenceProperties.threeCommodityTotal_threeNontrivial
#print axioms Kreps.PreferenceProperties.threeCommodityTotal_preference_properties
#print axioms Kreps.PreferenceProperties.table_additive_not_all
#print axioms Kreps.PreferenceProperties.threeFactor_first_utility_eq
#print axioms Kreps.PreferenceProperties.threeFactor_second_utility_eq
#print axioms Kreps.PreferenceProperties.threeFactor_third_utility_eq
#print axioms Kreps.PreferenceProperties.NormalizedThreeAxes
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_second_third
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_first_second
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_first_third
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_pair_symmetric
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_swap_first_two
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_first_base
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_merge_first
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_merge_last
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_pair_associative
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_pair_medial
#print axioms Kreps.PreferenceProperties.convexWarp_eq_max
#print axioms Kreps.PreferenceProperties.convexWarp_continuous
#print axioms Kreps.PreferenceProperties.LinearMoneyUtility
#print axioms Kreps.PreferenceProperties.WarpedMoneyUtility
#print axioms Kreps.PreferenceProperties.linear_warped_utilities_regular
#print axioms Kreps.PreferenceProperties.linear_warped_same_curve
#print axioms Kreps.PreferenceProperties.linear_curve_goods
#print axioms Kreps.PreferenceProperties.problem_2_13_quasiLinear_nonidentification
#print axioms Kreps.PreferenceProperties.LeontiefUtility
#print axioms Kreps.PreferenceProperties.leontiefUtility_monotone
#print axioms Kreps.PreferenceProperties.leontiefPreference_strictAllIncrease
#print axioms Kreps.PreferenceProperties.leontiefUtility_concave
#print axioms Kreps.PreferenceProperties.leontiefUtility_continuous
#print axioms Kreps.PreferenceProperties.leontiefUtility_first_axis
#print axioms Kreps.PreferenceProperties.leontiefPreference_not_strictlyMonotone
#print axioms Kreps.PreferenceProperties.leontiefPreference_not_strictlyConvex
#print axioms Kreps.PreferenceProperties.leontiefUtility_homogeneous
#print axioms Kreps.PreferenceProperties.leontief_indifference_curve
#print axioms Kreps.PreferenceProperties.problem_2_9b
#print axioms Kreps.PreferenceProperties.OrthantLebesgue
#print axioms Kreps.PreferenceProperties.orthantLebesgue_apply
#print axioms Kreps.PreferenceProperties.orthant_open_contains_ambient_ball
#print axioms Kreps.PreferenceProperties.orthantLebesgue_open_pos
#print axioms Kreps.PreferenceProperties.orthant_measure_openPos
#print axioms Kreps.PreferenceProperties.problem_2_15
#print axioms Kreps.PreferenceProperties.exists_pair_additive_scale_of_partialMedial
#print axioms Kreps.PreferenceProperties.normalized_threeFactor_partialMedial
#print axioms Kreps.PreferenceProperties.CommonThreeScoreUtility
#print axioms Kreps.PreferenceProperties.threeFactorIndependent_pullback
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_independent
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_continuous
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_first_strictMono
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_second_strictMono
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_third_strictMono
#print axioms Kreps.PreferenceProperties.commonThreeScoreUtility_axes
#print axioms Kreps.PreferenceProperties.measureUtility_add_dirac_self
#print axioms Kreps.PreferenceProperties.measureUtility_add_dirac_below
#print axioms Kreps.PreferenceProperties.measureUtility_add_dirac_not_continuousAt
#print axioms Kreps.PreferenceProperties.OneCommodityUtility
#print axioms Kreps.PreferenceProperties.OneCommodityUnit
#print axioms Kreps.PreferenceProperties.OneCommodityApproach
#print axioms Kreps.PreferenceProperties.oneCommodityUtility_properties
#print axioms Kreps.PreferenceProperties.oneCommodityApproach_tendsto
#print axioms Kreps.PreferenceProperties.oneCommodityApproach_strict
#print axioms Kreps.PreferenceProperties.orthant_comap_positive
#print axioms Kreps.PreferenceProperties.problem_2_15_not_continuous
#print axioms Kreps.PreferenceProperties.exists_common_baseline_score_interval
#print axioms Kreps.PreferenceProperties.scoreAggregator_commonThree_axes
#print axioms Kreps.PreferenceProperties.CoordinatePairUtility
#print axioms Kreps.PreferenceProperties.NormalizedCoordinateAxes
#print axioms Kreps.PreferenceProperties.stronglySeparable_common_update_utility_eq
#print axioms Kreps.PreferenceProperties.coordinatePairUtility_move_first
#print axioms Kreps.PreferenceProperties.coordinatePairUtility_move_second
#print axioms Kreps.PreferenceProperties.three_members_spare
#print axioms Kreps.PreferenceProperties.coordinatePairUtility_same
#print axioms Kreps.PreferenceProperties.piecewise_pair_updates
#print axioms Kreps.PreferenceProperties.coordinatePairUtility_context_iff
#print axioms Kreps.PreferenceProperties.coordinatePairUtility_all_comparisons
#print axioms Kreps.PreferenceProperties.exists_small_pair_interval
#print axioms Kreps.PreferenceProperties.normalizedThreeAxes_small_pair_interval
#print axioms Kreps.PreferenceProperties.additiveUtility_pair_eq_iff
#print axioms Kreps.PreferenceProperties.stronglySeparable_pair_comparison_iff
#print axioms Kreps.PreferenceProperties.stronglySeparable_pair_equality_iff
#print axioms Kreps.PreferenceProperties.represented_additive_pair_eq_iff
#print axioms Kreps.PreferenceProperties.HasLocalCommonPairScale
#print axioms Kreps.PreferenceProperties.normalizedThreeAxes_local_pair_scale
#print axioms Kreps.PreferenceProperties.exists_common_local_pair_scale
#print axioms Kreps.PreferenceProperties.represents_additive_of_reference_pair_comparisons
#print axioms Kreps.PreferenceProperties.exists_all_active_score_interval
#print axioms Kreps.PreferenceProperties.CommonActiveScoreEmbedding
#print axioms Kreps.PreferenceProperties.commonActiveScoreEmbedding_active
#print axioms Kreps.PreferenceProperties.commonActiveScoreEmbedding_inactive
#print axioms Kreps.PreferenceProperties.commonActiveScoreEmbedding_continuous
#print axioms Kreps.PreferenceProperties.commonActiveScoreEmbedding_axes
#print axioms Kreps.PreferenceProperties.HasAllPairsLocalScale
#print axioms Kreps.PreferenceProperties.exists_all_pairs_local_scale
#print axioms Kreps.PreferenceProperties.ordConnected_subtype_preconnected
#print axioms Kreps.PreferenceProperties.HasLocalScalarAdditiveChart
#print axioms Kreps.PreferenceProperties.exists_local_scalar_additive_chart
#print axioms Kreps.PreferenceProperties.baselineScores_interior_of_open_strictMono
#print axioms Kreps.PreferenceProperties.exists_local_scalar_additive_chart_of_open
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.mk
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.domain
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.coord
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.open_domain
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.interval
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.subset
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.continuous
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.increasing
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.represents
#print axioms Kreps.PreferenceProperties.localScalarChart_to_scalarAdditiveChart
#print axioms Kreps.PreferenceProperties.exists_scalarAdditiveChart_at_of_open
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.pair_compatible
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.mk
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.chart
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.center
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.seed_eq
#print axioms Kreps.PreferenceProperties.exists_coordinateChartFamily
#print axioms Kreps.PreferenceProperties.companionCoordinateIndex
#print axioms Kreps.PreferenceProperties.companionCoordinateIndex_injective
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.toCompanionFamily
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.companion_target_subset
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.companion_target_cover
#print axioms Kreps.PreferenceProperties.CoordinateChartFamily.companion_seed
#print axioms Kreps.PreferenceProperties.additiveUtility_pair_le_iff
#print axioms Kreps.PreferenceProperties.represented_additive_pair_le_iff
#print axioms Kreps.PreferenceProperties.ScalarAdditiveChart.pair_comparison_iff
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.mk
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.family
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.slope
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.positive
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.seed_unit
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.scale
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.continuous
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.increasing
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.seed_agrees
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.chart_agrees
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.companion_calibration
#print axioms Kreps.PreferenceProperties.exists_globalCoordinateScale
#print axioms Kreps.PreferenceProperties.GlobalCoordinateScale.align_chart
#print axioms Kreps.PreferenceProperties.common_companion_affine_slopes_equal
#print axioms Kreps.PreferenceProperties.globalCoordinateScale_local_pair_comparison
#print axioms Kreps.PreferenceProperties.globalCoordinateScale_pair_comparison
#print axioms Kreps.PreferenceProperties.exists_open_scalar_additive_representation
#print axioms Kreps.PreferenceProperties.exists_nondegenerate_scalar_additive
#print axioms Kreps.PreferenceProperties.exists_scalar_additive_of_three_nontrivial
#print axioms Kreps.PreferenceProperties.continuous_additive_of_continuous_represents
#print axioms Kreps.PreferenceProperties.proposition_2_14_exists
#print axioms Kreps.PreferenceProperties.table_additive
#print axioms Kreps.PreferenceProperties.table_continuous_additive
#print axioms Kreps.PreferenceProperties.PartitionPreference
#print axioms Kreps.PreferenceProperties.PartitionAdditiveUtility
#print axioms Kreps.PreferenceProperties.partitionPreference_rational
#print axioms Kreps.PreferenceProperties.partitionPreference_continuous
#print axioms Kreps.PreferenceProperties.partitionAdditiveUtility_continuous
#print axioms Kreps.PreferenceProperties.proposition_2_14_orthant
#print axioms Kreps.PreferenceProperties.proposition_2_14_orthant_additive
#print axioms Kreps.PreferenceProperties.proposition_2_14_orthant_iff
#print axioms Kreps.PreferenceProperties.FoodClothingBundle
#print axioms Kreps.PreferenceProperties.FoodWithClothing
#print axioms Kreps.PreferenceProperties.FirstFoodBundle
#print axioms Kreps.PreferenceProperties.SecondFoodBundle
#print axioms Kreps.PreferenceProperties.SkirtContext
#print axioms Kreps.PreferenceProperties.JeansContext
#print axioms Kreps.PreferenceProperties.replaceFoodBlock
#print axioms Kreps.PreferenceProperties.foodClothing_comparison_iff
#print axioms Kreps.PreferenceProperties.foodClothing_strict_iff
#print axioms Kreps.PreferenceProperties.foodClothing_printed_comparison
#print axioms Kreps.PreferenceProperties.foodClothing_printed_strict
#print axioms Kreps.PreferenceProperties.FoodClothingWitnessUtility
#print axioms Kreps.PreferenceProperties.foodClothingWitness_separable
#print axioms Kreps.PreferenceProperties.foodClothingWitness_initial_ranking
#print axioms Kreps.PreferenceProperties.foodClothingWitness_properties
#print axioms Kreps.PreferenceProperties.BeerWineBreadBundle
#print axioms Kreps.PreferenceProperties.BeerBreadOwner
#print axioms Kreps.PreferenceProperties.beerBreadOwner_selected
#print axioms Kreps.PreferenceProperties.beerBreadOwner_leftover
#print axioms Kreps.PreferenceProperties.beerWineBread_projection
#print axioms Kreps.PreferenceProperties.beerWineBread_leftover
#print axioms Kreps.PreferenceProperties.beerWineBread_reconstruction
#print axioms Kreps.PreferenceProperties.moneyTranslation_wealth_example
#print axioms Kreps.PreferenceProperties.quasiLinear_wealth_example
