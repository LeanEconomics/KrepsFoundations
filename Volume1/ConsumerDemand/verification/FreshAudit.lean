import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preference and consumption-domain prerequisites

Selected definitions and elementary results copied or adapted from Chapter 2,
commit `7d496c5`: `Basic`, `OrthantRepresentation`, `Monotonicity`,
`ConvexPreference`, and `ConcaveUtility`. Their economic conventions are unchanged.
Only the ingredients used by consumer demand are included in this independent
chapter package. The mathematical source is Kreps I, Chapters 1-2, pp. 1-44.
-/

namespace Kreps.ConsumerDemand

variable {X : Type*}

/-- Every pair of alternatives can be compared, including an alternative with itself. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- Weak preference is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- The book's standing rationality assumption: complete and transitive preference. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Alternatives at least as good as every feasible alternative. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Preference induced by utility, oriented with the preferred alternative first. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- A utility represents exactly the given weak preference. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Strict preference is weak preference without its reverse. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference is weak preference in both directions. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- Utility-induced preferences satisfy the chapter's rationality assumption. -/
theorem utilityPref_rational (u : X → ℝ) : Rational (UtilityPref u) :=
  ⟨fun x y => le_total (u y) (u x), fun _ _ _ hxy hyz => hyz.trans hxy⟩

/-- The consumption domain includes every boundary bundle and the origin. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- Local insatiability uses the book's closed-ball inequality. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- A convex combination as a point of its convex consumption domain. -/
def Mix (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- Internal convexity of a feasible menu agrees with closure under mixtures. -/
def ConvexMenu (hS : Convex ℝ S) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a, ∀ ha : a ∈ Set.Icc 0 1, Mix hS x y a ha ∈ A

/-- Mixtures are weakly better than the worse endpoint. -/
def ConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- Distinct endpoints give strictly better interior mixtures than the worse endpoint. -/
def StrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- Jensen's concavity inequality, on the actual consumption domain. -/
def ConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1,
    a * u x + (1 - a) * u y ≤ u (Mix hS x y a ha)

/-- The mixture's utility is at least the lesser endpoint utility. -/
def QuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, min (u x) (u y) ≤ u (Mix hS x y a ha)

/-- Distinct endpoints give a strict utility improvement over the worse one. -/
def StrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Budget sets at positive prices

Kreps I, Section 3.1 and the budget-set arguments in Proposition 3.1, pp. 50-54.
Income is nonnegative and every commodity price is strictly positive. Feasibility
uses weak inequalities, so zero consumption and spending exactly the available
income are included. Nonemptiness, coordinate bounds, closedness and convexity
are established before optimizing any utility.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- The strictly positive finite-dimensional price vectors of Section 3.1. -/
abbrev PositivePrices (k : ℕ) := {p : Fin k → ℝ // ∀ j, 0 < p j}

/-- The zero consumption bundle, feasible at every nonnegative income. -/
def ZeroBundle (k : ℕ) : NonnegativeOrthant k := ⟨0, le_rfl⟩

/-- Expenditure at constant unit prices, the finite scalar product `p · x`. -/
def Expenditure {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) : ℝ :=
  ∑ j, p.val j * x.val j

/-- The budget-feasible bundles at a strictly positive price vector and nonnegative income. -/
def BudgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  {x | Expenditure p x ≤ (y : ℝ)}

/-- The zero bundle costs nothing. -/
theorem expenditure_zero {k : ℕ} (p : PositivePrices k) :
    Expenditure p (ZeroBundle k) = 0 := by simp [Expenditure, ZeroBundle]

/-- Every feasible consumption expenditure is nonnegative. -/
theorem expenditure_nonneg {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) :
    0 ≤ Expenditure p x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (x.property j))

/-- Every nonnegative-income budget set is nonempty. -/
theorem budgetSet_nonempty {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    (BudgetSet p y).Nonempty := by
  refine ⟨ZeroBundle k, ?_⟩
  change Expenditure p (ZeroBundle k) ≤ (y : ℝ)
  rw [expenditure_zero]
  exact y.property

/-- Spending on one good cannot exceed the total nonnegative expenditure. -/
theorem commodity_expenditure_le {k : ℕ} (p : PositivePrices k)
    (x : NonnegativeOrthant k) (j : Fin k) : p.val j * x.val j ≤ Expenditure p x :=
  Finset.single_le_sum (fun i _ => mul_nonneg (p.property i).le (x.property i))
    (Finset.mem_univ j)

/-- Each budget-feasible coordinate is bounded by income divided by its price. -/
theorem budgetSet_coordinate_bound {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ BudgetSet p y) (j : Fin k) :
    x.val j ≤ (y : ℝ) / p.val j := by
  apply (le_div_iff₀ (p.property j)).mpr
  simpa only [mul_comm] using (commodity_expenditure_le p x j).trans hx

/-- At zero income the zero bundle is the only feasible consumption. -/
theorem budgetSet_zero {k : ℕ} (p : PositivePrices k) :
    BudgetSet p 0 = {ZeroBundle k} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext j
    apply le_antisymm
    · change x.val j ≤ 0
      simpa only [NNReal.coe_zero, zero_div] using budgetSet_coordinate_bound p 0 hx j
    · exact x.property j
  · rintro rfl
    change Expenditure p (ZeroBundle k) ≤ 0
    exact (expenditure_zero p).le

/-- Expenditure is continuous in the consumption bundle. -/
theorem expenditure_continuous {k : ℕ} (p : PositivePrices k) : Continuous (Expenditure p) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- Feasibility is a closed condition inside the nonnegative orthant. -/
theorem budgetSet_isClosed {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsClosed (BudgetSet p y) := isClosed_le (expenditure_continuous p) continuous_const

/-- Positive prices put the closed budget set inside a compact coordinate box. -/
theorem budgetSet_isCompact {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsCompact (BudgetSet p y) := by
  let b : Fin k → ℝ := fun j => (y : ℝ) / p.val j
  have hbox : IsCompact ((Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹'
      Set.Icc 0 b) :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  apply hbox.of_isClosed_subset (budgetSet_isClosed p y)
  intro x hx
  exact ⟨x.property, fun j => budgetSet_coordinate_bound p y hx j⟩

/-- Expenditure of a mixture is the corresponding mixture of expenditures. -/
theorem expenditure_mix {k : ℕ} (p : PositivePrices k) (x z : NonnegativeOrthant k)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) =
      a * Expenditure p x + (1 - a) * Expenditure p z := by
  change (∑ j, p.val j * (a * x.val j + (1 - a) * z.val j)) = _
  calc
    _ = ∑ j, (a * (p.val j * x.val j) + (1 - a) * (p.val j * z.val j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- Budget sets are convex, without any assumption on the consumer's utility. -/
theorem budgetSet_convex {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (BudgetSet p y) := by
  intro x hx z hz a ha
  have he := expenditure_mix p x z a ha
  change Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) ≤ (y : ℝ)
  rw [he]
  have hx' := mul_le_mul_of_nonneg_left hx ha.1
  have hz' := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ha.2)
  linarith

/-- Multiply every commodity price by the same strictly positive factor. -/
def ScalePrices {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) : PositivePrices k :=
  ⟨fun j => a * p.val j, fun j => mul_pos ha (p.property j)⟩

/-- Scaling all unit prices scales expenditure by the same factor. -/
theorem expenditure_scalePrices {k : ℕ} (a : ℝ) (ha : 0 < a)
    (p : PositivePrices k) (x : NonnegativeOrthant k) :
    Expenditure (ScalePrices a ha p) x = a * Expenditure p x := by
  simp only [Expenditure, ScalePrices, mul_assoc, Finset.mul_sum]

/-- Simultaneous positive scaling of prices and income leaves the entire budget set unchanged. -/
theorem budgetSet_scale {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    BudgetSet (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = BudgetSet p y := by
  ext x
  change Expenditure (ScalePrices a ha p) x ≤ a * (y : ℝ) ↔ _
  rw [expenditure_scalePrices, mul_le_mul_iff_right₀ ha]
  rfl

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Boundary-compatible first-order conditions

Kreps I, Chapter 3, pp. 57-62, and Appendix 5, pp. 479-484.
Derivatives within the consumption domain retain the one-sided boundary convention.
These preliminary directional lemmas do not yet assert the multiplier theorem.
-/

namespace Kreps.ConsumerDemand

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every feasible segment from a maximum has nonpositive first-order utility change. -/
theorem feasible_segment_derivative_nonpos {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x y : E} (hmax : IsMaxOn u feasible x)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hsegment : segment ℝ x y ⊆ feasible) : D (y - x) ≤ 0 :=
  hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hd.mono hsub)
    (sub_mem_posTangentConeAt_of_segment_subset hsegment)

/-- On a convex feasible region every feasible point gives a first-order inequality. -/
theorem convex_firstOrderNecessary {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x : E} (hmax : IsMaxOn u feasible x)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hc : Convex ℝ feasible) (hx : x ∈ feasible) :
    ∀ y ∈ feasible, D (y - x) ≤ 0 := by
  intro y hy
  exact feasible_segment_derivative_nonpos hmax hd hsub (hc.segment_subset hx hy)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Multipliers for a linear budget

Kreps I, Proposition 3.5a, pp. 57-58. The first-order directional condition reduces
necessity to this finite-dimensional linear problem. Positive income is essential
to the explicit multiplier construction; zero income is handled separately by the
singleton budget result.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators

/-- A maximizer of a linear functional on a positive-price budget has nonnegative
budget and commodity multipliers, including complementary slackness. -/
theorem linear_budget_multipliers {k : ℕ} (p m x : Fin k → ℝ) (y : ℝ)
    (hp : ∀ i, 0 < p i) (hy : 0 < y) (hx : ∀ i, 0 ≤ x i)
    (hbudget : ∑ i, p i * x i ≤ y)
    (hmax : ∀ z : Fin k → ℝ, (∀ i, 0 ≤ z i) → (∑ i, p i * z i ≤ y) →
      ∑ i, m i * z i ≤ ∑ i, m i * x i) :
    ∃ l : ℝ, 0 ≤ l ∧ (∀ i, m i ≤ l * p i) ∧
      (∀ i, (l * p i - m i) * x i = 0) ∧ l * (y - ∑ i, p i * x i) = 0 := by
  classical
  let v := ∑ i, m i * x i
  have hv : 0 ≤ v := by
    simpa [v] using hmax (fun _ => 0) (fun _ => le_rfl) (by simpa using hy.le)
  let l := v / y
  have hl : 0 ≤ l := div_nonneg hv hy.le
  have hly : l * y = v := div_mul_cancel₀ v (ne_of_gt hy)
  have hcoeff (i : Fin k) : m i ≤ l * p i := by
    have hvertex := hmax (Pi.single i (y / p i))
      (fun j => by by_cases h : j = i <;> simp [h, div_nonneg hy.le (hp i).le])
      (by simp [Pi.single_apply, mul_div_cancel₀ _ (ne_of_gt (hp i))])
    have hratio : m i * (y / p i) ≤ v := by
      simpa [Pi.single_apply, v] using hvertex
    have h := (div_le_iff₀ (hp i)).mp (show m i * y / p i ≤ v by
      simpa [mul_div_assoc] using hratio)
    nlinarith [hp i]
  have hsum : v ≤ l * ∑ i, p i * x i := by
    calc
      v ≤ ∑ i, (l * p i) * x i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcoeff i) (hx i))
      _ = l * ∑ i, p i * x i := by simp [Finset.mul_sum, mul_assoc]
  have hslack : l * (y - ∑ i, p i * x i) = 0 := by nlinarith
  have hgap : ∑ i, (l * p i - m i) * x i = 0 := by
    rw [show (∑ i, (l * p i - m i) * x i) =
        l * (∑ i, p i * x i) - v by
      simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, v]]
    nlinarith
  refine ⟨l, hl, hcoeff, ?_, hslack⟩
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (sub_nonneg.mpr (hcoeff i)) (hx i))).mp hgap i (Finset.mem_univ i)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concave supporting inequalities within the consumption domain

Kreps I, Proposition 3.5(b), p. 57, and the proof of Proposition A5.4, p. 484.
A derivative within a convex domain bounds every secant of a concave function.
The proof restricts to the segment from the candidate to the comparison point and
uses Mathlib's one-dimensional right-hand derivative bound. No open neighborhood
of the candidate is assumed, so the result includes boundary consumption bundles.
-/

namespace Kreps.ConsumerDemand

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A concave function lies below its supporting derivative, including at domain boundaries. -/
theorem concave_support_le {u : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {x y : E}
    (hu : ConcaveOn ℝ S u) (hd : HasFDerivWithinAt u D S x)
    (hx : x ∈ S) (hy : y ∈ S) : u y - u x ≤ D (y - x) := by
  have hmap : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) S :=
    hu.1.mapsTo_lineMap hx hy
  have hline : ConcaveOn ℝ (Icc (0 : ℝ) 1) (u ∘ AffineMap.lineMap x y) :=
    (hu.comp_affineMap (AffineMap.lineMap x y)).subset hmap (convex_Icc 0 1)
  have hdline : HasDerivWithinAt (u ∘ AffineMap.lineMap x y) (D (y - x))
      (Icc (0 : ℝ) 1) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivWithinAt_lineMap hmap (by simp)
  have hbound := hline.slope_le_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_lt_one hdline
  simpa [slope_def_field] using hbound

/-- The equivalent tangent upper bound used in the proof of Proposition A5.4. -/
theorem concave_support_upper {u : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {x y : E}
    (hu : ConcaveOn ℝ S u) (hd : HasFDerivWithinAt u D S x)
    (hx : x ∈ S) (hy : y ∈ S) : u y ≤ u x + D (y - x) := by
  have h := concave_support_le hu hd hx hy
  linarith

/-- Nonpositive first-order changes toward every feasible point suffice for a concave maximum. -/
theorem concave_firstOrderSufficient {u : E → ℝ} {D : E →L[ℝ] ℝ}
    {domain feasible : Set E} {x : E} (hu : ConcaveOn ℝ domain u)
    (hd : HasFDerivWithinAt u D domain x) (hsub : feasible ⊆ domain)
    (hx : x ∈ feasible) (hfirst : ∀ y ∈ feasible, D (y - x) ≤ 0) :
    IsMaxOn u feasible x := by
  intro y hy
  have h := concave_support_le hu hd (hsub hx) (hsub hy)
  have hzero := hfirst y hy
  change u y ≤ u x
  exact sub_nonpos.mp (h.trans hzero)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Calculus conditions for the consumer's problem

Kreps I, Definition 3.4 and Proposition 3.5, pp. 57-62. The derivative is taken
within the nonnegative orthant. Its values on the coordinate directions are the
right-hand marginal utilities, including at boundary bundles. Values of the
utility outside the orthant play no role and need not form a smooth extension.

Necessity reduces the derivative's first-order inequalities to a finite linear
budget problem. Sufficiency uses the concave supporting inequality. The compact
conditions are also equivalent to the full nonnegative-multiplier conditions.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal BigOperators

/-- The derivative's marginal value in the direction of one additional unit of good `j`. -/
def MarginalUtility {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ) (j : Fin k) : ℝ :=
  D (Pi.single j 1)

/-- **Definition 3.4:** feasibility, marginal inequalities, and complementary slackness. -/
def CombinedOptimality {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) (m : Fin k → ℝ) : Prop :=
  x ∈ BudgetSet p y ∧ ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j ≤ l * p.val j) ∧
    (∀ j, 0 < x.val j → m j = l * p.val j) ∧
    (Expenditure p x < (y : ℝ) → l = 0)

/-- The book's optimality conditions evaluated at the actual within-domain derivative. -/
def OptimalityConditions {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) (D : (Fin k → ℝ) →L[ℝ] ℝ) : Prop :=
  CombinedOptimality p y x (MarginalUtility D)

/-- The same budget region expressed in the ambient vector space for within-domain calculus. -/
def BudgetVectors {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) : Set (Fin k → ℝ) :=
  {z | 0 ≤ z ∧ ∑ j, p.val j * z j ≤ (y : ℝ)}

/-- A subtype bundle is feasible exactly when its coordinate vector is in the ambient budget. -/
theorem mem_budgetVectors_val {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (x : NonnegativeOrthant k) : x.val ∈ BudgetVectors p y ↔ x ∈ BudgetSet p y := by
  exact ⟨And.right, fun hx => ⟨x.property, hx⟩⟩

/-- Ambient budget vectors form a convex set, including its nonnegative boundary. -/
theorem budgetVectors_convex {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    Convex ℝ (BudgetVectors p y) := by
  intro x hx z hz a b ha hb hab
  refine ⟨(convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) hx.1 hz.1 ha hb hab, ?_⟩
  change (∑ j, p.val j * (a * x j + b * z j)) ≤ (y : ℝ)
  have he : (∑ j, p.val j * (a * x j + b * z j)) =
      a * (∑ j, p.val j * x j) + b * (∑ j, p.val j * z j) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he]
  have hxa := mul_le_mul_of_nonneg_left hx.2 ha
  have hzb := mul_le_mul_of_nonneg_left hz.2 hb
  nlinarith

/-- A linear derivative is the scalar product of its coordinate marginals with the direction. -/
theorem derivative_coordinate_expansion {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ)
    (z : Fin k → ℝ) : D z = ∑ j, MarginalUtility D j * z j := by
  classical
  have hz : z = ∑ j, z j • (Pi.single j 1 : Fin k → ℝ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    D z = D (∑ j, z j • (Pi.single j 1 : Fin k → ℝ)) := congrArg D hz
    _ = ∑ j, MarginalUtility D j * z j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [MarginalUtility, map_smul, mul_comm]

/-- Within-orthant derivatives give the actual right-hand coordinate marginal at every bundle. -/
theorem marginalUtility_right_derivative {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} {x : NonnegativeOrthant k}
    (hd : HasFDerivWithinAt u D (Ici 0) x.val) (j : Fin k) :
    HasDerivWithinAt (fun t : ℝ => u (x.val + t • Pi.single j 1))
      (MarginalUtility D j) (Ici 0) 0 := by
  have hp : HasDerivAt (fun t : ℝ => x.val + t • (Pi.single j 1 : Fin k → ℝ))
      (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single j 1 : Fin k → ℝ)).const_add x.val
  have hm : MapsTo (fun t : ℝ => x.val + t • (Pi.single j 1 : Fin k → ℝ))
      (Ici 0) (Ici 0) := by
    intro t ht i
    apply add_nonneg (x.property i)
    change 0 ≤ t * (Pi.single j 1 : Fin k → ℝ) i
    apply mul_nonneg ht
    by_cases hij : i = j <;> simp [hij]
  exact hd.comp_hasDerivWithinAt_of_eq 0 hp.hasDerivWithinAt hm (by simp)

/-- The compact conditions are equivalent to vanishing multiplier-slack products. -/
theorem combinedOptimality_iff_complementarity {k : ℕ} (p : PositivePrices k)
    (y : ℝ≥0) (x : NonnegativeOrthant k) (m : Fin k → ℝ) :
    CombinedOptimality p y x m ↔
      x ∈ BudgetSet p y ∧ ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j ≤ l * p.val j) ∧
        (∀ j, (l * p.val j - m j) * x.val j = 0) ∧
        l * ((y : ℝ) - Expenditure p x) = 0 := by
  constructor
  · rintro ⟨hx, l, hl, hm, heq, hslack⟩
    refine ⟨hx, l, hl, hm, ?_, ?_⟩
    · intro j
      by_cases hj : x.val j = 0
      · simp [hj]
      · rw [heq j (lt_of_le_of_ne (x.property j) (Ne.symm hj)), sub_self, zero_mul]
    · by_cases hs : Expenditure p x < (y : ℝ)
      · rw [hslack hs, zero_mul]
      · have he : Expenditure p x = (y : ℝ) := le_antisymm hx (le_of_not_gt hs)
        rw [he, sub_self, mul_zero]
  · rintro ⟨hx, l, hl, hm, heq, hslack⟩
    refine ⟨hx, l, hl, hm, ?_, ?_⟩
    · intro j hj
      have he := (mul_eq_zero.mp (heq j)).resolve_right (ne_of_gt hj)
      exact (sub_eq_zero.mp he).symm
    · intro hs
      exact (mul_eq_zero.mp hslack).resolve_right (ne_of_gt (sub_pos.mpr hs))

/-- The full Lagrangian conditions use nonnegative budget and commodity multipliers. -/
theorem combinedOptimality_iff_lagrangian {k : ℕ} (p : PositivePrices k)
    (y : ℝ≥0) (x : NonnegativeOrthant k) (m : Fin k → ℝ) :
    CombinedOptimality p y x m ↔
      x ∈ BudgetSet p y ∧ ∃ (l : ℝ) (μ : Fin k → ℝ), 0 ≤ l ∧
        (∀ j, 0 ≤ μ j) ∧ (∀ j, m j - l * p.val j + μ j = 0) ∧
        (∀ j, μ j * x.val j = 0) ∧ l * ((y : ℝ) - Expenditure p x) = 0 := by
  rw [combinedOptimality_iff_complementarity]
  constructor
  · rintro ⟨hx, l, hl, hm, hg, hs⟩
    exact ⟨hx, l, fun j => l * p.val j - m j, hl,
      fun j => sub_nonneg.mpr (hm j), fun j => by ring, hg, hs⟩
  · rintro ⟨hx, l, μ, hl, hμ, hm, hg, hs⟩
    have he (j) : μ j = l * p.val j - m j := by linarith [hm j]
    refine ⟨hx, l, hl, ?_, ?_, hs⟩
    · intro j
      linarith [hμ j, hm j]
    · intro j
      rw [← he j]
      exact hg j

/-- **Proposition 3.5(a):** every positive-income optimum satisfies the calculus conditions. -/
theorem proposition_3_5a {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) {x : NonnegativeOrthant k}
    (hd : HasFDerivWithinAt u D (Ici 0) x.val)
    (hx : x ∈ MarshallianDemand (fun z => u z.val) p y) :
    OptimalityConditions p y x D := by
  have hmax : IsMaxOn u (BudgetVectors p y) x.val := by
    intro z hz
    exact hx.2 ⟨z, hz.1⟩ hz.2
  have hfirst := convex_firstOrderNecessary hmax hd (fun _ hz => hz.1)
    (budgetVectors_convex p y) ((mem_budgetVectors_val p y x).mpr hx.1)
  have hlinear : ∀ z : Fin k → ℝ, (∀ j, 0 ≤ z j) →
      (∑ j, p.val j * z j ≤ (y : ℝ)) →
      (∑ j, MarginalUtility D j * z j) ≤ ∑ j, MarginalUtility D j * x.val j := by
    intro z hz hb
    have he := hfirst z ⟨hz, hb⟩
    rw [map_sub, derivative_coordinate_expansion, derivative_coordinate_expansion] at he
    exact sub_nonpos.mp he
  apply (combinedOptimality_iff_complementarity p y x (MarginalUtility D)).mpr
  exact ⟨hx.1, linear_budget_multipliers p.val (MarginalUtility D) x.val (y : ℝ)
    p.property hy x.property hx.1 hlinear⟩

/-- The optimality conditions make the derivative largest at the candidate over its budget. -/
theorem optimalityConditions_firstOrder {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {D : (Fin k → ℝ) →L[ℝ] ℝ}
    (ho : OptimalityConditions p y x D) :
    ∀ z ∈ BudgetVectors p y, D (z - x.val) ≤ 0 := by
  obtain ⟨_, l, hl, hm, hg, hs⟩ :=
    (combinedOptimality_iff_complementarity p y x (MarginalUtility D)).mp ho
  have hprod (j) : MarginalUtility D j * x.val j = (l * p.val j) * x.val j := by
    have h := hg j
    nlinarith
  have hxsum : (∑ j, MarginalUtility D j * x.val j) = l * (y : ℝ) := by
    calc
      (∑ j, MarginalUtility D j * x.val j) = l * Expenditure p x := by
        simp_rw [hprod]
        simp [Expenditure, Finset.mul_sum, mul_assoc]
      _ = l * (y : ℝ) := by nlinarith
  intro z hz
  rw [map_sub, derivative_coordinate_expansion, derivative_coordinate_expansion, hxsum]
  apply sub_nonpos.mpr
  calc
    (∑ j, MarginalUtility D j * z j) ≤ ∑ j, (l * p.val j) * z j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (hz.1 j))
    _ = l * (∑ j, p.val j * z j) := by simp [Finset.mul_sum, mul_assoc]
    _ ≤ l * (y : ℝ) := mul_le_mul_of_nonneg_left hz.2 hl

/-- **Proposition 3.5(b):** the calculus conditions suffice for a concave utility maximum. -/
theorem proposition_3_5b {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} (hu : ConcaveOn ℝ (Ici 0) u)
    (hd : HasFDerivWithinAt u D (Ici 0) x.val) (ho : OptimalityConditions p y x D) :
    x ∈ MarshallianDemand (fun z => u z.val) p y := by
  have hmax := concave_firstOrderSufficient hu hd (fun _ hz => hz.1)
    ((mem_budgetVectors_val p y x).mpr ho.1) (optimalityConditions_firstOrder ho)
  refine ⟨ho.1, ?_⟩
  intro z hz
  exact hmax ((mem_budgetVectors_val p y z).mpr hz)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strict logarithmic supporting inequalities

Kreps I, Problems 3.3-3.5, p. 64. Logarithmic utility is compared only where
every logarithm has a strictly positive argument. This avoids treating Lean's
total-function value `Real.log 0` as an economic utility at zero consumption.
Positive shifts make the results applicable to the full nonnegative orthant.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Weighted logarithmic utility, interpreted economically only at positive arguments. -/
noncomputable def ShiftedLogUtility {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∑ j, a j * Real.log (x.val j + γ j)

/-- The marginal coefficients at a bundle where all logarithm arguments are positive. -/
noncomputable def LogMarginals {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) : ℝ := a j / (x.val j + γ j)

/-- The scalar logarithm lies below its tangent on the positive half-line. -/
theorem log_sub_log_le_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log z - Real.log x ≤ (z - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz hx)
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

/-- At different positive points, the logarithmic supporting inequality is strict. -/
theorem log_sub_log_lt_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (hne : z ≠ x) :
    Real.log z - Real.log x < (z - x) / x := by
  have hne' : z / x ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq (ne_of_gt hx)).mp h)
  have h := Real.log_lt_sub_one_of_pos (div_pos hz hx) hne'
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

/-- Positive weights give a strict supporting inequality whenever the bundles differ. -/
theorem shiftedLog_strict_support {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (x z : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j)
    (hz : ∀ j, 0 < z.val j + γ j) (hne : z ≠ x) :
    ShiftedLogUtility a γ z - ShiftedLogUtility a γ x <
      ∑ j, LogMarginals a γ x j * (z.val j - x.val j) := by
  have hex : ∃ j, z.val j ≠ x.val j := by
    by_contra! h
    exact hne (Subtype.ext (funext h))
  obtain ⟨j, hj⟩ := hex
  rw [ShiftedLogUtility, ShiftedLogUtility, ← Finset.sum_sub_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    have h := mul_le_mul_of_nonneg_left (log_sub_log_le_tangent (hx i) (hz i)) (ha i).le
    dsimp only [LogMarginals]
    convert h using 1 <;> ring
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    have hneq : z.val j + γ j ≠ x.val j + γ j := fun h => hj (add_right_cancel h)
    have h := mul_lt_mul_of_pos_left (log_sub_log_lt_tangent (hx j) (hz j) hneq) (ha j)
    dsimp only [LogMarginals]
    convert h using 1 <;> ring

/-- Combined optimality bounds the corresponding linear marginal objective over the budget. -/
theorem combinedOptimality_linear_bound {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y) :
    (∑ j, m j * (z.val j - x.val j)) ≤ 0 := by
  obtain ⟨_, l, hl, hm, hg, hs⟩ :=
    (combinedOptimality_iff_complementarity p y x m).mp ho
  have hprod (j) : m j * x.val j = (l * p.val j) * x.val j := by
    have h := hg j
    nlinarith
  have hsum : (∑ j, m j * x.val j) = l * Expenditure p x := by
    simp_rw [hprod]
    simp [Expenditure, Finset.mul_sum, mul_assoc]
  have hzsum : (∑ j, m j * z.val j) ≤ l * Expenditure p z := by
    calc
      _ ≤ ∑ j, (l * p.val j) * z.val j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (z.property j))
      _ = _ := by simp [Expenditure, Finset.mul_sum, mul_assoc]
  have hbudget : l * Expenditure p z ≤ l * (y : ℝ) :=
    mul_le_mul_of_nonneg_left hz hl
  simp only [mul_sub, Finset.sum_sub_distrib, hsum]
  nlinarith

/-- The logarithmic conditions imply strict optimality among positive-argument feasible bundles. -/
theorem shiftedLog_strict_optimality {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hzpos : ∀ j, 0 < z.val j + γ j) (hne : z ≠ x) :
    ShiftedLogUtility a γ z < ShiftedLogUtility a γ x := by
  have hstrict := shiftedLog_strict_support a γ ha x z hx hzpos hne
  have hlinear := combinedOptimality_linear_bound ho hz
  linarith

/-- With strictly positive shifts, the logarithmic conditions give the full singleton demand. -/
theorem shiftedLog_demand_of_positive_shifts {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 < γ j) {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} (ho : CombinedOptimality p y x (LogMarginals a γ x)) :
    MarshallianDemand (ShiftedLogUtility a γ) p y = {x} := by
  have hpos (z : NonnegativeOrthant k) (j) : 0 < z.val j + γ j :=
    add_pos_of_nonneg_of_pos (z.property j) (hγ j)
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (not_lt_of_ge (hz.2 x ho.1))
      (shiftedLog_strict_optimality a γ ha (hpos x) ho hz.1 (hpos z) hne)
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨ho.1, fun w hw => ?_⟩
    change ShiftedLogUtility a γ w ≤ ShiftedLogUtility a γ x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedLog_strict_optimality a γ ha (hpos x) ho hw (hpos w) he).le

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Shifted Cobb-Douglas utility, including zero boundary factors

Kreps I, pp. 59-60 and Problems 3.3 and 3.5, p. 64. Positive exponents make
the product zero if any shifted consumption is zero. Elsewhere, its logarithm
is exactly the weighted sum of logarithms. Consequently the logarithmic
conditions characterize a unique product-utility optimum on the full orthant,
without asserting concavity of the original unnormalized product.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The shifted Cobb-Douglas product with real exponents. -/
noncomputable def ShiftedCobbDouglas {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∏ j, (x.val j + γ j) ^ a j

/-- Positive shifted quantities make the product strictly positive. -/
theorem shiftedCobbDouglas_pos {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j) :
    0 < ShiftedCobbDouglas a γ x :=
  Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) (a j))

/-- A zero shifted quantity makes the product zero when its exponent is positive. -/
theorem shiftedCobbDouglas_eq_zero {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) (ha : 0 < a j)
    (hx : x.val j + γ j = 0) : ShiftedCobbDouglas a γ x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hx, Real.zero_rpow (ne_of_gt ha)]

/-- On the positive-argument region, logarithms give the weighted-log utility exactly. -/
theorem log_shiftedCobbDouglas {k : ℕ} (a γ : Fin k → ℝ)
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j + γ j) :
    Real.log (ShiftedCobbDouglas a γ x) = ShiftedLogUtility a γ x := by
  rw [ShiftedCobbDouglas, Real.log_prod
    (fun j _ => ne_of_gt (Real.rpow_pos_of_pos (hx j) (a j)))]
  exact Finset.sum_congr rfl (fun j _ => Real.log_rpow (hx j) (a j))

/-- Logarithmic optimality yields strict product-utility optimality, including boundary rivals. -/
theorem shiftedCobbDouglas_strict_optimality {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y) (hne : z ≠ x) :
    ShiftedCobbDouglas a γ z < ShiftedCobbDouglas a γ x := by
  by_cases hpos : ∀ j, 0 < z.val j + γ j
  · apply (Real.log_lt_log_iff (shiftedCobbDouglas_pos a γ z hpos)
      (shiftedCobbDouglas_pos a γ x hx)).mp
    rw [log_shiftedCobbDouglas a γ z hpos, log_shiftedCobbDouglas a γ x hx]
    exact shiftedLog_strict_optimality a γ ha hx ho hz hpos hne
  · push Not at hpos
    obtain ⟨j, hj⟩ := hpos
    have hzero : z.val j + γ j = 0 := le_antisymm hj (add_nonneg (z.property j) (hγ j))
    rw [shiftedCobbDouglas_eq_zero a γ z j (ha j) hzero]
    exact shiftedCobbDouglas_pos a γ x hx

/-- The positive-argument candidate is the unique full-domain product-utility optimum. -/
theorem shiftedCobbDouglas_demand_of_optimality {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j)
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j + γ j)
    (ho : CombinedOptimality p y x (LogMarginals a γ x)) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y = {x} := by
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (not_lt_of_ge (hz.2 x ho.1))
      (shiftedCobbDouglas_strict_optimality a γ ha hγ hx ho hz.1 hne)
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨ho.1, fun w hw => ?_⟩
    change ShiftedCobbDouglas a γ w ≤ ShiftedCobbDouglas a γ x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedCobbDouglas_strict_optimality a γ ha hγ hx ho hw he).le

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Full-domain Cobb-Douglas demand

Kreps I, pp. 59-60. Each good receives its exponent's share of total expenditure.
The proof uses the strictly increasing logarithmic transformation only where
all coordinates are positive and treats zero boundary factors separately.
There is no normalization assumption on the sum of exponents and no finite
derivative assumption at the boundary. Zero income is included explicitly.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The ordinary, unshifted Cobb-Douglas utility on the full nonnegative orthant. -/
noncomputable def CobbDouglas {k : ℕ} (a : Fin k → ℝ) : NonnegativeOrthant k → ℝ :=
  ShiftedCobbDouglas a 0

/-- Positive powers make Cobb-Douglas continuous even at zero coordinates. -/
theorem cobbDouglas_continuous {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    Continuous (CobbDouglas a) := by
  unfold CobbDouglas ShiftedCobbDouglas
  apply continuous_finsetProd
  intro j _
  exact (Real.continuous_rpow_const (ha j).le).comp
    (((continuous_apply j).comp continuous_subtype_val).add continuous_const)

/-- The total exponent is strictly positive in a nonempty commodity space. -/
theorem exponent_sum_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    0 < ∑ j, a j := Finset.sum_pos (fun j _ => ha j) Finset.univ_nonempty

/-- The Cobb-Douglas expenditure-share formula. -/
noncomputable def CobbDouglasBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) : NonnegativeOrthant k :=
  ⟨fun j => (a j / ∑ i, a i) * ((y : ℝ) / p.val j), fun j =>
    mul_nonneg (div_pos (ha j) (exponent_sum_pos a ha)).le
      (div_nonneg y.property (p.property j).le)⟩

/-- At positive income every coordinate of Cobb-Douglas demand is strictly positive. -/
theorem cobbDouglasBundle_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (j : Fin k) : 0 < (CobbDouglasBundle a ha p y).val j :=
  mul_pos (div_pos (ha j) (exponent_sum_pos a ha)) (div_pos hy (p.property j))

/-- The expenditure-share formula exhausts income. -/
theorem expenditure_cobbDouglasBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (CobbDouglasBundle a ha p y) = (y : ℝ) := by
  have hterm (j : Fin k) :
      p.val j * (CobbDouglasBundle a ha p y).val j = a j * ((y : ℝ) / ∑ i, a i) := by
    dsimp only [CobbDouglasBundle]
    field_simp [ne_of_gt (p.property j)]
  simp only [Expenditure, hterm, ← Finset.sum_mul]
  exact mul_div_cancel₀ _ (ne_of_gt (exponent_sum_pos a ha))

/-- At positive income, the logarithmic marginal equals total exponent over income times price. -/
theorem cobbDouglasBundle_logMarginals {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (j : Fin k) :
    LogMarginals a 0 (CobbDouglasBundle a ha p y) j = ((∑ i, a i) / (y : ℝ)) * p.val j := by
  dsimp only [LogMarginals, CobbDouglasBundle, Pi.zero_apply]
  simp only [add_zero]
  field_simp [ne_of_gt (ha j), ne_of_gt (p.property j), ne_of_gt hy,
    ne_of_gt (exponent_sum_pos a ha)]

/-- The explicit bundle satisfies all logarithmic optimality conditions. -/
theorem cobbDouglasBundle_optimality {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    CombinedOptimality p y (CobbDouglasBundle a ha p y)
      (LogMarginals a 0 (CobbDouglasBundle a ha p y)) := by
  refine ⟨(expenditure_cobbDouglasBundle a ha p y).le, (∑ i, a i) / (y : ℝ),
    (div_pos (exponent_sum_pos a ha) hy).le, ?_, ?_, ?_⟩
  · intro j
    exact (cobbDouglasBundle_logMarginals a ha p y hy j).le
  · intro j _
    exact cobbDouglasBundle_logMarginals a ha p y hy j
  · rw [expenditure_cobbDouglasBundle]
    exact fun h => False.elim (lt_irrefl _ h)

/-- The expenditure-share formula is the unique demand at positive income. -/
theorem cobbDouglas_demand_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    MarshallianDemand (CobbDouglas a) p y = {CobbDouglasBundle a ha p y} := by
  exact shiftedCobbDouglas_demand_of_optimality a 0 ha (fun _ => le_rfl)
    (fun j => by simpa using cobbDouglasBundle_pos a ha p y hy j)
    (cobbDouglasBundle_optimality a ha p y hy)

/-- The expenditure-share formula becomes the origin at zero income. -/
theorem cobbDouglasBundle_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) :
    CobbDouglasBundle a ha p 0 = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [CobbDouglasBundle, ZeroBundle]

/-- The full Cobb-Douglas demand formula of pp. 59-60, for every nonnegative income. -/
theorem cobbDouglas_demand {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (CobbDouglas a) p y = {CobbDouglasBundle a ha p y} := by
  by_cases hy : 0 < (y : ℝ)
  · exact cobbDouglas_demand_pos a ha p y hy
  · have hzero : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
    subst y
    rw [marshallianDemand_zero, cobbDouglasBundle_zero]

/-- The source's interiority assertion follows for every full-domain optimum. -/
theorem cobbDouglas_demand_positive {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {x : NonnegativeOrthant k} (hx : x ∈ MarshallianDemand (CobbDouglas a) p y) :
    ∀ j, 0 < x.val j := by
  rw [cobbDouglas_demand a ha p y, Set.mem_singleton_iff] at hx
  subst x
  exact cobbDouglasBundle_pos a ha p y hy

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Marginal utility per dollar and expenditure shares

Kreps I, pp. 60-62. Consumed goods have equal marginal utility per dollar;
no unconsumed good has a larger ratio. Cross-multiplied identities remain valid
when the multiplier is zero. A ratio of marginal utilities is asserted only
when its denominator is nonzero, rather than giving `0/0` an economic meaning.
The Cobb-Douglas corollaries include the source's ten-percent illustration.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Combined optimality gives a common upper bound on marginal utility per dollar. -/
theorem combinedOptimality_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m) :
    ∃ l : ℝ, 0 ≤ l ∧ (∀ j, m j / p.val j ≤ l) ∧
      (∀ j, 0 < x.val j → m j / p.val j = l) := by
  obtain ⟨_, l, hl, hm, he, _⟩ := ho
  refine ⟨l, hl, fun j => (div_le_iff₀ (p.property j)).mpr (hm j), ?_⟩
  intro j hj
  exact (div_eq_iff (ne_of_gt (p.property j))).mpr (he j hj)

/-- No good offers a higher marginal return per dollar than a consumed good. -/
theorem consumed_good_maximizes_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hj : 0 < x.val j) : m i / p.val i ≤ m j / p.val j := by
  obtain ⟨l, _, hm, he⟩ := combinedOptimality_bangForBuck ho
  rw [he j hj]
  exact hm i

/-- Consumed goods have equal marginal returns per dollar, even when both returns vanish. -/
theorem consumed_goods_equal_bangForBuck {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) :
    m i / p.val i = m j / p.val j :=
  le_antisymm (consumed_good_maximizes_bangForBuck ho i j hj)
    (consumed_good_maximizes_bangForBuck ho j i hi)

/-- The price/marginal identity without division by a possibly zero marginal. -/
theorem consumed_goods_marginal_cross_product {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) :
    m i * p.val j = m j * p.val i := by
  have h := consumed_goods_equal_bangForBuck ho i j hi hj
  exact (div_eq_div_iff (ne_of_gt (p.property i)) (ne_of_gt (p.property j))).mp h

/-- The marginal-utility ratio equals the price ratio when the marginal denominator is nonzero. -/
theorem consumed_goods_marginal_ratio {k : ℕ} {p : PositivePrices k} {y : ℝ≥0}
    {x : NonnegativeOrthant k} {m : Fin k → ℝ} (ho : CombinedOptimality p y x m)
    (i j : Fin k) (hi : 0 < x.val i) (hj : 0 < x.val j) (hmj : m j ≠ 0) :
    m i / m j = p.val i / p.val j := by
  apply (div_eq_div_iff hmj (ne_of_gt (p.property j))).mpr
  simpa only [mul_comm] using consumed_goods_marginal_cross_product ho i j hi hj

/-- Each Cobb-Douglas expenditure is precisely its exponent's fraction of total income. -/
theorem cobbDouglas_expenditure_share {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    p.val j * (CobbDouglasBundle a ha p y).val j = (a j / ∑ i, a i) * (y : ℝ) := by
  dsimp only [CobbDouglasBundle]
  field_simp [ne_of_gt (p.property j)]

/-- Changing other prices leaves Cobb-Douglas demand for a fixed-price good unchanged. -/
theorem cobbDouglas_other_prices_irrelevant {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p q : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : p.val j = q.val j) :
    (CobbDouglasBundle a ha p y).val j = (CobbDouglasBundle a ha q y).val j := by
  simp only [CobbDouglasBundle, hj]

/-- The literal ten-percent share illustration on p. 60. -/
theorem cobbDouglas_ten_percent {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : a j / (∑ i, a i) = 1 / 10) :
    (CobbDouglasBundle a ha p y).val j = (y : ℝ) / (10 * p.val j) := by
  simp only [CobbDouglasBundle, hj]
  ring

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Correspondences and parametric maxima

Kreps I, Appendix 4, pp. 471-477. The book's upper semicontinuity is the
sequential closed-graph condition. It must not be confused with open-set upper
hemicontinuity in the absence of a local compact bound. These general lemmas
provide the existence and limit steps used in the maximum theorem.
-/

namespace Kreps.ConsumerDemand

open Filter Set
open scoped Topology

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- Definition A4.2a: membership is preserved under simultaneous sequential limits. -/
def SequentialUpper (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (x : ℕ → X) (p₀ : P) (x₀ : X),
    Tendsto p atTop (𝓝 p₀) → Tendsto x atTop (𝓝 x₀) →
    (∀ n, x n ∈ A (p n)) → x₀ ∈ A p₀

/-- Definition A4.2b: every feasible limit point has a feasible companion sequence. -/
def SequentialLower (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (p₀ : P), Tendsto p atTop (𝓝 p₀) →
    ∀ x₀ ∈ A p₀, ∃ x : ℕ → X, (∀ᶠ n in atTop, x n ∈ A (p n)) ∧
      Tendsto x atTop (𝓝 x₀)

/-- The maximizing correspondence for an objective depending on the parameter. -/
def ParametricMaxima (A : P → Set X) (F : P → X → ℝ) (p : P) : Set X :=
  {x | x ∈ A p ∧ ∀ y ∈ A p, F p y ≤ F p x}

omit [TopologicalSpace P] in
/-- Compact, nonempty feasible sets give nonempty maximizing sets. -/
theorem parametricMaxima_nonempty {A : P → Set X} {F : P → X → ℝ} {p : P}
    (hA : IsCompact (A p)) (hne : (A p).Nonempty) (hF : Continuous (F p)) :
    (ParametricMaxima A F p).Nonempty := by
  obtain ⟨x, hx, hm⟩ := hA.exists_isMaxOn hne hF.continuousOn
  exact ⟨x, hx, hm⟩

/-- The closed-graph step of Berge's theorem, using the book's sequential conventions. -/
theorem parametricMaxima_sequentialUpper {A : P → Set X} {F : P → X → ℝ}
    (hA : SequentialUpper A) (hL : SequentialLower A)
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    SequentialUpper (ParametricMaxima A F) := by
  intro p x p₀ x₀ hp hx hm
  refine ⟨hA p x p₀ x₀ hp hx (fun n => (hm n).1), ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hL p p₀ hp y hy
  exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
    (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
    (hz.mono fun n hn => (hm n).2 (z n) hn)

/-- A compact local bound converts the book's upper condition to Mathlib hemicontinuity. -/
theorem sequentialUpper_upperHemicontinuousAt {A : P → Set X} {p₀ : P}
    [(𝓝 p₀).IsCountablyGenerated] (hA : SequentialUpper A)
    {K : Set X} (hK : IsSeqCompact K) (hb : ∀ᶠ p in 𝓝 p₀, A p ⊆ K) :
    UpperHemicontinuousAt A p₀ := by
  apply UpperHemicontinuousAt.of_sequences hK hb
  intro p hp x hx x₀ hlim
  exact hA p x p₀ x₀ hp hlim hx

/-- Continuous feasible selections through each point imply the book's lower condition. -/
theorem sequentialLower_of_continuous_selections {A : P → Set X}
    (h : ∀ p x, x ∈ A p → ∃ s : P → X,
      Continuous s ∧ s p = x ∧ ∀ q, s q ∈ A q) : SequentialLower A := by
  intro p p₀ hp x₀ hx₀
  obtain ⟨s, hs, hsp, hmem⟩ := h p₀ x₀ hx₀
  refine ⟨s ∘ p, Eventually.of_forall (fun n => hmem (p n)), ?_⟩
  simpa only [hsp] using hs.continuousAt.tendsto.comp hp

/-- A local compact container for all nearby feasible sets (Appendix 4). -/
def LocalCompactBound (A : P → Set X) : Prop :=
  ∀ p, ∃ K : Set X, IsCompact K ∧ ∀ᶠ q in 𝓝 p, A q ⊆ K

/-- The supremum value of a parameterized optimization problem. -/
noncomputable def ParametricValue (A : P → Set X) (F : P → X → ℝ) (p : P) : ℝ :=
  sSup (F p '' A p)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- An attained maximum evaluates the supremum without any choice of maximizer. -/
theorem parametricValue_eq_of_maximum {A : P → Set X} {F : P → X → ℝ} {p : P} {x : X}
    (hx : x ∈ ParametricMaxima A F p) : ParametricValue A F p = F p x := by
  apply csSup_eq_of_is_forall_le_of_forall_le_imp_ge
  · exact ⟨F p x, x, hx.1, rfl⟩
  · rintro v ⟨y, hy, rfl⟩
    exact hx.2 y hy
  · intro b hb
    exact hb _ ⟨x, hx.1, rfl⟩

/-- The maximum-value continuity step, with existence separated from the limit argument. -/
theorem parametricValue_continuous [SequentialSpace P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hupper : SequentialUpper (ParametricMaxima A F))
    (hne : ∀ p, (ParametricMaxima A F p).Nonempty)
    (hbound : LocalCompactBound (ParametricMaxima A F))
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    Continuous (ParametricValue A F) := by
  classical
  choose s hs using hne
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hpn := hp.comp hns
  obtain ⟨K, hK, hb⟩ := hbound p₀
  have hev : ∀ᶠ n in atTop, s (p (ns n)) ∈ K := by
    filter_upwards [hpn hb] with n hn
    exact hn (hs _)
  obtain ⟨x, _, ms, hms, hlim⟩ := hK.tendsto_subseq' hev.frequently
  have hpm := hpn.comp hms.tendsto_atTop
  have hx : x ∈ ParametricMaxima A F p₀ :=
    hupper (fun n => p (ns (ms n))) (fun n => s (p (ns (ms n))))
      p₀ x hpm hlim (fun n => hs _)
  refine ⟨ms, ?_⟩
  have ht := hF.continuousAt.tendsto.comp (hpm.prodMk_nhds hlim)
  have heq : (fun n => ParametricValue A F (p (ns (ms n)))) =
      (fun n => F (p (ns (ms n))) (s (p (ns (ms n))))) := by
    funext n
    exact parametricValue_eq_of_maximum (hs _)
  change Tendsto (fun n => ParametricValue A F (p (ns (ms n)))) atTop
    (𝓝 (ParametricValue A F p₀))
  rw [heq, parametricValue_eq_of_maximum hx]
  exact ht

/-- Local compact containment passes to every pointwise smaller correspondence. -/
theorem LocalCompactBound.mono {A B : P → Set X} (h : LocalCompactBound B)
    (hab : ∀ p, A p ⊆ B p) : LocalCompactBound A := by
  intro p
  obtain ⟨K, hK, hb⟩ := h p
  exact ⟨K, hK, hb.mono (fun q hq => (hab q).trans hq)⟩

/-- Closed-graph fibers are closed in first-countable spaces. -/
theorem SequentialUpper.isClosed [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (p : P) : IsClosed (A p) := by
  apply isSeqClosed_iff_isClosed.mp
  intro x x₀ hx ht
  exact h (fun _ => p) x p x₀ tendsto_const_nhds ht hx

/-- The book's closed-graph condition and a local compact bound imply compact values. -/
theorem SequentialUpper.isCompact [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (hb : LocalCompactBound A) (p : P) : IsCompact (A p) := by
  obtain ⟨K, hK, hlocal⟩ := hb p
  exact hK.of_isClosed_subset (h.isClosed p) hlocal.self_of_nhds

/-- Corollary A4.8's singleton step, without needing a utility function. -/
theorem continuous_of_singleton_correspondence [FirstCountableTopology P]
    [FirstCountableTopology X] {s : P → X}
    (hu : SequentialUpper (fun p => {s p}))
    (hb : LocalCompactBound (fun p => {s p})) : Continuous s := by
  apply upperHemicontinuous_singleton_iff.mp
  intro p
  obtain ⟨K, hK, hk⟩ := hb p
  exact sequentialUpper_upperHemicontinuousAt hu hK.isSeqCompact hk

/-- Equality of objective suprema expressed by equality of all real upper bounds.
This avoids assigning a real value to the supremum of an unbounded set. -/
def SameObjectiveUpperBounds (A B : P → Set X) (F : P → X → ℝ) : Prop :=
  ∀ p r, (∀ x ∈ A p, F p x ≤ r) ↔ (∀ x ∈ B p, F p x ≤ r)

/-- Berge's auxiliary-correspondence form: the feasible set itself need not be compact.
The nonempty auxiliary fibers make the convention used in the source proof explicit. -/
theorem maximum_theorem_auxiliary [FirstCountableTopology P] [FirstCountableTopology X]
    {A B : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper B) (hb : LocalCompactBound B)
    (hne : ∀ p, (B p).Nonempty) (hba : ∀ p, B p ⊆ A p)
    (hzb : ∀ p, ParametricMaxima A F p ⊆ B p)
    (hsup : SameObjectiveUpperBounds A B F) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) := by
  have hn (p) : (ParametricMaxima A F p).Nonempty := by
    have hc : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
    obtain ⟨x, hx, hmax⟩ := parametricMaxima_nonempty (hu.isCompact hb p) (hne p) hc
    exact ⟨x, hba p hx, (hsup p (F p x)).mpr hmax⟩
  have hz : SequentialUpper (ParametricMaxima A F) := by
    intro p x p₀ x₀ hp hx hm
    have hxB : x₀ ∈ B p₀ := hu p x p₀ x₀ hp hx (fun n => hzb _ (hm n))
    refine ⟨hba _ hxB, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hl p p₀ hp y hy
    exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
      (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
      (hz.mono fun n hn => (hm n).2 (z n) hn)
  have hbound := hb.mono hzb
  exact ⟨hn, hz, hbound, parametricValue_continuous hz hn hbound hF⟩

/-- The compact-feasible-set version used for consumer budgets, including zero income. -/
theorem maximum_theorem [FirstCountableTopology P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper A) (hb : LocalCompactBound A)
    (hne : ∀ p, (A p).Nonempty) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) :=
  maximum_theorem_auxiliary hF hl hu hb hne (fun _ => Subset.rfl)
    (fun _ _ hx => hx.1) (fun _ _ => Iff.rfl)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- For nonempty objectives with finite upper bounds, the auxiliary theorem's upper-bound
formulation is exactly equality of the printed real suprema. -/
theorem sameObjectiveUpperBounds_iff_value_eq {A B : P → Set X} {F : P → X → ℝ}
    (ha : ∀ p, (A p).Nonempty) (hb : ∀ p, (B p).Nonempty)
    (hba : ∀ p, BddAbove (F p '' A p)) (hbb : ∀ p, BddAbove (F p '' B p)) :
    SameObjectiveUpperBounds A B F ↔ ∀ p, ParametricValue A F p = ParametricValue B F p := by
  have hA (p : P) (r : ℝ) : ParametricValue A F p ≤ r ↔ ∀ x ∈ A p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hba p) ((ha p).image (F p))]
    simp
  have hB (p : P) (r : ℝ) : ParametricValue B F p ≤ r ↔ ∀ x ∈ B p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hbb p) ((hb p).image (F p))]
    simp
  constructor
  · intro h p
    apply le_antisymm
    · exact (hA p _).mpr ((h p _).mpr ((hB p _).mp le_rfl))
    · exact (hB p _).mpr ((h p _).mp ((hA p _).mp le_rfl))
  · intro h p r
    rw [← hA, ← hB, h p]

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuity and local boundedness of the budget correspondence

Kreps I, the proof of Proposition 3.3, pp. 55-56. The graph is closed and nearby
budgets lie in a common compact coordinate box. For lower semicontinuity we use
the printed recovery formula `(y'/y) * (p · x)/(p' · x) * x`, with the zero
bundle handled separately. The formula supplies a continuous feasible selection
through every feasible bundle, including the zero-income case.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal Topology

/-- The full parameter domain, including zero income but excluding zero prices. -/
abbrev PriceIncome (k : ℕ) := PositivePrices k × ℝ≥0

/-- Scale a nonnegative bundle by a nonnegative scalar. -/
def ScaleBundle {k : ℕ} (a : ℝ≥0) (x : NonnegativeOrthant k) : NonnegativeOrthant k :=
  ⟨fun j => (a : ℝ) * x.val j, fun j => mul_nonneg a.property (x.property j)⟩

/-- Scaling zero consumption leaves it unchanged. -/
theorem scaleBundle_zero {k : ℕ} (a : ℝ≥0) : ScaleBundle a (ZeroBundle k) = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, ZeroBundle]

/-- Scaling by one leaves the whole bundle unchanged. -/
theorem scaleBundle_one {k : ℕ} (x : NonnegativeOrthant k) : ScaleBundle 1 x = x := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle]

/-- Expenditure scales linearly in consumption. -/
theorem expenditure_scaleBundle {k : ℕ} (p : PositivePrices k) (a : ℝ≥0)
    (x : NonnegativeOrthant k) : Expenditure p (ScaleBundle a x) = a * Expenditure p x := by
  simp only [Expenditure, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every nonzero nonnegative bundle costs strictly more than zero at strictly positive prices. -/
theorem expenditure_pos {k : ℕ} (p : PositivePrices k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : 0 < Expenditure p x := by
  have hn : Expenditure p x ≠ 0 := by
    intro he
    apply hx
    apply Subtype.ext
    funext j
    have h := commodity_expenditure_le p x j
    have hp := p.property j
    have hxj : 0 ≤ x.val j := x.property j
    change x.val j = 0
    rw [he] at h
    nlinarith
  exact lt_of_le_of_ne (expenditure_nonneg p x) hn.symm

/-- For a fixed bundle, expenditure varies continuously with the price vector. -/
theorem expenditure_price_continuous {k : ℕ} (x : NonnegativeOrthant k) :
    Continuous (fun p : PositivePrices k => Expenditure p x) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- Joint continuity in prices and consumption gives closed budget graphs. -/
theorem expenditure_joint_continuous {k : ℕ} :
    Continuous (fun z : PositivePrices k × NonnegativeOrthant k => Expenditure z.1 z.2) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))

/-- The exact nonnegative multiplier in the book's recovery sequence. -/
noncomputable def BudgetAdjustmentFactor {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : ℝ≥0 :=
  ⟨(η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x),
    mul_nonneg (div_nonneg η.2.property θ.2.property)
      (div_nonneg (expenditure_nonneg θ.1 x) (expenditure_nonneg η.1 x))⟩

/-- Adjust the reference bundle to the new prices and income by the printed scaling formula. -/
noncomputable def BudgetAdjustment {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : NonnegativeOrthant k :=
  ScaleBundle (BudgetAdjustmentFactor θ x η) x

/-- The recovery multiplier equals one at its positive-income, nonzero reference point. -/
theorem budgetAdjustment_self {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ≠ ZeroBundle k) : BudgetAdjustment θ x θ = x := by
  have hf : BudgetAdjustmentFactor θ x θ = 1 := by
    apply NNReal.coe_injective
    change (θ.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure θ.1 x) = 1
    rw [div_self hy.ne', div_self (expenditure_pos θ.1 hx).ne', one_mul]
  rw [BudgetAdjustment, hf, scaleBundle_one]

/-- Every adjusted bundle remains feasible at its new prices and income. -/
theorem budgetAdjustment_feasible {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ∈ BudgetSet θ.1 θ.2) (η : PriceIncome k) :
    BudgetAdjustment θ x η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    change Expenditure η.1 (ScaleBundle _ (ZeroBundle k)) ≤ (η.2 : ℝ)
    rw [scaleBundle_zero, expenditure_zero]
    exact η.2.property
  change Expenditure η.1 (ScaleBundle _ x) ≤ (η.2 : ℝ)
  rw [expenditure_scaleBundle]
  change ((η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x)) *
    Expenditure η.1 x ≤ (η.2 : ℝ)
  rw [mul_assoc, div_mul_cancel₀ _ (expenditure_pos η.1 hx0).ne']
  calc
    _ ≤ ((η.2 : ℝ) / θ.2) * θ.2 :=
      mul_le_mul_of_nonneg_left hx (div_nonneg η.2.property θ.2.property)
    _ = _ := div_mul_cancel₀ _ hy.ne'

/-- The recovery bundle is continuous in the new parameters when the reference is nonzero. -/
theorem budgetAdjustment_continuous {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : Continuous (BudgetAdjustment θ x) := by
  have hf : Continuous (fun η : PriceIncome k => (BudgetAdjustmentFactor θ x η : ℝ)) :=
    ((continuous_subtype_val.comp continuous_snd).div_const (θ.2 : ℝ)).mul
      (continuous_const.div ((expenditure_price_continuous x).comp continuous_fst)
        (fun η => (expenditure_pos η.1 hx).ne'))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact hf.mul continuous_const

/-- Every feasible reference bundle admits a global continuous feasible recovery selection. -/
theorem budgetSet_continuous_selection {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (hx : x ∈ BudgetSet θ.1 θ.2) :
    ∃ s : PriceIncome k → NonnegativeOrthant k, Continuous s ∧ s θ = x ∧
      ∀ η, s η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    exact ⟨fun _ => ZeroBundle k, continuous_const, rfl,
      fun η => by change Expenditure η.1 (ZeroBundle k) ≤ (η.2 : ℝ)
                  rw [expenditure_zero]; exact η.2.property⟩
  have hy : 0 < (θ.2 : ℝ) := (expenditure_pos θ.1 hx0).trans_le hx
  exact ⟨BudgetAdjustment θ x, budgetAdjustment_continuous θ hx0,
    budgetAdjustment_self θ hy hx0, budgetAdjustment_feasible θ hy hx⟩

/-- The budget correspondence is lower semicontinuous, including at zero income. -/
theorem budgetSet_sequentialLower {k : ℕ} :
    SequentialLower (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) :=
  sequentialLower_of_continuous_selections budgetSet_continuous_selection

/-- Limits of feasible bundles are feasible at the limiting prices and income. -/
theorem budgetSet_sequentialUpper {k : ℕ} :
    SequentialUpper (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ x θ₀ x₀ hθ hx hm
  have he := expenditure_joint_continuous.continuousAt.tendsto.comp
    ((continuous_fst.continuousAt.tendsto.comp hθ).prodMk_nhds hx)
  have hy := (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hθ
  exact le_of_tendsto_of_tendsto he hy (Filter.Eventually.of_forall hm)

/-- All nearby budgets fit in one compact coordinate box. -/
theorem budgetSet_localCompactBound {k : ℕ} :
    LocalCompactBound (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ
  let b : Fin k → ℝ := fun j => ((θ.2 : ℝ) + 1) / (θ.1.val j / 2)
  let K := (Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹' Set.Icc 0 b
  have hK : IsCompact K :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  refine ⟨K, hK, ?_⟩
  have hyc : Continuous (fun η : PriceIncome k => (η.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hy : ∀ᶠ η : PriceIncome k in 𝓝 θ, (η.2 : ℝ) < (θ.2 : ℝ) + 1 :=
    (hyc.continuousAt (x := θ)).eventually
      (isOpen_Iio.mem_nhds (show (θ.2 : ℝ) < (θ.2 : ℝ) + 1 by linarith))
  have hp : ∀ᶠ η : PriceIncome k in 𝓝 θ, ∀ j, θ.1.val j / 2 < η.1.val j := by
    apply Filter.eventually_all.mpr
    intro j
    have hjc : Continuous (fun η : PriceIncome k => η.1.val j) :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    have hj : θ.1.val j / 2 < θ.1.val j := by have h := θ.1.property j; linarith
    exact hjc.continuousAt.eventually (isOpen_Ioi.mem_nhds hj)
  filter_upwards [hy, hp] with η hy hp
  intro x hx
  refine ⟨x.property, fun j => ?_⟩
  apply (le_div_iff₀ (by have h := θ.1.property j; positivity)).mpr
  have h₁ := commodity_expenditure_le η.1 x j
  have h₂ := mul_le_mul_of_nonneg_right (hp j).le (x.property j)
  change Expenditure η.1 x ≤ (η.2 : ℝ) at hx
  change x.val j * (θ.1.val j / 2) ≤ (θ.2 : ℝ) + 1
  nlinarith

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Budget vertices and positive bundles

Kreps I, Section 3.1 and Figure 3.1, pp. 50-51. The single-good vertices spend
the entire budget on one commodity. Positive income also makes a strictly
positive bundle affordable, which is useful when boundary utility is zero.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Spending the entire income on commodity `j`, including the zero-income case. -/
noncomputable def SingleGoodBundle {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    NonnegativeOrthant k :=
  ⟨Pi.single j ((y : ℝ) / p.val j), fun i => by
    by_cases h : i = j
    · subst i
      simpa using div_nonneg y.property (p.property j).le
    · simp [h]⟩

/-- A single-good vertex exhausts the budget. -/
theorem expenditure_singleGoodBundle {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (j : Fin k) : Expenditure p (SingleGoodBundle p y j) = (y : ℝ) := by
  simp [Expenditure, SingleGoodBundle, Pi.single_apply,
    mul_div_cancel₀ _ (ne_of_gt (p.property j))]

/-- All single-good vertices are feasible. -/
theorem singleGoodBundle_mem_budgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    (j : Fin k) : SingleGoodBundle p y j ∈ BudgetSet p y :=
  (expenditure_singleGoodBundle p y j).le

/-- Dividing positive income equally across expenditures gives a positive feasible bundle. -/
theorem budgetSet_exists_positive {k : ℕ} [NeZero k] (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ x ∈ BudgetSet p y, ∀ j, 0 < x.val j := by
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  let x : NonnegativeOrthant k :=
    ⟨fun j => (y : ℝ) / ((k : ℝ) * p.val j), fun j => by
      exact (div_pos hy (mul_pos hk (p.property j))).le⟩
  refine ⟨x, ?_, fun j => div_pos hy (mul_pos hk (p.property j))⟩
  change (∑ j, p.val j * ((y : ℝ) / ((k : ℝ) * p.val j))) ≤ (y : ℝ)
  have hterm (j : Fin k) :
      p.val j * ((y : ℝ) / ((k : ℝ) * p.val j)) = (y : ℝ) / k := by
    field_simp [ne_of_gt (p.property j)]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (mul_div_cancel₀ _ (ne_of_gt hk)).le

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two-good budget triangle

Kreps I, Figure 3.1, p. 51. The nonnegative two-good budget region is exactly
the convex hull of the origin and the two single-good intercepts. The statement
includes the degenerate zero-income triangle.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The three vertices of the two-good budget triangle. -/
noncomputable def BudgetTriangleVertices (p : PositivePrices 2) (y : ℝ≥0) :
    Set (Fin 2 → ℝ) :=
  {0, (SingleGoodBundle p y 0).val, (SingleGoodBundle p y 1).val}

/-- Every vertex belongs to the corresponding budget. -/
theorem budgetTriangleVertices_subset (p : PositivePrices 2) (y : ℝ≥0) :
    BudgetTriangleVertices p y ⊆ BudgetVectors p y := by
  intro x hx
  rcases hx with rfl | rfl | h
  · exact ⟨le_rfl, by simp⟩
  · exact ⟨(SingleGoodBundle p y 0).property, (expenditure_singleGoodBundle p y 0).le⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨(SingleGoodBundle p y 1).property, (expenditure_singleGoodBundle p y 1).le⟩

/-- **Figure 3.1:** the full budget region is precisely the triangle with the printed intercepts. -/
theorem budgetVectors_eq_triangle (p : PositivePrices 2) (y : ℝ≥0) :
    BudgetVectors p y = convexHull ℝ (BudgetTriangleVertices p y) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hy : 0 < (y : ℝ)
    · let w : Fin 3 → ℝ :=
        ![1 - (p.val 0 * x 0 + p.val 1 * x 1) / y,
          p.val 0 * x 0 / y, p.val 1 * x 1 / y]
      let z : Fin 3 → Fin 2 → ℝ :=
        ![0, (SingleGoodBundle p y 0).val, (SingleGoodBundle p y 1).val]
      have hbudget : p.val 0 * x 0 + p.val 1 * x 1 ≤ (y : ℝ) := by
        simpa [Fin.sum_univ_succ] using hx.2
      apply mem_convexHull_of_exists_fintype w z
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr ((div_le_one hy).mpr hbudget)
        · exact div_nonneg (mul_nonneg (p.property 0).le (hx.1 0)) hy.le
        · exact div_nonneg (mul_nonneg (p.property 1).le (hx.1 1)) hy.le
      · simp only [w, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one]
        ring
      · intro i
        fin_cases i <;> simp [z, BudgetTriangleVertices]
      · funext i
        fin_cases i <;>
          norm_num [w, z, SingleGoodBundle, Fin.sum_univ_succ] <;>
          field_simp [ne_of_gt (p.property 0), ne_of_gt (p.property 1), ne_of_gt hy]
    · have hy0 : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
      subst y
      have hzero : x = 0 := by
        have hmem : (⟨x, hx.1⟩ : NonnegativeOrthant 2) ∈ BudgetSet p 0 := hx.2
        rw [budgetSet_zero, Set.mem_singleton_iff] at hmem
        exact congrArg Subtype.val hmem
      rw [hzero]
      exact subset_convexHull ℝ _ (by simp [BudgetTriangleVertices])
  · exact convexHull_min (budgetTriangleVertices_subset p y) (budgetVectors_convex p y)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strict support inequalities for CES powers

Kreps I, Problem 3.7, pp. 64-65. Dividing the power by its nonzero exponent
gives an increasing, strictly concave transform for every exponent below one.
The comparison permits a zero alternative when the exponent is positive; for
negative exponents it applies on the positive half-line. These inequalities
will prove global optimality without differentiating at a zero coordinate.
-/

namespace Kreps.ConsumerDemand

/-- The normalized power lies strictly below its tangent at one. -/
theorem normalizedPower_unit_tangent_lt {mu t : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (ht : 0 ≤ t) (htp : mu < 0 → 0 < t) (hne : t ≠ 1) :
    (t ^ mu - 1) / mu < t - 1 := by
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · have hl := Real.log_lt_sub_one_of_pos (htp hm) hne
    have he := Real.add_one_le_exp (Real.log t * mu)
    rw [← Real.rpow_def_of_pos (htp hm)] at he
    have hm' := mul_lt_mul_of_neg_right hl hm
    apply (div_lt_iff_of_neg hm).mpr
    nlinarith
  · have hb := rpow_one_add_lt_one_add_mul_self
      (s := t - 1) (by linarith) (sub_ne_zero.mpr hne) hm hmu
    simp only [add_sub_cancel] at hb
    exact (div_lt_iff₀ hm).mpr (by linarith)

/-- The normalized power has a strict supporting tangent at every positive point. -/
theorem normalizedPower_tangent_lt {mu x z : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (hx : 0 < x) (hz : 0 ≤ z) (hzp : mu < 0 → 0 < z) (hne : z ≠ x) :
    (z ^ mu - x ^ mu) / mu < x ^ (mu - 1) * (z - x) := by
  have hxp := Real.rpow_pos_of_pos hx mu
  have ht := normalizedPower_unit_tangent_lt hmu hm0 (div_nonneg hz hx.le)
    (fun hm => div_pos (hzp hm) hx) (by
      intro he
      exact hne ((div_eq_one_iff_eq hx.ne').mp he))
  calc
    (z ^ mu - x ^ mu) / mu = x ^ mu * ((z / x) ^ mu - 1) / mu := by
      rw [Real.div_rpow hz hx.le]
      field_simp
    _ < x ^ mu * (z / x - 1) := by
      simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left ht hxp
    _ = x ^ (mu - 1) * (z - x) := by
      rw [Real.rpow_sub_one hx.ne']
      field_simp

/-- The weak supporting inequality also includes an alternative equal to the base point. -/
theorem normalizedPower_tangent_le {mu x z : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (hx : 0 < x) (hz : 0 ≤ z) (hzp : mu < 0 → 0 < z) :
    (z ^ mu - x ^ mu) / mu ≤ x ^ (mu - 1) * (z - x) := by
  by_cases he : z = x
  · simp [he]
  · exact (normalizedPower_tangent_lt hmu hm0 hx hz hzp he).le

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The CES consumer's demand

Kreps I, Problem 3.7, pp. 64-65. The full nonnegative orthant is retained.
For a negative exponent the utility is extended by zero whenever any commodity
quantity is zero, as required by the limiting interior formula. Positive income
has the unique interior demand proportional to `(a j / p j) ^ (1 / (1 - mu))`.
The proof compares every affordable alternative using strict support inequalities.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The power sum inside the CES utility. -/
noncomputable def CESPowerSum {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (x : NonnegativeOrthant k) : ℝ := ∑ j, a j * x.val j ^ mu

/-- CES utility, with its zero boundary extension for negative exponents. -/
noncomputable def CESUtility {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (x : NonnegativeOrthant k) : ℝ :=
  if mu < 0 ∧ ∃ j, x.val j = 0 then 0 else CESPowerSum a mu x ^ (1 / mu)

/-- The positive price-adjusted power weight in the CES demand formula. -/
noncomputable def CESWeight {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (p : PositivePrices k) (j : Fin k) : ℝ := (a j / p.val j) ^ (1 / (1 - mu))

/-- The expenditure needed to buy one unit of the vector of CES weights. -/
noncomputable def CESDenominator {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (p : PositivePrices k) : ℝ := ∑ j, p.val j * CESWeight a mu p j

/-- Every CES weight is positive when its primitive coefficient and price are positive. -/
theorem cesWeight_pos {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) (j : Fin k) : 0 < CESWeight a mu p j :=
  Real.rpow_pos_of_pos (div_pos (ha j) (p.property j)) _

/-- The CES denominator is strictly positive in a nonempty commodity space. -/
theorem cesDenominator_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) :
    0 < CESDenominator a mu p :=
  Finset.sum_pos (fun j _ => mul_pos (p.property j) (cesWeight_pos a ha mu p j))
    Finset.univ_nonempty

/-- The CES demand formula, scaled to exhaust the given income. -/
noncomputable def CESBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) :
    NonnegativeOrthant k :=
  ⟨fun j => ((y : ℝ) / CESDenominator a mu p) * CESWeight a mu p j,
    fun j => mul_nonneg (div_nonneg y.property (cesDenominator_pos a ha mu p).le)
      (cesWeight_pos a ha mu p j).le⟩

/-- Every coordinate of the formula is positive at positive income. -/
theorem cesBundle_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) (j : Fin k) :
    0 < (CESBundle a ha mu p y).val j :=
  mul_pos (div_pos hy (cesDenominator_pos a ha mu p)) (cesWeight_pos a ha mu p j)

/-- The explicit CES bundle exhausts income. -/
theorem expenditure_cesBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (CESBundle a ha mu p y) = (y : ℝ) := by
  unfold Expenditure CESBundle
  simp only
  simp_rw [mul_left_comm (p.val _), ← Finset.mul_sum]
  exact div_mul_cancel₀ _ (cesDenominator_pos a ha mu p).ne'

/-- The normalized power marginal has the same ratio to price in every coordinate. -/
theorem cesBundle_marginal_ratio {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (j : Fin k) :
    a j * (CESBundle a ha mu p y).val j ^ (mu - 1) =
      ((y : ℝ) / CESDenominator a mu p) ^ (mu - 1) * p.val j := by
  have hbase := div_pos (ha j) (p.property j)
  have hscale := div_pos hy (cesDenominator_pos a ha mu p)
  have he : 1 / (1 - mu) * (mu - 1) = -1 := by
    field_simp [ne_of_gt (sub_pos.mpr hmu)]
    ring
  change a j * (((y : ℝ) / CESDenominator a mu p) *
    (a j / p.val j) ^ (1 / (1 - mu))) ^ (mu - 1) = _
  rw [Real.mul_rpow hscale.le (Real.rpow_nonneg hbase.le _),
    ← Real.rpow_mul hbase.le, he, Real.rpow_neg_one]
  field_simp [ne_of_gt (ha j), ne_of_gt (p.property j)]

/-- Strict coordinate support inequalities sum to a strict budget comparison. -/
theorem cesPowerSum_strict_support {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) {x z : NonnegativeOrthant k}
    (hx : ∀ j, 0 < x.val j) (hz : mu < 0 → ∀ j, 0 < z.val j) (hne : z ≠ x) :
    (CESPowerSum a mu z - CESPowerSum a mu x) / mu <
      ∑ j, (a j * x.val j ^ (mu - 1)) * (z.val j - x.val j) := by
  have he : (CESPowerSum a mu z - CESPowerSum a mu x) / mu =
      ∑ j, a j * ((z.val j ^ mu - x.val j ^ mu) / mu) := by
    simp only [CESPowerSum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Finset.sum_lt_sum
  · intro j _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (normalizedPower_tangent_le hmu hm0 (hx j) (z.property j) (fun hm => hz hm j))
      (ha j).le
  · have hcoord : ∃ j, z.val j ≠ x.val j := by
      by_contra hn
      push Not at hn
      exact hne (Subtype.ext (funext hn))
    obtain ⟨j, hj⟩ := hcoord
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simpa only [mul_assoc] using mul_lt_mul_of_pos_left
      (normalizedPower_tangent_lt hmu hm0 (hx j) (z.property j)
        (fun hm => hz hm j) hj) (ha j)

/-- Every power sum is nonnegative on the full orthant. -/
theorem cesPowerSum_nonneg {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (x : NonnegativeOrthant k) : 0 ≤ CESPowerSum a mu x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (ha j).le (Real.rpow_nonneg (x.property j) _))

/-- Every power sum at an interior bundle is strictly positive. -/
theorem cesPowerSum_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    0 < CESPowerSum a mu x :=
  Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _))
    Finset.univ_nonempty

/-- The boundary clause does not affect the formula on the positive orthant. -/
theorem cesUtility_of_positive {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    CESUtility a mu x = CESPowerSum a mu x ^ (1 / mu) := by
  have hn : ¬∃ j, x.val j = 0 := fun ⟨j, hj⟩ => (hx j).ne' hj
  simp [CESUtility, hn]

/-- Interior CES utility is positive, for either sign of the exponent. -/
theorem cesUtility_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    0 < CESUtility a mu x := by
  rw [cesUtility_of_positive a mu hx]
  exact Real.rpow_pos_of_pos (cesPowerSum_pos a ha mu hx) _

/-- Every distinct affordable alternative has a smaller normalized power sum. -/
theorem cesPowerSum_strict_budget {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hzp : mu < 0 → ∀ j, 0 < z.val j) (hne : z ≠ CESBundle a ha mu p y) :
    (CESPowerSum a mu z - CESPowerSum a mu (CESBundle a ha mu p y)) / mu < 0 := by
  have hs := cesPowerSum_strict_support a ha hmu hm0
    (cesBundle_pos a ha mu p y hy) hzp hne
  simp_rw [cesBundle_marginal_ratio a ha hmu p y hy, mul_assoc,
    ← Finset.mul_sum] at hs
  have he : (∑ j, p.val j * (z.val j - (CESBundle a ha mu p y).val j)) =
      Expenditure p z - Expenditure p (CESBundle a ha mu p y) := by
    simp only [Expenditure, mul_sub, Finset.sum_sub_distrib]
  rw [he, expenditure_cesBundle] at hs
  exact hs.trans_le (mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_pos_of_pos (div_pos hy (cesDenominator_pos a ha mu p)) _).le
    (sub_nonpos.mpr hz))

/-- The explicit CES bundle strictly beats every other affordable bundle, including axes. -/
theorem cesUtility_strict_budget {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y)
    (hne : z ≠ CESBundle a ha mu p y) :
    CESUtility a mu z < CESUtility a mu (CESBundle a ha mu p y) := by
  have hx := cesBundle_pos a ha mu p y hy
  by_cases hb : mu < 0 ∧ ∃ j, z.val j = 0
  · rw [CESUtility, ite_eq_left hb]
    exact cesUtility_pos a ha mu hx
  have hzp : mu < 0 → ∀ j, 0 < z.val j := by
    intro hm j
    exact lt_of_le_of_ne (z.property j) (fun he => hb ⟨hm, j, he.symm⟩)
  have hs := cesPowerSum_strict_budget a ha hmu hm0 p y hy hz hzp hne
  rw [CESUtility, ite_eq_right hb, cesUtility_of_positive a mu hx]
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · have hsum : CESPowerSum a mu (CESBundle a ha mu p y) < CESPowerSum a mu z := by
      have h := (div_lt_iff_of_neg hm).mp hs
      linarith
    exact Real.rpow_lt_rpow_of_neg (cesPowerSum_pos a ha mu hx) hsum
      (one_div_neg.mpr hm)
  · have hsum : CESPowerSum a mu z < CESPowerSum a mu (CESBundle a ha mu p y) := by
      have h := (div_lt_iff₀ hm).mp hs
      linarith
    exact Real.rpow_lt_rpow (cesPowerSum_nonneg a ha mu z) hsum (one_div_pos.mpr hm)

/-- The CES demand formula is the unique maximizer at positive income. -/
theorem ces_demand_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    MarshallianDemand (CESUtility a mu) p y = {CESBundle a ha mu p y} := by
  have hbudget : CESBundle a ha mu p y ∈ BudgetSet p y :=
    (expenditure_cesBundle a ha mu p y).le
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact not_lt_of_ge (hz.2 _ hbudget)
      (cesUtility_strict_budget a ha hmu hm0 p y hy hz.1 hne)
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst z
    refine ⟨hbudget, fun z hz => ?_⟩
    by_cases he : z = CESBundle a ha mu p y
    · change CESUtility a mu z ≤ CESUtility a mu (CESBundle a ha mu p y)
      exact (congrArg (CESUtility a mu) he).le
    · exact (cesUtility_strict_budget a ha hmu hm0 p y hy hz he).le

/-- At zero income the CES formula gives the origin. -/
theorem cesBundle_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (p : PositivePrices k) : CESBundle a ha mu p 0 = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [CESBundle, ZeroBundle]

/-- **Problem 3.7:** the full CES demand correspondence for every nonnegative income. -/
theorem problem_3_7 {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 1) (hm0 : mu ≠ 0) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (CESUtility a mu) p y = {CESBundle a ha mu p y} := by
  by_cases hy : 0 < (y : ℝ)
  · exact ces_demand_pos a ha hmu hm0 p y hy
  · have he : y = 0 := Subtype.ext (le_antisymm (le_of_not_gt hy) y.property)
    subst y
    rw [marshallianDemand_zero, cesBundle_zero]

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuity of CES utility at the axes

Kreps I, Problem 3.7, pp. 64-65. Negative powers are evaluated only at positive
coordinates in the interior formula. Its zero extension at an axis is continuous:
utility is bounded above by a positive constant times every coordinate. Thus the
full-domain demand theorem does not rely on the value of `Real.rpow` at zero
for a negative exponent.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators Topology
open Filter

/-- CES utility is nonnegative on the entire consumption domain. -/
theorem cesUtility_nonneg {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (mu : ℝ) (x : NonnegativeOrthant k) : 0 ≤ CESUtility a mu x := by
  unfold CESUtility
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (cesPowerSum_nonneg a ha mu x) _

/-- A negative-exponent CES utility vanishes whenever a commodity is absent. -/
theorem cesUtility_zero_of_coordinate {k : ℕ} (a : Fin k → ℝ) {mu : ℝ}
    (hmu : mu < 0) {x : NonnegativeOrthant k} {j : Fin k} (hj : x.val j = 0) :
    CESUtility a mu x = 0 := by
  have hb : mu < 0 ∧ ∃ i, x.val i = 0 := ⟨hmu, j, hj⟩
  simp only [CESUtility, ite_eq_left hb]

/-- Each coordinate provides a linear upper bound for negative-exponent CES utility. -/
theorem cesUtility_le_coordinate {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 0) (x : NonnegativeOrthant k) (j : Fin k) :
    CESUtility a mu x ≤ a j ^ (1 / mu) * x.val j := by
  by_cases hb : ∃ i, x.val i = 0
  · obtain ⟨i, hi⟩ := hb
    rw [cesUtility_zero_of_coordinate a hmu hi]
    exact mul_nonneg (Real.rpow_pos_of_pos (ha j) _).le (x.property j)
  have hx : ∀ i, 0 < x.val i := fun i =>
    lt_of_le_of_ne (x.property i) (fun he => hb ⟨i, he.symm⟩)
  rw [cesUtility_of_positive a mu hx]
  have hterm : a j * x.val j ^ mu ≤ CESPowerSum a mu x :=
    Finset.single_le_sum (fun i _ =>
      mul_nonneg (ha i).le (Real.rpow_nonneg (x.property i) _)) (Finset.mem_univ j)
  calc
    CESPowerSum a mu x ^ (1 / mu) ≤ (a j * x.val j ^ mu) ^ (1 / mu) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _))
        hterm (one_div_neg.mpr hmu).le
    _ = a j ^ (1 / mu) * x.val j := by
      rw [Real.mul_rpow (ha j).le (Real.rpow_nonneg (x.property j) _),
        ← Real.rpow_mul (x.property j)]
      simp [hmu.ne]

/-- At an interior point the power sum is continuous for any real exponent. -/
theorem cesPowerSum_continuousAt_interior {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    ContinuousAt (CESPowerSum a mu) x := by
  have hc (j : Fin k) : ContinuousAt (fun z : NonnegativeOrthant k => z.val j ^ mu) x :=
    (((continuous_apply j).comp continuous_subtype_val).continuousAt).rpow_const
      (Or.inl (hx j).ne')
  unfold CESPowerSum
  fun_prop

/-- The full-domain CES formula is continuous at every strictly positive bundle. -/
theorem cesUtility_continuousAt_interior {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (mu : ℝ) {x : NonnegativeOrthant k} (hx : ∀ j, 0 < x.val j) :
    ContinuousAt (CESUtility a mu) x := by
  have hc := (cesPowerSum_continuousAt_interior a mu hx).rpow_const (p := 1 / mu)
    (Or.inl (cesPowerSum_pos a ha mu hx).ne')
  apply hc.congr
  have he : ∀ᶠ z : NonnegativeOrthant k in 𝓝 x, ∀ j, 0 < z.val j := by
    apply eventually_all.mpr
    intro j
    exact (isOpen_lt continuous_const ((continuous_apply j).comp continuous_subtype_val)).mem_nhds
      (hx j)
  filter_upwards [he] with z hz
  exact (cesUtility_of_positive a mu hz).symm

/-- The negative-exponent boundary extension is continuous at every absent commodity. -/
theorem cesUtility_continuousAt_boundary {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hmu : mu < 0) {x : NonnegativeOrthant k} {j : Fin k} (hj : x.val j = 0) :
    ContinuousAt (CESUtility a mu) x := by
  have hc : Continuous (fun z : NonnegativeOrthant k => a j ^ (1 / mu) * z.val j) :=
    continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  have hl : Tendsto (fun z : NonnegativeOrthant k => a j ^ (1 / mu) * z.val j)
      (𝓝 x) (𝓝 0) := by simpa only [hj, mul_zero] using hc.tendsto x
  change Tendsto (CESUtility a mu) (𝓝 x) (𝓝 (CESUtility a mu x))
  rw [cesUtility_zero_of_coordinate a hmu hj]
  exact squeeze_zero (cesUtility_nonneg a ha mu)
    (fun z => cesUtility_le_coordinate a ha hmu z j) hl

/-- CES utility is continuous on the full orthant for every nonzero real exponent. -/
theorem cesUtility_continuous {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) {mu : ℝ} (hm0 : mu ≠ 0) : Continuous (CESUtility a mu) := by
  rcases lt_or_gt_of_ne hm0 with hm | hm
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hb : ∃ j, x.val j = 0
    · obtain ⟨j, hj⟩ := hb
      exact cesUtility_continuousAt_boundary a ha hm hj
    · exact cesUtility_continuousAt_interior a ha mu
        (fun j => lt_of_le_of_ne (x.property j) (fun he => hb ⟨j, he.symm⟩))
  · have he : CESUtility a mu = fun x => CESPowerSum a mu x ^ (1 / mu) := by
      funext x
      simp [CESUtility, not_lt_of_ge hm.le]
    rw [he]
    apply Continuous.rpow_const _ (fun _ => Or.inr (one_div_pos.mpr hm).le)
    have hc (j : Fin k) : Continuous (fun x : NonnegativeOrthant k => x.val j ^ mu) :=
      (Real.continuous_rpow_const hm.le).comp
        ((continuous_apply j).comp continuous_subtype_val)
    unfold CESPowerSum
    fun_prop

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homothetic preference and income scaling of all demand

Kreps I, Problem 3.10(b), p. 65. Positive income scaling transports every
maximizer, and transports the full choice set bijectively. Zero target income is
handled separately; the origin at zero source income does not identify choices
at positive income. Neither continuity nor uniqueness is assumed.

The homotheticity definition and elementary scaling identities are selected
local copies from Chapter 2's `Homotheticity`, originating at commit `7d496c5`.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

variable {k : ℕ}

/-- Every common nonnegative scaling preserves weak preference. -/
def HomotheticPreference (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ x z t, r x z → r (ScaleBundle t x) (ScaleBundle t z)

/-- A zero scalar gives the zero commodity bundle. -/
theorem scaleBundle_zero_scalar (x : NonnegativeOrthant k) :
    ScaleBundle 0 x = ZeroBundle k := by
  apply Subtype.ext
  ext j
  simp [ScaleBundle, ZeroBundle]

/-- Successive scalings multiply their factors. -/
theorem scaleBundle_mul (a b : ℝ≥0) (x : NonnegativeOrthant k) :
    ScaleBundle (a * b) x = ScaleBundle a (ScaleBundle b x) := by
  apply Subtype.ext
  ext j
  simp [ScaleBundle, mul_assoc]

/-- Every positive scalar can be undone inside the consumption domain. -/
theorem scaleBundle_inv {a : ℝ≥0} (ha : a ≠ 0) (x : NonnegativeOrthant k) :
    ScaleBundle a⁻¹ (ScaleBundle a x) = x := by
  rw [← scaleBundle_mul, inv_mul_cancel₀ ha, scaleBundle_one]

/-- Positive scaling preserves and reflects weak preference. -/
theorem homothetic_scale_iff {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hh : HomotheticPreference r) {a : ℝ≥0} (ha : 0 < a) (x z : NonnegativeOrthant k) :
    r (ScaleBundle a x) (ScaleBundle a z) ↔ r x z := by
  refine ⟨fun h => ?_, hh x z a⟩
  simpa only [scaleBundle_inv ha.ne'] using hh _ _ a⁻¹ h

/-- Positive scaling exactly transports budget feasibility at fixed prices. -/
theorem mem_budgetSet_scale_bundle_iff (p : PositivePrices k) (y : ℝ≥0)
    {a : ℝ≥0} (ha : 0 < a) (x : NonnegativeOrthant k) :
    ScaleBundle a x ∈ BudgetSet p (a * y) ↔ x ∈ BudgetSet p y := by
  change Expenditure p (ScaleBundle a x) ≤ ((a * y : ℝ≥0) : ℝ) ↔ _
  rw [expenditure_scaleBundle, NNReal.coe_mul]
  exact mul_le_mul_iff_right₀ ha

/-- A chosen bundle stays chosen under a positive common scaling of consumption and income. -/
theorem homothetic_choice_scale_pos
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a)
    {x : NonnegativeOrthant k} (hx : x ∈ PrefChoice r (BudgetSet p y)) :
    ScaleBundle a x ∈ PrefChoice r (BudgetSet p (a * y)) := by
  refine ⟨(mem_budgetSet_scale_bundle_iff p y ha x).mpr hx.1, ?_⟩
  intro z hz
  have hz' : ScaleBundle a⁻¹ z ∈ BudgetSet p y := by
    have h := (mem_budgetSet_scale_bundle_iff p (a * y) (inv_pos.mpr ha) z).mpr hz
    simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using h
  have hr := hh x (ScaleBundle a⁻¹ z) a (hx.2 _ hz')
  rwa [← scaleBundle_mul, mul_inv_cancel₀ ha.ne', scaleBundle_one] at hr

/-- The scaled choice is optimal exactly when the original choice is optimal. -/
theorem homothetic_choice_scale_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a) (x : NonnegativeOrthant k) :
    ScaleBundle a x ∈ PrefChoice r (BudgetSet p (a * y)) ↔
      x ∈ PrefChoice r (BudgetSet p y) := by
  constructor
  · intro h
    have h' := homothetic_choice_scale_pos hh p (a * y) (inv_pos.mpr ha) h
    simpa [scaleBundle_inv ha.ne', ← mul_assoc, inv_mul_cancel₀ ha.ne'] using h'
  · exact homothetic_choice_scale_pos hh p y ha

/-- At positive incomes, the entire demand correspondence scales, including multiple maxima. -/
theorem homothetic_choice_set_scale
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y : ℝ≥0) {a : ℝ≥0} (ha : 0 < a) :
    PrefChoice r (BudgetSet p (a * y)) = ScaleBundle a '' PrefChoice r (BudgetSet p y) := by
  ext z
  constructor
  · intro hz
    refine ⟨ScaleBundle a⁻¹ z, ?_, ?_⟩
    · have h := homothetic_choice_scale_pos hh p (a * y) (inv_pos.mpr ha) hz
      simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using h
    · rw [← scaleBundle_mul, mul_inv_cancel₀ ha.ne', scaleBundle_one]
  · rintro ⟨x, hx, rfl⟩
    exact homothetic_choice_scale_pos hh p y ha hx

/-- **Problem 3.10(b):** from positive income, every chosen bundle scales by the income ratio. -/
theorem problem_3_10b
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hh : HomotheticPreference r)
    (p : PositivePrices k) (y y' : ℝ≥0) (hy : 0 < y)
    {x : NonnegativeOrthant k} (hx : x ∈ PrefChoice r (BudgetSet p y)) :
    ScaleBundle (y' / y) x ∈ PrefChoice r (BudgetSet p y') := by
  by_cases hy' : y' = 0
  · subst y'
    simp only [zero_div, scaleBundle_zero_scalar, budgetSet_zero]
    refine ⟨rfl, ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    simpa only [scaleBundle_zero_scalar] using hh x x 0 (hx.2 x hx.1)
  · have h := homothetic_choice_scale_pos hh p y (div_pos (pos_iff_ne_zero.mpr hy') hy) hx
    simpa only [div_mul_cancel₀ _ hy.ne'] using h

/-- Degree-one homogeneous utility represents homothetic preference, including at zero scale. -/
theorem homothetic_of_homogeneous {u : NonnegativeOrthant k → ℝ}
    (hu : ∀ a x, u (ScaleBundle a x) = (a : ℝ) * u x) : HomotheticPreference (UtilityPref u) := by
  intro x z a hxz
  change u (ScaleBundle a z) ≤ u (ScaleBundle a x)
  rw [hu, hu]
  exact mul_le_mul_of_nonneg_left hxz a.property

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homotheticity of CES preferences

Kreps I, Problems 3.7 and 3.10(a), pp. 64-65. CES utility is homogeneous of
degree one, including its zero boundary extension for negative exponents.
The resulting preference is homothetic for every nonnegative rescaling.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Scaling a commodity vector scales its power sum by the corresponding real power. -/
theorem cesPowerSum_scale {k : ℕ} (a : Fin k → ℝ) (mu : ℝ)
    (t : ℝ≥0) (x : NonnegativeOrthant k) :
    CESPowerSum a mu (ScaleBundle t x) = (t : ℝ) ^ mu * CESPowerSum a mu x := by
  simp only [CESPowerSum, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.mul_rpow (x := (t : ℝ)) (y := x.val j) (z := mu) t.property (x.property j)]
  ring

/-- The CES utility of the origin is zero for every nonzero exponent. -/
theorem cesUtility_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ) {mu : ℝ} (hm0 : mu ≠ 0) :
    CESUtility a mu (ZeroBundle k) = 0 := by
  by_cases hm : mu < 0
  · exact cesUtility_zero_of_coordinate a hm (j := ⟨0, NeZero.pos k⟩) rfl
  · simp [CESUtility, CESPowerSum, ZeroBundle, hm, Real.zero_rpow hm0,
      Real.zero_rpow (inv_ne_zero hm0)]

/-- Positive scaling preserves the CES formula on the full orthant. -/
theorem cesUtility_scale_pos {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) :
    CESUtility a mu (ScaleBundle t x) = (t : ℝ) * CESUtility a mu x := by
  have he : (∃ j, (ScaleBundle t x).val j = 0) ↔ ∃ j, x.val j = 0 := by
    simp only [ScaleBundle, mul_eq_zero, ht.ne', false_or]
  by_cases hb : mu < 0 ∧ ∃ j, x.val j = 0
  · have hb' : mu < 0 ∧ ∃ j, (ScaleBundle t x).val j = 0 := ⟨hb.1, he.mpr hb.2⟩
    simp only [CESUtility, ite_eq_left hb, ite_eq_left hb', mul_zero]
  · have hb' : ¬(mu < 0 ∧ ∃ j, (ScaleBundle t x).val j = 0) :=
      fun h => hb ⟨h.1, he.mp h.2⟩
    rw [CESUtility, ite_eq_right hb', CESUtility, ite_eq_right hb, cesPowerSum_scale,
      Real.mul_rpow (x := (t : ℝ) ^ mu) (y := CESPowerSum a mu x) (z := 1 / mu)
        (Real.rpow_nonneg t.property mu) (cesPowerSum_nonneg a ha mu x),
      ← Real.rpow_mul (x := (t : ℝ)) t.property]
    simp [hm0]

/-- CES utility is homogeneous of degree one, including at zero scale and zero quantities. -/
theorem cesUtility_scale {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) (t : ℝ≥0) (x : NonnegativeOrthant k) :
    CESUtility a mu (ScaleBundle t x) = (t : ℝ) * CESUtility a mu x := by
  by_cases ht : 0 < (t : ℝ)
  · exact cesUtility_scale_pos a ha hm0 t ht x
  · have he : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property)
    subst t
    rw [scaleBundle_zero_scalar, cesUtility_zero a hm0]
    simp

/-- **Problem 3.10(a), CES:** the nonzero-exponent CES utilities represent homothetic preference. -/
theorem cesUtility_homothetic {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    {mu : ℝ} (hm0 : mu ≠ 0) : HomotheticPreference (UtilityPref (CESUtility a mu)) :=
  homothetic_of_homogeneous (cesUtility_scale a ha hm0)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Linear utility and its complete demand correspondence

Kreps I, Problem 3.6(a), p. 64. Every optimal bundle spends the entire income
on goods with maximal utility per unit of expenditure. The characterization
retains the whole face of solutions when several goods tie, and includes zero
income. No differentiability or previously assumed maximizer is needed.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Linear utility with a separate coefficient for each commodity. -/
def LinearUtility {k : ℕ} (a : Fin k → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  ∑ j, a j * x.val j

/-- Linear utility is continuous, including on the boundary of the orthant. -/
theorem linearUtility_continuous {k : ℕ} (a : Fin k → ℝ) :
    Continuous (LinearUtility a) := by
  unfold LinearUtility
  exact continuous_finsetSum _ (fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_subtype_val))

/-- A single-good vertex has the corresponding utility per dollar times income. -/
theorem linearUtility_singleGoodBundle {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    LinearUtility a (SingleGoodBundle p y j) = (a j / p.val j) * (y : ℝ) := by
  simp only [LinearUtility, SingleGoodBundle, Pi.single_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- An upper bound on all utility-price ratios bounds every bundle's utility by its cost. -/
theorem linearUtility_le_ratio_expenditure {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (M : ℝ) (hM : ∀ j, a j / p.val j ≤ M)
    (x : NonnegativeOrthant k) : LinearUtility a x ≤ M * Expenditure p x := by
  calc
    LinearUtility a x ≤ ∑ j, (M * p.val j) * x.val j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (p.property j)).mp (hM j))
        (x.property j)
    _ = M * Expenditure p x := by simp [Expenditure, Finset.mul_sum, mul_assoc]

/-- A maximizing utility-price ratio exists because there are finitely many goods. -/
theorem exists_maximal_utility_price_ratio {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (p : PositivePrices k) : ∃ j, ∀ i, a i / p.val i ≤ a j / p.val j :=
  Finite.exists_max (fun j => a j / p.val j)

/-- Spending on a maximal-ratio good is optimal. -/
theorem singleGoodBundle_mem_linearDemand {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k)
    (hj : ∀ i, a i / p.val i ≤ a j / p.val j) :
    SingleGoodBundle p y j ∈ MarshallianDemand (LinearUtility a) p y := by
  refine ⟨singleGoodBundle_mem_budgetSet p y j, fun x hx => ?_⟩
  change LinearUtility a x ≤ LinearUtility a (SingleGoodBundle p y j)
  rw [linearUtility_singleGoodBundle]
  exact (linearUtility_le_ratio_expenditure a p _ hj x).trans
    (mul_le_mul_of_nonneg_left hx (div_pos (ha j) (p.property j)).le)

/-- **Problem 3.6(a):** the full demand face, including ties and zero income. -/
theorem problem_3_6a {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand (LinearUtility a) p y ↔
      Expenditure p x = (y : ℝ) ∧
        ∀ i, 0 < x.val i → ∀ j, a j / p.val j ≤ a i / p.val i := by
  obtain ⟨b, hb⟩ := exists_maximal_utility_price_ratio a p
  let M := a b / p.val b
  have hM : 0 < M := div_pos (ha b) (p.property b)
  have hcoeff (j : Fin k) : a j ≤ M * p.val j :=
    (div_le_iff₀ (p.property j)).mp (hb j)
  constructor
  · intro hx
    have hlow : M * (y : ℝ) ≤ LinearUtility a x := by
      simpa only [UtilityPref, linearUtility_singleGoodBundle] using
        hx.2 _ (singleGoodBundle_mem_budgetSet p y b)
    have hupp := linearUtility_le_ratio_expenditure a p M hb x
    have hcost : Expenditure p x = (y : ℝ) := by
      apply le_antisymm hx.1
      exact (mul_le_mul_iff_right₀ hM).mp (hlow.trans hupp)
    have hvalue : LinearUtility a x = M * (y : ℝ) :=
      le_antisymm (by rwa [hcost] at hupp) hlow
    have hgap : ∑ j, (M * p.val j - a j) * x.val j = 0 := by
      calc
        _ = M * Expenditure p x - LinearUtility a x := by
          simp [Expenditure, LinearUtility, sub_mul, Finset.sum_sub_distrib,
            Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [hcost, hvalue]; ring
    refine ⟨hcost, fun i hi j => ?_⟩
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => mul_nonneg (sub_nonneg.mpr (hcoeff l)) (x.property l))).mp
        hgap i (Finset.mem_univ i)
    have heq : a i / p.val i = M := by
      apply (div_eq_iff (ne_of_gt (p.property i))).mpr
      have := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hi)
      linarith
    rw [heq]
    exact hb j
  · rintro ⟨hcost, hsupp⟩
    have hvalue : LinearUtility a x = M * Expenditure p x := by
      rw [LinearUtility, Expenditure, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 < x.val i
      · have heq : a i / p.val i = M := le_antisymm (hb i) (hsupp i hi b)
        have hcoeffeq := (div_eq_iff (ne_of_gt (p.property i))).mp heq
        rw [hcoeffeq]
        ring
      · have hzero : x.val i = 0 := le_antisymm (le_of_not_gt hi) (x.property i)
        simp only [hzero, mul_zero]
    refine ⟨hcost.le, fun z hz => ?_⟩
    change LinearUtility a z ≤ LinearUtility a x
    rw [hvalue, hcost]
    exact (linearUtility_le_ratio_expenditure a p M hb z).trans
      (mul_le_mul_of_nonneg_left hz hM.le)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The linear and Cobb-Douglas limits of CES demand

Kreps I, Problem 3.7, pp. 64-65. At exponent one the entire linear-demand
face is retained, including ties. As the exponent approaches zero, the unique
CES demand converges to Cobb-Douglas expenditure shares. No normalization of
the positive coefficients is needed for this demand limit; a literal finite
limit of the unnormalized utility itself would need additional normalization.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal Topology
open Filter

/-- At exponent one CES utility is exactly linear utility, including on the boundary. -/
theorem cesUtility_one {k : ℕ} (a : Fin k → ℝ) : CESUtility a 1 = LinearUtility a := by
  funext x
  simp [CESUtility, CESPowerSum, LinearUtility]

/-- **Problem 3.7, exponent one:** all spending goes to goods with maximal utility-price ratio. -/
theorem problem_3_7_one {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand (CESUtility a 1) p y ↔
      Expenditure p x = (y : ℝ) ∧
        ∀ i, 0 < x.val i → ∀ j, a j / p.val j ≤ a i / p.val i := by
  rw [cesUtility_one]
  exact problem_3_6a a ha p y x

/-- The CES price-adjusted weights vary continuously with the exponent at zero. -/
theorem cesWeight_continuousAt_zero {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (j : Fin k) : ContinuousAt (fun mu => CESWeight a mu p j) 0 := by
  unfold CESWeight
  apply (Real.continuousAt_const_rpow (div_pos (ha j) (p.property j)).ne').comp
  exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)

/-- At exponent zero, the denominator of the demand formula is the sum of coefficients. -/
theorem cesDenominator_zero {k : ℕ} (a : Fin k → ℝ) (p : PositivePrices k) :
    CESDenominator a 0 p = ∑ j, a j := by
  unfold CESDenominator CESWeight
  simp only [sub_zero, div_one, Real.rpow_one]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(p.property j).ne']

/-- The CES denominator is continuous in the exponent at zero. -/
theorem cesDenominator_continuousAt_zero {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) :
    ContinuousAt (fun mu => CESDenominator a mu p) 0 := by
  have hw := cesWeight_continuousAt_zero a ha p
  unfold CESDenominator
  fun_prop

/-- The continuous extension of the CES demand formula at zero is the Cobb-Douglas formula. -/
theorem cesBundle_at_zero_exponent {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    CESBundle a ha 0 p y = CobbDouglasBundle a ha p y := by
  apply Subtype.ext
  funext j
  simp only [CESBundle, CESWeight, cesDenominator_zero, CobbDouglasBundle,
    sub_zero, div_one, Real.rpow_one]
  ring

/-- **Problem 3.7, zero limit:** the actual CES demand quantities converge to Cobb-Douglas. -/
theorem problem_3_7_zero_limit {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Tendsto (fun mu => (CESBundle a ha mu p y).val) (𝓝 0)
      (𝓝 (CobbDouglasBundle a ha p y).val) := by
  rw [← cesBundle_at_zero_exponent a ha p y]
  apply tendsto_pi_nhds.mpr
  intro j
  apply ContinuousAt.tendsto
  exact (continuousAt_const.div (cesDenominator_continuousAt_zero a ha p)
    (cesDenominator_pos a ha 0 p).ne').mul (cesWeight_continuousAt_zero a ha p j)

/-- The limit also holds along precisely the admissible nonzero CES exponents below one. -/
theorem cesDemand_tendsto_cobbDouglas {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Tendsto (fun mu => (CESBundle a ha mu p y).val)
      (𝓝[{mu : ℝ | mu < 1 ∧ mu ≠ 0}] 0) (𝓝 (CobbDouglasBundle a ha p y).val) :=
  (problem_3_7_zero_limit a ha p y).mono_left nhdsWithin_le_nhds

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One-sided derivatives of a capped absolute value

The piecewise linear coordinate slices used for Problem 3.13 have finite
one-sided derivatives everywhere. Writing the cap as the difference of two
convex real functions lets Mathlib's convex one-sided derivative theorem
handle all kink locations, including coincident kinks.
-/

namespace Kreps.ConsumerDemand

open Set

/-- A capped absolute value is a difference of two convex functions. -/
theorem cappedAbs_eq_difference (b c t : ℝ) :
    min |t - b| c = |t - b| - max (|t - b| - c) 0 := by
  by_cases h : |t - b| ≤ c
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

/-- Both one-sided derivatives of a capped absolute value exist at every real point. -/
theorem cappedAbs_one_sided (b c t : ℝ) :
    DifferentiableWithinAt ℝ (fun r => min |r - b| c) (Iic t) t ∧
      DifferentiableWithinAt ℝ (fun r => min |r - b| c) (Ici t) t := by
  have hf : ConvexOn ℝ univ (fun r : ℝ => |r - b|) := by
    simpa only [Real.dist_eq] using convexOn_univ_dist b
  have hg : ConvexOn ℝ univ (fun r : ℝ => max (|r - b| - c) 0) := by
    convert! (hf.add_const (-c)).sup (convexOn_const (0 : ℝ) convex_univ) using 1
  have hmem : t ∈ interior (univ : Set ℝ) := by simp
  constructor
  · have hd := (hf.hasDerivWithinAt_leftDeriv_of_mem_interior hmem).sub
      (hg.hasDerivWithinAt_leftDeriv_of_mem_interior hmem)
    convert! hd.Iic_of_Iio.differentiableWithinAt using 1
    funext r
    exact cappedAbs_eq_difference b c r
  · have hd := (hf.hasDerivWithinAt_rightDeriv_of_mem_interior hmem).sub
      (hg.hasDerivWithinAt_rightDeriv_of_mem_interior hmem)
    convert! hd.Ici_of_Ioi.differentiableWithinAt using 1
    funext r
    exact cappedAbs_eq_difference b c r

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Budget-preserving commodity transfers

Kreps I, pp. 61-62. Moving expenditure from a consumed good to another good
preserves cost and remains nonnegative for a suitably small transfer. The actual
within-domain derivative along that path is the difference of marginal utilities
per dollar. This uses a multivariate derivative, not merely coordinate partials.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- One dollar moved from good `j` to good `i`, expressed as a commodity direction. -/
noncomputable def TransferDirection {k : ℕ} (p : PositivePrices k) (i j : Fin k) : Fin k → ℝ :=
  (1 / p.val i) • Pi.single i 1 - (1 / p.val j) • Pi.single j 1

/-- Every expenditure transfer has zero net cost. -/
theorem transferDirection_cost {k : ℕ} (p : PositivePrices k) (i j : Fin k) :
    (∑ l, p.val l * TransferDirection p i j l) = 0 := by
  simp [TransferDirection, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
    ne_of_gt (p.property i), ne_of_gt (p.property j)]

/-- Transferring no more than the original expenditure on the donor good is nonnegative. -/
theorem transfer_nonnegative {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) {d : ℝ} (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    0 ≤ x.val + d • TransferDirection p i j := by
  intro l
  by_cases hli : l = i
  · subst l
    have h : 0 ≤ d / p.val i := div_nonneg hd (p.property i).le
    simpa [TransferDirection, Pi.single_apply, hij, Ne.symm hij, div_eq_mul_inv] using
      add_nonneg (x.property i) h
  · by_cases hlj : l = j
    · subst l
      have h : d / p.val j ≤ x.val j :=
        (div_le_iff₀ (p.property j)).mpr (by simpa only [mul_comm] using hb)
      simpa [TransferDirection, Pi.single_apply, hij, Ne.symm hij, div_eq_mul_inv] using
        sub_nonneg.mpr h
    · simpa [TransferDirection, Pi.single_apply, hli, hlj] using x.property l

/-- A feasible commodity transfer as a nonnegative consumption bundle. -/
noncomputable def TransferBundle {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    NonnegativeOrthant k := ⟨x.val + d • TransferDirection p i j,
      transfer_nonnegative p x i j hij hd hb⟩

/-- The actual nonnegative transfer bundle has exactly the original expenditure. -/
theorem expenditure_transferBundle {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    Expenditure p (TransferBundle p x i j hij d hd hb) = Expenditure p x := by
  have he : Expenditure p (TransferBundle p x i j hij d hd hb) =
      Expenditure p x + d * (∑ l, p.val l * TransferDirection p i j l) := by
    simp only [Expenditure, TransferBundle, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he, transferDirection_cost, mul_zero, add_zero]

/-- The expenditure transfer preserves budget feasibility. -/
theorem transferBundle_mem_budget {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ BudgetSet p y) (i j : Fin k) (hij : i ≠ j)
    (d : ℝ) (hd : 0 ≤ d) (hb : d ≤ p.val j * x.val j) :
    TransferBundle p x i j hij d hd hb ∈ BudgetSet p y := by
  change Expenditure p (TransferBundle p x i j hij d hd hb) ≤ (y : ℝ)
  rwa [expenditure_transferBundle]

/-- Evaluating a linear derivative on the exchange gives the marginal-return difference. -/
theorem derivative_transferDirection {k : ℕ} (D : (Fin k → ℝ) →L[ℝ] ℝ)
    (p : PositivePrices k) (i j : Fin k) :
    D (TransferDirection p i j) =
      MarginalUtility D i / p.val i - MarginalUtility D j / p.val j := by
  simp [TransferDirection, MarginalUtility, map_sub, map_smul, div_eq_mul_inv, mul_comm]

/-- The actual right derivative on a short exchange segment equals the marginal-return gap. -/
theorem utility_transfer_derivative {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) {b : ℝ} (hb : b ≤ p.val j * x.val j)
    (hd : HasFDerivWithinAt u D (Set.Ici 0) x.val) :
    HasDerivWithinAt (fun d : ℝ => u (x.val + d • TransferDirection p i j))
      (MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) (Set.Icc 0 b) 0 := by
  have hp : HasDerivAt (fun d : ℝ => x.val + d • TransferDirection p i j)
      (TransferDirection p i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (TransferDirection p i j)).const_add x.val
  have hm : Set.MapsTo (fun d : ℝ => x.val + d • TransferDirection p i j)
      (Set.Icc 0 b) (Set.Ici 0) :=
    fun _ ht => transfer_nonnegative p x i j hij ht.1 (ht.2.trans hb)
  have h := hd.comp_hasDerivWithinAt_of_eq 0 hp.hasDerivWithinAt hm (by simp)
  rwa [derivative_transferDirection] at h

/-- A positive marginal-return gap yields an actual utility-improving affordable transfer. -/
theorem exists_improving_commodity_transfer {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (x : NonnegativeOrthant k)
    (i j : Fin k) (hij : i ≠ j) (hj : 0 < x.val j)
    (hd : HasFDerivWithinAt u D (Set.Ici 0) x.val)
    (hgap : 0 < MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) :
    ∃ d : ℝ, 0 < d ∧ d ≤ p.val j * x.val j ∧
      u x.val < u (x.val + d • TransferDirection p i j) := by
  let b := p.val j * x.val j
  have hb : 0 < b := mul_pos (p.property j) hj
  have hder := utility_transfer_derivative p x i j hij (le_refl b) hd
  by_contra! hn
  have hmax : IsMaxOn (fun d : ℝ => u (x.val + d • TransferDirection p i j))
      (Set.Icc 0 b) 0 := by
    intro d hd'
    change u (x.val + d • TransferDirection p i j) ≤ u (x.val + 0 • TransferDirection p i j)
    simp only [zero_smul, add_zero]
    by_cases hzero : d = 0
    · simp [hzero]
    · have hpos : 0 < d := lt_of_le_of_ne hd'.1 (Ne.symm hzero)
      exact hn d hpos hd'.2
  have hfirst := convex_firstOrderNecessary hmax hder.hasFDerivWithinAt (Set.Subset.refl _)
    (convex_Icc _ _) (show 0 ∈ Set.Icc (0 : ℝ) b from ⟨le_rfl, hb.le⟩)
    b ⟨hb.le, le_rfl⟩
  have hnonpos : b * (MarginalUtility D i / p.val i - MarginalUtility D j / p.val j) ≤ 0 := by
    simpa using hfirst
  exact not_lt_of_ge hnonpos (mul_pos hb hgap)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Constructed witnesses for Figure 3.2

Kreps I, Figure 3.2(a-c), p. 53. The book gives pictures, not the utility
formulas used here. These explicitly constructed two-good examples realize
two separated optima, a convex continuum of optima, and a unique satiation
bundle with slack expenditure, respectively.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- Equal unit prices for the constructed two-good illustrations. -/
def IllustrationPrices : PositivePrices 2 := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- The first single-good unit bundle. -/
def IllustrationFirst : NonnegativeOrthant 2 :=
  ⟨![1, 0], fun j => by fin_cases j <;> norm_num⟩

/-- The second single-good unit bundle. -/
def IllustrationSecond : NonnegativeOrthant 2 :=
  ⟨![0, 1], fun j => by fin_cases j <;> norm_num⟩

/-- A satiation bundle strictly inside the income-three budget. -/
def IllustrationSatiation : NonnegativeOrthant 2 :=
  ⟨![1, 1], fun j => by fin_cases j <;> norm_num⟩

/-- Constructed utility for the two separated solutions in Figure 3.2(a). -/
def SeparatedOptimaUtility (x : NonnegativeOrthant 2) : ℝ := x.val 0 ^ 2 + x.val 1 ^ 2

/-- Constructed utility for the interior satiation example in Figure 3.2(c). -/
def SatiationUtility (x : NonnegativeOrthant 2) : ℝ :=
  -((x.val 0 - 1) ^ 2 + (x.val 1 - 1) ^ 2)

/-- At unit prices expenditure is the sum of the two commodity quantities. -/
theorem illustration_expenditure (x : NonnegativeOrthant 2) :
    Expenditure IllustrationPrices x = x.val 0 + x.val 1 := by
  simp [Expenditure, IllustrationPrices, Fin.sum_univ_succ]

/-- Every feasible bundle has squared-sum utility at most one. -/
theorem separatedOptimaUtility_le_one {x : NonnegativeOrthant 2}
    (hx : x ∈ BudgetSet IllustrationPrices 1) : SeparatedOptimaUtility x ≤ 1 := by
  have hbudget : x.val 0 + x.val 1 ≤ 1 := by
    simpa only [BudgetSet, Set.mem_ofPred_eq, illustration_expenditure, NNReal.coe_one] using hx
  have h0 : 0 ≤ x.val 0 := x.property 0
  have h1 : 0 ≤ x.val 1 := x.property 1
  have h01 : x.val 0 ≤ 1 := by linarith
  have h11 : x.val 1 ≤ 1 := by linarith
  dsimp only [SeparatedOptimaUtility]
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h01), mul_nonneg h1 (sub_nonneg.mpr h11)]

/-- **Figure 3.2(a), constructed witness:** exactly the two distinct corner bundles are optimal. -/
theorem figure_3_2a_demand :
    MarshallianDemand SeparatedOptimaUtility IllustrationPrices 1 =
      {IllustrationFirst, IllustrationSecond} := by
  have hfirst : IllustrationFirst ∈ BudgetSet IllustrationPrices 1 := by
    norm_num [BudgetSet, illustration_expenditure, IllustrationFirst]
  have hsecond : IllustrationSecond ∈ BudgetSet IllustrationPrices 1 := by
    norm_num [BudgetSet, illustration_expenditure, IllustrationSecond]
  apply Set.Subset.antisymm
  · intro x hx
    have hlow : 1 ≤ SeparatedOptimaUtility x := by
      simpa [UtilityPref, SeparatedOptimaUtility, IllustrationFirst] using hx.2 _ hfirst
    have heq : x.val 0 ^ 2 + x.val 1 ^ 2 = 1 :=
      le_antisymm (separatedOptimaUtility_le_one hx.1) hlow
    have hbudget : x.val 0 + x.val 1 ≤ 1 := by
      simpa only [BudgetSet, Set.mem_ofPred_eq, illustration_expenditure, NNReal.coe_one]
        using hx.1
    have h0 : 0 ≤ x.val 0 := x.property 0
    have h1 : 0 ≤ x.val 1 := x.property 1
    have hprod : x.val 0 * x.val 1 = 0 := by
      nlinarith [mul_nonneg h0 h1,
        mul_nonneg (add_nonneg h0 h1) (sub_nonneg.mpr hbudget)]
    rcases mul_eq_zero.mp hprod with hz | hz
    · right
      apply Set.mem_singleton_iff.mpr
      have hone : x.val 1 = 1 := by nlinarith
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [IllustrationSecond, hz, hone]
    · left
      have hone : x.val 0 = 1 := by nlinarith
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [IllustrationFirst, hz, hone]
  · intro x hx
    rcases hx with rfl | hx
    · refine ⟨hfirst, fun z hz => ?_⟩
      simpa [UtilityPref, SeparatedOptimaUtility, IllustrationFirst] using
        separatedOptimaUtility_le_one hz
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨hsecond, fun z hz => ?_⟩
      simpa [UtilityPref, SeparatedOptimaUtility, IllustrationSecond] using
        separatedOptimaUtility_le_one hz

/-- **Figure 3.2(b), constructed witness:** every point of the budget line is demanded. -/
theorem figure_3_2b_demand :
    MarshallianDemand (LinearUtility (fun _ : Fin 2 => 1)) IllustrationPrices 1 =
      {x | x.val 0 + x.val 1 = 1} := by
  ext x
  rw [problem_3_6a _ (fun _ => zero_lt_one)]
  simp [Expenditure, IllustrationPrices, Fin.sum_univ_succ]

/-- The satiation utility is globally no greater than its value zero at the satiation bundle. -/
theorem satiationUtility_le_zero (x : NonnegativeOrthant 2) : SatiationUtility x ≤ 0 := by
  dsimp only [SatiationUtility]
  nlinarith [sq_nonneg (x.val 0 - 1), sq_nonneg (x.val 1 - 1)]

/-- **Figure 3.2(c), constructed witness:** satiation is the unique optimum. -/
theorem figure_3_2c_demand :
    MarshallianDemand SatiationUtility IllustrationPrices 3 = {IllustrationSatiation} := by
  have hfeas : IllustrationSatiation ∈ BudgetSet IllustrationPrices 3 := by
    norm_num [BudgetSet, illustration_expenditure, IllustrationSatiation]
  apply Set.Subset.antisymm
  · intro x hx
    have hlow : 0 ≤ SatiationUtility x := by
      simpa [UtilityPref, SatiationUtility, IllustrationSatiation] using hx.2 _ hfeas
    have h0 : x.val 0 = 1 := by
      dsimp only [SatiationUtility] at hlow
      nlinarith [sq_nonneg (x.val 0 - 1), sq_nonneg (x.val 1 - 1)]
    have h1 : x.val 1 = 1 := by
      dsimp only [SatiationUtility] at hlow
      nlinarith [sq_nonneg (x.val 0 - 1), sq_nonneg (x.val 1 - 1)]
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [IllustrationSatiation, h0, h1]
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨hfeas, fun z _ => ?_⟩
    simpa [UtilityPref, SatiationUtility, IllustrationSatiation] using satiationUtility_le_zero z

/-- The unique satiation optimum spends strictly less than income. -/
theorem figure_3_2c_slack : Expenditure IllustrationPrices IllustrationSatiation < (3 : ℝ) := by
  norm_num [illustration_expenditure, IllustrationSatiation]

/-- Both constructed single-good optima are distinct points. -/
theorem illustration_vertices_ne : IllustrationFirst ≠ IllustrationSecond := by
  intro h
  have he := congrArg (fun x : NonnegativeOrthant 2 => x.val 0) h
  norm_num [IllustrationFirst, IllustrationSecond] at he

/-- The separated-optima example has continuous utility. -/
theorem separatedOptimaUtility_continuous : Continuous SeparatedOptimaUtility := by
  have hc (i : Fin 2) : Continuous (fun x : NonnegativeOrthant 2 => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact ((hc 0).pow 2).add ((hc 1).pow 2)

/-- The separated-optima example has nonconvex preferences, as in panel (a). -/
theorem figure_3_2a_not_convex :
    ¬ConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 2 → ℝ))
      (UtilityPref SeparatedOptimaUtility) := by
  intro hc
  have h := hc IllustrationFirst IllustrationSecond
    (by norm_num [UtilityPref, SeparatedOptimaUtility, IllustrationFirst, IllustrationSecond])
    (1 / 2) (by constructor <;> norm_num)
  norm_num [UtilityPref, SeparatedOptimaUtility, IllustrationFirst, IllustrationSecond, Mix] at h

/-- Linear preferences in panel (b) are convex. -/
theorem figure_3_2b_convex :
    ConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 2 → ℝ))
      (UtilityPref (LinearUtility (fun _ => 1))) := by
  intro x z hx a ha
  norm_num [UtilityPref, LinearUtility, Mix, Fin.sum_univ_succ] at hx ⊢
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx)]

/-- The same linear preferences are not strictly convex, as in panel (b). -/
theorem figure_3_2b_not_strictlyConvex :
    ¬StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 2 → ℝ))
      (UtilityPref (LinearUtility (fun _ => 1))) := by
  intro hc
  have h := hc IllustrationFirst IllustrationSecond illustration_vertices_ne
    (by norm_num [UtilityPref, LinearUtility, IllustrationFirst, IllustrationSecond,
      Fin.sum_univ_succ]) (1 / 2) (by constructor <;> norm_num)
  norm_num [Strict, UtilityPref, LinearUtility, IllustrationFirst, IllustrationSecond,
    Fin.sum_univ_succ, Mix] at h

/-- The interior satiation example has continuous utility. -/
theorem satiationUtility_continuous : Continuous SatiationUtility := by
  have hc (i : Fin 2) : Continuous (fun x : NonnegativeOrthant 2 => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact (((hc 0).sub continuous_const).pow 2 |>.add
    (((hc 1).sub continuous_const).pow 2)).neg

/-- Satiation directly contradicts local insatiability, as in panel (c). -/
theorem figure_3_2c_not_locallyInsatiable : ¬LocallyInsatiable (UtilityPref SatiationUtility) := by
  intro hl
  obtain ⟨z, _, hbetter⟩ := hl IllustrationSatiation 1 zero_lt_one
  apply hbetter.2
  change SatiationUtility z ≤ SatiationUtility IllustrationSatiation
  simpa [SatiationUtility, IllustrationSatiation] using satiationUtility_le_zero z

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence of the shifted-product expenditure multiplier

Kreps I, Problem 3.5, p. 64. For positive income, the continuous expenditure
curve obtained by truncating negative commodity expenditures crosses income
at a strictly positive multiplier. Explicit upper and lower brackets establish
existence without assuming the desired demand or multiplier in advance.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Total spending prescribed by the marginal multiplier, with negative demands truncated. -/
noncomputable def WaterfillCost {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : ℝ := ∑ j, max (a j / l - p.val j * γ j) 0

/-- The expenditure curve is continuous on every closed interval of positive multipliers. -/
theorem waterfillCost_continuousOn {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    {lo hi : ℝ} (hlo : 0 < lo) : ContinuousOn (WaterfillCost a γ p) (Set.Icc lo hi) := by
  apply continuousOn_finsetSum
  intro j _
  have hdiv : ContinuousOn (fun l : ℝ => a j / l) (Set.Icc lo hi) :=
    continuousOn_const.div continuousOn_id (fun _ hl => ne_of_gt (hlo.trans_le hl.1))
  exact (hdiv.sub continuousOn_const).sup continuousOn_const

/-- Dropping the truncation gives a useful lower bound on prescribed expenditure. -/
theorem waterfillCost_lower_bound {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : (∑ j, a j) / l - ∑ j, p.val j * γ j ≤ WaterfillCost a γ p l := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun j _ => le_max_left _ _)

/-- Nonnegative shifts make prescribed expenditure no greater than the unshifted total. -/
theorem waterfillCost_upper_bound {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) {l : ℝ} (hl : 0 < l) :
    WaterfillCost a γ p l ≤ (∑ j, a j) / l := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  exact max_le (sub_le_self _ (mul_nonneg (p.property j).le (hγ j))) (div_pos (ha j) hl).le

/-- The multiplier equation always has a positive solution at positive income. -/
theorem exists_waterfill_multiplier {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ l : ℝ, 0 < l ∧ WaterfillCost a γ p l = (y : ℝ) := by
  let A := ∑ j, a j
  let C := ∑ j, p.val j * γ j
  have hA : 0 < A := exponent_sum_pos a ha
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j))
  let lo := A / ((y : ℝ) + C + 1)
  let hi := A / (y : ℝ)
  have hden : 0 < (y : ℝ) + C + 1 := by positivity
  have hlo : 0 < lo := div_pos hA hden
  have hhi : 0 < hi := div_pos hA hy
  have horder : lo ≤ hi := div_le_div_of_nonneg_left hA.le hy (by linarith)
  have helo : A / lo = (y : ℝ) + C + 1 := by
    dsimp only [lo]
    field_simp
  have hehi : A / hi = (y : ℝ) := by
    dsimp only [hi]
    field_simp
  have hlow : (y : ℝ) ≤ WaterfillCost a γ p lo := by
    have h := waterfillCost_lower_bound a γ p lo
    change A / lo - C ≤ _ at h
    rw [helo] at h
    linarith
  have hhigh : WaterfillCost a γ p hi ≤ (y : ℝ) := by
    have h := waterfillCost_upper_bound a γ ha hγ p hhi
    change _ ≤ A / hi at h
    rwa [hehi] at h
  obtain ⟨l, hl, hvalue⟩ := intermediate_value_Icc' horder
    (waterfillCost_continuousOn a γ p hlo) ⟨hhigh, hlow⟩
  exact ⟨l, hlo.trans_le hl.1, hvalue⟩

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The shifted-product demand procedure

Kreps I, Problem 3.5, p. 64. Solve the expenditure equation for a positive
multiplier, then truncate each prescribed quantity at zero. The resulting
bundle is the unique optimum for positive exponents and nonnegative shifts,
including zero shifts and corner solutions. Existence of the multiplier is
proved in `WaterfillingMultiplier`; zero income is treated separately.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The quantity formula from the shifted-product multiplier procedure. -/
noncomputable def WaterfillBundle {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k)
    (l : ℝ) : NonnegativeOrthant k :=
  ⟨fun j => max (a j / (l * p.val j) - γ j) 0, fun _ => le_max_right _ _⟩

/-- Commodity expenditure is the positive part of its untruncated expenditure. -/
theorem waterfillBundle_commodity_cost {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) (j : Fin k) :
    p.val j * (WaterfillBundle a γ p l).val j = max (a j / l - p.val j * γ j) 0 := by
  dsimp only [WaterfillBundle]
  rw [mul_max_of_nonneg _ _ (p.property j).le, mul_zero]
  congr 1
  field_simp [ne_of_gt (p.property j)]

/-- Total expenditure of the proposed bundle is the multiplier's expenditure curve. -/
theorem expenditure_waterfillBundle {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) :
    Expenditure p (WaterfillBundle a γ p l) = WaterfillCost a γ p l := by
  exact Finset.sum_congr rfl (fun j _ => waterfillBundle_commodity_cost a γ p l j)

/-- Every shifted quantity of the candidate is positive, even when some shifts are zero. -/
theorem waterfillBundle_shifted_pos {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k) :
    0 < (WaterfillBundle a γ p l).val j + γ j := by
  have hdiv := div_pos (ha j) (mul_pos hl (p.property j))
  have hmax := le_max_left (a j / (l * p.val j) - γ j) 0
  change 0 < max (a j / (l * p.val j) - γ j) 0 + γ j
  linarith

/-- Prescribed marginal utility per dollar never exceeds the multiplier. -/
theorem waterfillBundle_marginal_le {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k) :
    LogMarginals a γ (WaterfillBundle a γ p l) j ≤ l * p.val j := by
  apply (div_le_iff₀ (waterfillBundle_shifted_pos a γ ha p hl j)).mpr
  have hmax := le_max_left (a j / (l * p.val j) - γ j) 0
  have hbound : a j / (l * p.val j) ≤ (WaterfillBundle a γ p l).val j + γ j := by
    change a j / (l * p.val j) ≤ max (a j / (l * p.val j) - γ j) 0 + γ j
    linarith
  have h := (div_le_iff₀ (mul_pos hl (p.property j))).mp hbound
  simpa only [mul_comm] using h

/-- A consumed good has marginal utility per dollar exactly equal to the multiplier. -/
theorem waterfillBundle_marginal_eq {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) {l : ℝ} (hl : 0 < l) (j : Fin k)
    (hj : 0 < (WaterfillBundle a γ p l).val j) :
    LogMarginals a γ (WaterfillBundle a γ p l) j = l * p.val j := by
  have hinside : 0 < a j / (l * p.val j) - γ j :=
    (lt_max_iff.mp hj).resolve_right (lt_irrefl 0)
  have hx : (WaterfillBundle a γ p l).val j = a j / (l * p.val j) - γ j :=
    max_eq_left hinside.le
  dsimp only [LogMarginals]
  rw [hx, sub_add_cancel]
  field_simp [ne_of_gt (ha j)]

/-- Solving the expenditure equation verifies all logarithmic optimality conditions. -/
theorem waterfillBundle_optimality {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) {l : ℝ} (hl : 0 < l)
    (he : WaterfillCost a γ p l = (y : ℝ)) :
    CombinedOptimality p y (WaterfillBundle a γ p l)
      (LogMarginals a γ (WaterfillBundle a γ p l)) := by
  have hcost : Expenditure p (WaterfillBundle a γ p l) = (y : ℝ) :=
    (expenditure_waterfillBundle a γ p l).trans he
  refine ⟨hcost.le, l, hl.le, waterfillBundle_marginal_le a γ ha p hl,
    waterfillBundle_marginal_eq a γ ha p hl, ?_⟩
  rw [hcost]
  exact fun h => False.elim (lt_irrefl _ h)

/-- Any positive root of the expenditure equation gives the entire demand singleton. -/
theorem shiftedProduct_demand_of_waterfill {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0)
    {l : ℝ} (hl : 0 < l) (he : WaterfillCost a γ p l = (y : ℝ)) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y = {WaterfillBundle a γ p l} :=
  shiftedCobbDouglas_demand_of_optimality a γ ha hγ
    (waterfillBundle_shifted_pos a γ ha p hl)
    (waterfillBundle_optimality a γ ha p y hl he)

/-- **Problem 3.5:** the multiplier procedure exists and yields the unique demand. -/
theorem problem_3_5 {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) : ∃ l : ℝ, 0 < l ∧ WaterfillCost a γ p l = (y : ℝ) ∧
      MarshallianDemand (ShiftedCobbDouglas a γ) p y = {WaterfillBundle a γ p l} := by
  obtain ⟨l, hl, he⟩ := exists_waterfill_multiplier a γ ha hγ p y hy
  exact ⟨l, hl, he, shiftedProduct_demand_of_waterfill a γ ha hγ p y hl he⟩

/-- At zero income the shifted-product problem retains the unique feasible origin. -/
theorem problem_3_5_zero {k : ℕ} (a γ : Fin k → ℝ) (p : PositivePrices k) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p 0 = {ZeroBundle k} :=
  marshallianDemand_zero _ p

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A finite algebraic procedure for shifted-product demand

Kreps I, Problem 3.5, p. 64. For each nonempty subset of goods, compute the
ratio of its total exponents to income plus its shifted expenditure. Keep the
candidate exactly when its strict positive-demand set is that subset. At least
one of these finitely many candidates passes, and every passing candidate gives
the unique demand. Equality at a threshold correctly leaves a good unconsumed.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The goods with strictly positive prescribed consumption. -/
noncomputable def WaterfillActiveSet {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun j => p.val j * γ j < a j / l)

/-- The algebraic candidate multiplier for a proposed active set. -/
noncomputable def ActiveSetMultiplier {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (A : Finset (Fin k)) : ℝ :=
  (∑ j ∈ A, a j) / ((y : ℝ) + ∑ j ∈ A, p.val j * γ j)

/-- The expenditure curve is the sum of untruncated expenditures over its active set. -/
theorem waterfillCost_eq_active_sum {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (l : ℝ) :
    WaterfillCost a γ p l =
      (∑ j ∈ WaterfillActiveSet a γ p l, a j) / l -
        ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold WaterfillActiveSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p.val j * γ j < a j / l
  · simp only [hj, ite_true, max_eq_left (sub_pos.mpr hj).le]
  · simp only [hj, ite_false, max_eq_right (sub_nonpos.mpr (le_of_not_gt hj))]

/-- A positive-income solution has at least one strictly consumed good. -/
theorem waterfillActiveSet_nonempty {k : ℕ} (a γ : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) {l : ℝ}
    (he : WaterfillCost a γ p l = (y : ℝ)) : (WaterfillActiveSet a γ p l).Nonempty := by
  by_contra h
  have hempty := Finset.not_nonempty_iff_eq_empty.mp h
  have hcost := waterfillCost_eq_active_sum a γ p l
  rw [hempty] at hcost
  simp only [Finset.sum_empty, zero_div, sub_zero] at hcost
  linarith

/-- Every positive root is exactly the algebraic candidate of its active set. -/
theorem waterfill_multiplier_eq_active_candidate {k : ℕ} (a γ : Fin k → ℝ)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {l : ℝ} (hl : 0 < l) (he : WaterfillCost a γ p l = (y : ℝ)) :
    l = ActiveSetMultiplier a γ p y (WaterfillActiveSet a γ p l) := by
  have hC : 0 ≤ ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j))
  have hden : 0 < (y : ℝ) + ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j :=
    add_pos_of_pos_of_nonneg hy hC
  have hc := waterfillCost_eq_active_sum a γ p l
  rw [he] at hc
  have hsum : (∑ j ∈ WaterfillActiveSet a γ p l, a j) / l =
      (y : ℝ) + ∑ j ∈ WaterfillActiveSet a γ p l, p.val j * γ j := by linarith
  have heq := (div_eq_iff (ne_of_gt hl)).mp hsum
  apply Eq.symm
  apply (div_eq_iff (ne_of_gt hden)).mpr
  nlinarith

/-- A nonempty proposed active set yields a positive candidate multiplier. -/
theorem activeSetMultiplier_pos {k : ℕ} (a γ : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    (A : Finset (Fin k)) (hA : A.Nonempty) : 0 < ActiveSetMultiplier a γ p y A := by
  apply div_pos (Finset.sum_pos (fun j _ => ha j) hA)
  exact add_pos_of_pos_of_nonneg hy
    (Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (hγ j)))

/-- A candidate passing the active-set test solves the expenditure equation. -/
theorem active_candidate_solves_expenditure {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k)
    (y : ℝ≥0) (A : Finset (Fin k)) (hA : A.Nonempty)
    (htest : WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A) :
    WaterfillCost a γ p (ActiveSetMultiplier a γ p y A) = (y : ℝ) := by
  rw [waterfillCost_eq_active_sum, htest]
  have hsum : 0 < ∑ j ∈ A, a j := Finset.sum_pos (fun j _ => ha j) hA
  unfold ActiveSetMultiplier
  field_simp
  ring

/-- **Problem 3.5, finite procedure:** a nonempty subset always passes the algebraic test. -/
theorem problem_3_5_finite_candidates {k : ℕ} [NeZero k] (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃ A : Finset (Fin k), A.Nonempty ∧
      WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A ∧
      MarshallianDemand (ShiftedCobbDouglas a γ) p y =
        {WaterfillBundle a γ p (ActiveSetMultiplier a γ p y A)} := by
  obtain ⟨l, hl, he⟩ := exists_waterfill_multiplier a γ ha hγ p y hy
  have heq := waterfill_multiplier_eq_active_candidate a γ hγ p y hy hl he
  refine ⟨WaterfillActiveSet a γ p l, waterfillActiveSet_nonempty a γ p y hy he, ?_, ?_⟩
  · rw [← heq]
  · rw [← heq]
    exact shiftedProduct_demand_of_waterfill a γ ha hγ p y hl he

/-- Every nonempty subset that passes the finite test returns the unique correct demand. -/
theorem problem_3_5_finite_candidate_sound {k : ℕ} (a γ : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (hγ : ∀ j, 0 ≤ γ j) (p : PositivePrices k)
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (A : Finset (Fin k)) (hA : A.Nonempty)
    (htest : WaterfillActiveSet a γ p (ActiveSetMultiplier a γ p y A) = A) :
    MarshallianDemand (ShiftedCobbDouglas a γ) p y =
      {WaterfillBundle a γ p (ActiveSetMultiplier a γ p y A)} :=
  shiftedProduct_demand_of_waterfill a γ ha hγ p y
    (activeSetMultiplier_pos a γ ha hγ p y hy A hA)
    (active_candidate_solves_expenditure a γ ha p y A hA htest)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Leontief demand without differentiability

Kreps I, Problem 3.6(b), p. 64. For positive coefficients, the utility minimum
has a unique optimal bundle: every effective quantity equals income divided by
the cost of one unit of utility. The proof compares costs directly and applies
at zero income as well as positive income.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The smallest effective quantity among the finitely many commodities. -/
noncomputable def LeontiefUtility {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => a j * x.val j)

/-- Leontief utility is no larger than any effective commodity quantity. -/
theorem leontiefUtility_le {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) : LeontiefUtility a x ≤ a j * x.val j :=
  Finset.inf'_le _ (Finset.mem_univ j)

/-- A common lower bound for the effective quantities is a lower bound for utility. -/
theorem le_leontiefUtility {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (x : NonnegativeOrthant k) (t : ℝ) (ht : ∀ j, t ≤ a j * x.val j) :
    t ≤ LeontiefUtility a x :=
  Finset.le_inf' _ _ (fun j _ => ht j)

/-- The expenditure needed for one unit of utility. -/
noncomputable def LeontiefUnitCost {k : ℕ} (a : Fin k → ℝ) (p : PositivePrices k) : ℝ :=
  ∑ j, p.val j / a j

/-- With at least one good and strictly positive coefficients, unit cost is positive. -/
theorem leontiefUnitCost_pos {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) : 0 < LeontiefUnitCost a p := by
  exact Finset.sum_pos (fun j _ => div_pos (p.property j) (ha j)) Finset.univ_nonempty

/-- The proportional bundle prescribed by Problem 3.6(b). -/
noncomputable def LeontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) : NonnegativeOrthant k :=
  ⟨fun j => ((y : ℝ) / LeontiefUnitCost a p) / a j,
    fun j => div_nonneg (div_nonneg y.property (leontiefUnitCost_pos a ha p).le) (ha j).le⟩

/-- All effective quantities at the proposed demand equal its utility level. -/
theorem leontiefBundle_effective_quantity {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) (j : Fin k) :
    a j * (LeontiefBundle a ha p y).val j = (y : ℝ) / LeontiefUnitCost a p := by
  exact mul_div_cancel₀ _ (ne_of_gt (ha j))

/-- The proposed Leontief bundle spends exactly the available income. -/
theorem expenditure_leontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    Expenditure p (LeontiefBundle a ha p y) = (y : ℝ) := by
  calc
    _ = ((y : ℝ) / LeontiefUnitCost a p) * LeontiefUnitCost a p := by
      simp only [Expenditure, LeontiefBundle, LeontiefUnitCost, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (y : ℝ) := div_mul_cancel₀ _ (ne_of_gt (leontiefUnitCost_pos a ha p))

/-- The utility attained by the proportional bundle. -/
theorem leontiefUtility_leontiefBundle {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    LeontiefUtility a (LeontiefBundle a ha p y) = (y : ℝ) / LeontiefUnitCost a p := by
  apply le_antisymm
  · obtain ⟨j⟩ := (inferInstance : Nonempty (Fin k))
    exact (leontiefUtility_le a _ j).trans (leontiefBundle_effective_quantity a ha p y j).le
  · exact le_leontiefUtility a _ _ (fun j =>
      (leontiefBundle_effective_quantity a ha p y j).ge)

/-- Achieving utility `t` requires at least `t` times the unit cost. -/
theorem leontiefUtility_cost_bound {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (x : NonnegativeOrthant k) :
    LeontiefUtility a x * LeontiefUnitCost a p ≤ Expenditure p x := by
  rw [LeontiefUnitCost, Expenditure, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (leontiefUtility_le a x j)
    (div_pos (p.property j) (ha j)).le
  convert h using 1 <;> field_simp [ne_of_gt (ha j)]

/-- The proportional bundle is a global optimum on the full nonnegative budget. -/
theorem leontiefBundle_mem_demand {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ j, 0 < a j) (p : PositivePrices k) (y : ℝ≥0) :
    LeontiefBundle a ha p y ∈ MarshallianDemand (LeontiefUtility a) p y := by
  refine ⟨(expenditure_leontiefBundle a ha p y).le, fun x hx => ?_⟩
  change LeontiefUtility a x ≤ LeontiefUtility a (LeontiefBundle a ha p y)
  rw [leontiefUtility_leontiefBundle]
  exact (le_div_iff₀ (leontiefUnitCost_pos a ha p)).mpr
    ((leontiefUtility_cost_bound a ha p x).trans hx)

/-- **Problem 3.6(b):** the entire demand correspondence is the proposed singleton. -/
theorem problem_3_6b {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand (LeontiefUtility a) p y = {LeontiefBundle a ha p y} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hlevel : (y : ℝ) / LeontiefUnitCost a p ≤ LeontiefUtility a x := by
      simpa only [UtilityPref, leontiefUtility_leontiefBundle] using
        hx.2 _ (leontiefBundle_mem_demand a ha p y).1
    have hcoord (j : Fin k) : (LeontiefBundle a ha p y).val j ≤ x.val j :=
      (div_le_iff₀ (ha j)).mpr (by
        simpa only [mul_comm] using hlevel.trans (leontiefUtility_le a x j))
    have hsum : ∑ j, p.val j * (x.val j - (LeontiefBundle a ha p y).val j) ≤ 0 := by
      calc
        _ = Expenditure p x - Expenditure p (LeontiefBundle a ha p y) := by
          simp [Expenditure, mul_sub, Finset.sum_sub_distrib]
        _ ≤ 0 := by rw [expenditure_leontiefBundle]; exact sub_nonpos.mpr hx.1
    have hzero : ∑ j, p.val j * (x.val j - (LeontiefBundle a ha p y).val j) = 0 :=
      le_antisymm hsum (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (p.property j).le (sub_nonneg.mpr (hcoord j))))
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (p.property j).le (sub_nonneg.mpr (hcoord j)))).mp hzero j
        (Finset.mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (ne_of_gt (p.property j)))
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact leontiefBundle_mem_demand a ha p y

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homotheticity of linear and Leontief utility

Kreps I, Problems 3.6 and 3.10(a), pp. 64-65. Both utility specifications
are homogeneous of degree one on the full nonnegative orthant. The proofs
include zero scaling and do not impose uniqueness on linear demand.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Linear utility is homogeneous of degree one, even without coefficient restrictions. -/
theorem linearUtility_scale {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0)
    (x : NonnegativeOrthant k) :
    LinearUtility a (ScaleBundle t x) = (t : ℝ) * LinearUtility a x := by
  simp only [LinearUtility, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Problem 3.10(a), linear case:** linear utility represents homothetic preference. -/
theorem linearUtility_homothetic {k : ℕ} (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (LinearUtility a)) :=
  homothetic_of_homogeneous (linearUtility_scale a)

/-- A common nonnegative scale factors out of the finite Leontief minimum. -/
theorem leontiefUtility_scale {k : ℕ} [NeZero k] (a : Fin k → ℝ) (t : ℝ≥0)
    (x : NonnegativeOrthant k) :
    LeontiefUtility a (ScaleBundle t x) = (t : ℝ) * LeontiefUtility a x := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin k => a j * x.val j)
  change LeontiefUtility a x = a j * x.val j at hj
  apply le_antisymm
  · calc
      LeontiefUtility a (ScaleBundle t x) ≤ a j * (ScaleBundle t x).val j :=
        leontiefUtility_le a _ j
      _ = (t : ℝ) * LeontiefUtility a x := by rw [hj]; simp only [ScaleBundle]; ring
  · apply le_leontiefUtility
    intro i
    have hi := mul_le_mul_of_nonneg_left (leontiefUtility_le a x i) t.property
    change (t : ℝ) * LeontiefUtility a x ≤ a i * ((t : ℝ) * x.val i)
    calc
      _ ≤ (t : ℝ) * (a i * x.val i) := hi
      _ = _ := by ring

/-- **Problem 3.10(a), Leontief case:** fixed-proportion utility is homothetic. -/
theorem leontiefUtility_homothetic {k : ℕ} [NeZero k] (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (LeontiefUtility a)) :=
  homothetic_of_homogeneous (leontiefUtility_scale a)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Smooth increasing concave component utilities

Kreps I, Problems 3.8-3.9, p. 65. The derivatives are finite real values and are
taken within the nonnegative half-line, including zero. Continuity of the
marginal is the source's continuous differentiability assumption. The common
toolkit permits weakly concave components so the linear numeraire in Problem 3.9
is included; Problem 3.8 separately supplies strict concavity of every component.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- Primitive component functions and their continuous within-domain marginal utilities. -/
structure SeparableMarginals (k : ℕ) where
  utility : Fin k → ℝ → ℝ
  marginal : Fin k → ℝ → ℝ
  concave : ∀ j, ConcaveOn ℝ (Ici 0) (utility j)
  increasing : ∀ j, StrictMonoOn (utility j) (Ici 0)
  hasDeriv : ∀ j t, 0 ≤ t → HasDerivWithinAt (utility j) (marginal j t) (Ici 0) t
  continuous_marginal : ∀ j, ContinuousOn (marginal j) (Ici 0)

variable {k : ℕ} (U : SeparableMarginals k)

/-- The additively separable objective, interpreted on the nonnegative orthant. -/
def SeparableMarginals.total (x : Fin k → ℝ) : ℝ := ∑ j, U.utility j (x j)

/-- The derivative of the total objective is the sum of coordinate marginal maps. -/
noncomputable def SeparableMarginals.derivative (x : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ j, U.marginal j (x j) • ContinuousLinearMap.proj j

/-- The stated marginal is positive at every finite consumption level. -/
theorem SeparableMarginals.marginal_pos (j : Fin k) {t : ℝ} (ht : 0 ≤ t) :
    0 < U.marginal j t := by
  have hu := U.increasing j ht (show (0 : ℝ) ≤ t + 1 by linarith)
    (show t < t + 1 by linarith)
  have hs := (U.concave j).slope_le_of_hasDerivWithinAt ht
    (show (0 : ℝ) ≤ t + 1 by linarith) (show t < t + 1 by linarith) (U.hasDeriv j t ht)
  simp only [slope_def_field, add_sub_cancel_left, div_one] at hs
  linarith

/-- Strict concavity makes the marginal curve strictly decreasing, including at zero. -/
theorem SeparableMarginals.marginal_strictAnti (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictAntiOn (U.marginal j) (Ici 0) := by
  intro x hx z hz hxz
  exact (hs.lt_slope_of_hasDerivWithinAt hx hz hxz (U.hasDeriv j z hz)).trans
    (hs.slope_lt_of_hasDerivWithinAt hx hz hxz (U.hasDeriv j x hx))

/-- Concavity alone makes each marginal curve nonincreasing. -/
theorem SeparableMarginals.marginal_antitone (j : Fin k) :
    AntitoneOn (U.marginal j) (Ici 0) := by
  intro x hx z hz hxz
  rcases hxz.eq_or_lt with he | hlt
  · subst z
    exact le_rfl
  · exact ((U.concave j).le_slope_of_hasDerivWithinAt hx hz hlt
      (U.hasDeriv j z hz)).trans
      ((U.concave j).slope_le_of_hasDerivWithinAt hx hz hlt (U.hasDeriv j x hx))

/-- The component chain rule and finite sum give the genuine within-orthant derivative. -/
theorem SeparableMarginals.hasFDeriv {x : Fin k → ℝ} (hx : 0 ≤ x) :
    HasFDerivWithinAt U.total (U.derivative x) (Ici 0) x := by
  have h (j : Fin k) (_ : j ∈ Finset.univ) :
      HasFDerivWithinAt (fun z : Fin k → ℝ => U.utility j (z j))
        (U.marginal j (x j) • ContinuousLinearMap.proj j) (Ici 0) x :=
    (U.hasDeriv j (x j) (hx j)).comp_hasFDerivWithinAt (𝕜 := ℝ)
      (f := fun z : Fin k → ℝ => z j)
      (f' := (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ))
      (s := Ici (0 : Fin k → ℝ)) x
      (hasFDerivWithinAt_apply (𝕜 := ℝ) j x (Ici (0 : Fin k → ℝ))) (fun _ hz => hz j)
  convert HasFDerivWithinAt.sum h using 1
  · ext z
    simp [SeparableMarginals.total]
  · rfl

/-- Coordinate values of the total derivative are exactly the supplied scalar marginals. -/
theorem SeparableMarginals.marginalUtility (x : Fin k → ℝ) (j : Fin k) :
    MarginalUtility (U.derivative x) j = U.marginal j (x j) := by
  classical
  simp [MarginalUtility, SeparableMarginals.derivative, Pi.single_apply]

/-- The total utility is continuous on the full nonnegative orthant. -/
theorem SeparableMarginals.continuous_total :
    Continuous (fun x : NonnegativeOrthant k => U.total x.val) := by
  apply continuous_finsetSum
  intro j _
  have hc : ContinuousOn (U.utility j) (Ici 0) :=
    fun t ht => (U.hasDeriv j t ht).continuousWithinAt
  exact hc.comp_continuous ((continuous_apply j).comp continuous_subtype_val)
    (fun x => x.property j)

/-- The sum of the component concavity inequalities is concavity of total utility. -/
theorem SeparableMarginals.concave_total : ConcaveOn ℝ (Ici 0) U.total := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz a b ha hb hab
  simp only [SeparableMarginals.total, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => (U.concave j).2 (hx j) (hz j) ha hb hab)

/-- Strict concavity of all components gives strict concavity on the product domain. -/
theorem SeparableMarginals.strictConcave_total
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictConcaveOn ℝ (Ici 0) U.total := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz hne a b ha hb hab
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ z j := by
    by_contra! he
    exact hne (funext he)
  simp only [SeparableMarginals.total, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · exact fun i _ => (U.concave i).2 (hx i) (hz i) ha.le hb.le hab
  · exact ⟨j, Finset.mem_univ j, (hs j).2 (hx j) (hz j) hj ha hb hab⟩

/-- Strict concavity supplies the internal strict quasi-concavity used by demand uniqueness. -/
theorem SeparableMarginals.strictQuasiConcave_total
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictlyQuasiConcaveUtility (convex_Ici (0 : Fin k → ℝ))
      (fun x : NonnegativeOrthant k => U.total x.val) := by
  intro x z hne hxz a ha
  have h := (U.strictConcave_total hs).2 x.property z.property
    (fun he => hne (Subtype.ext he)) ha.1 (sub_pos.mpr ha.2) (by ring : a + (1 - a) = 1)
  change U.total z.val < U.total (a • x.val + (1 - a) • z.val)
  simp only [smul_eq_mul] at h
  nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr hxz)]

/-- Primitive strict-component hypotheses give a unique demand at every income, including zero. -/
theorem SeparableMarginals.unique_demand
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices k) (y : ℝ≥0) :
    ∃! x, x ∈ MarshallianDemand (fun z => U.total z.val) p y :=
  proposition_3_1c_unique U.continuous_total (U.strictQuasiConcave_total hs) p y

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The marginal-curve graphical procedure

Kreps I, Problem 3.8, p. 65. Plot each decreasing marginal-utility-per-dollar
curve. At a common horizontal height, use its intersection quantity, or zero
when the height is at least its value at zero. Add the quantities weighted by
their prices, and find the height where this total is income. The results prove
existence and uniqueness of this construction from the primitive component
assumptions, without assuming that marginal utilities vanish at infinity.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ} (U : SeparableMarginals k)

/-- The vertical coordinate in the source's graphical procedure. -/
noncomputable def SeparableMarginals.perDollar (p : PositivePrices k) (j : Fin k) (q : ℝ) : ℝ :=
  U.marginal j q / p.val j

/-- A marginal intersection, clipped to zero consumption above its initial marginal. -/
def MarginalGraph (p : PositivePrices k) (j : Fin k) (l q : ℝ) : Prop :=
  0 ≤ q ∧ U.marginal j q ≤ l * p.val j ∧ (0 < q → U.marginal j q = l * p.val j)

/-- A common positive height whose clipped intersections spend exactly the available income. -/
def GraphicalAllocation (p : PositivePrices k) (y : ℝ≥0)
    (l : ℝ) (x : NonnegativeOrthant k) : Prop :=
  0 < l ∧ Expenditure p x = (y : ℝ) ∧ ∀ j, MarginalGraph U p j l (x.val j)

/-- Every plotted marginal-per-dollar curve is continuous on the closed half-line. -/
theorem SeparableMarginals.perDollar_continuous (p : PositivePrices k) (j : Fin k) :
    ContinuousOn (U.perDollar p j) (Ici 0) :=
  (U.continuous_marginal j).div_const _

/-- Strict component concavity makes its plotted curve strictly decreasing. -/
theorem SeparableMarginals.perDollar_strictAnti (p : PositivePrices k) (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictAntiOn (U.perDollar p j) (Ici 0) := by
  intro x hx z hz hxz
  exact div_lt_div_of_pos_right (U.marginal_strictAnti j hs hx hz hxz) (p.property j)

/-- The graph is precisely the positive intersection or the clipped zero corner. -/
theorem marginalGraph_iff (p : PositivePrices k) (j : Fin k) (l q : ℝ) :
    MarginalGraph U p j l q ↔
      (q = 0 ∧ U.perDollar p j 0 ≤ l) ∨ (0 < q ∧ U.perDollar p j q = l) := by
  constructor
  · rintro ⟨hq, hm, he⟩
    rcases hq.eq_or_lt with hzero | hpos
    · subst q
      exact Or.inl ⟨rfl, (div_le_iff₀ (p.property j)).mpr hm⟩
    · exact Or.inr ⟨hpos, (div_eq_iff (p.property j).ne').mpr (he hpos)⟩
  · rintro (⟨rfl, h⟩ | ⟨hq, h⟩)
    · exact ⟨le_rfl, (div_le_iff₀ (p.property j)).mp h, fun hq => (lt_irrefl _ hq).elim⟩
    · have he : U.marginal j q = l * p.val j := (div_eq_iff (p.property j).ne').mp h
      exact ⟨hq.le, he.le, fun _ => he⟩

/-- A strictly decreasing component curve has at most one clipped intersection at any height. -/
theorem marginalGraph_unique (p : PositivePrices k) (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j)) {l q t : ℝ}
    (hq : MarginalGraph U p j l q) (ht : MarginalGraph U p j l t) : q = t := by
  have hnot {a b : ℝ} (ha : MarginalGraph U p j l a)
      (hb : MarginalGraph U p j l b) : ¬a < b := by
    intro hab
    have h := U.marginal_strictAnti j hs ha.1 hb.1 hab
    rw [hb.2.2 (ha.1.trans_lt hab)] at h
    exact (not_lt_of_ge ha.2.1) h
  exact le_antisymm (le_of_not_gt (hnot ht hq)) (le_of_not_gt (hnot hq ht))

/-- Any common-height graphical allocation solves the full consumer problem. -/
theorem graphicalAllocation_optimal {p : PositivePrices k} {y : ℝ≥0}
    {l : ℝ} {x : NonnegativeOrthant k} (h : GraphicalAllocation U p y l x) :
    x ∈ MarshallianDemand (fun z => U.total z.val) p y := by
  apply proposition_3_5b U.concave_total (U.hasFDeriv x.property)
  refine ⟨h.2.1.le, l, h.1.le, ?_, ?_, ?_⟩
  · intro j
    rw [U.marginalUtility]
    exact (h.2.2 j).2.1
  · intro j hj
    rw [U.marginalUtility]
    exact (h.2.2 j).2.2 hj
  · intro hs
    exact ((not_lt_of_ge h.2.1.ge) hs).elim

/-- Positive-income demand supplies the actual graphical height and exhausts income. -/
theorem optimal_graphicalAllocation (hk : 0 < k) {p : PositivePrices k} {y : ℝ≥0}
    (hy : 0 < (y : ℝ)) {x : NonnegativeOrthant k}
    (hx : x ∈ MarshallianDemand (fun z => U.total z.val) p y) :
    ∃ l, GraphicalAllocation U p y l x := by
  obtain ⟨hxb, l, hl, hm, he, hslack⟩ :=
    proposition_3_5a p y hy (U.hasFDeriv x.property) hx
  simp only [U.marginalUtility] at hm he
  have hlpos : 0 < l := by
    have hmi := hm ⟨0, hk⟩
    have hp := U.marginal_pos ⟨0, hk⟩ (x.property ⟨0, hk⟩)
    rcases hl.eq_or_lt with hz | hpos
    · rw [← hz, zero_mul] at hmi
      exact (not_le_of_gt hp hmi).elim
    · exact hpos
  have hbudget : Expenditure p x = (y : ℝ) := by
    apply le_antisymm hxb
    exact le_of_not_gt (fun h => hlpos.ne' (hslack h))
  exact ⟨l, hlpos, hbudget, fun j => ⟨x.property j, hm j, he j⟩⟩

/-- Solving the graphical system is exactly the positive-income demand problem. -/
theorem demand_iff_graphicalAllocation (hk : 0 < k) (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand (fun z => U.total z.val) p y ↔
      ∃ l, GraphicalAllocation U p y l x :=
  ⟨optimal_graphicalAllocation U hk hy, fun ⟨_, h⟩ => graphicalAllocation_optimal U h⟩

/-- Existence of the common-height intersections is a conclusion, not an algorithmic premise. -/
theorem exists_graphicalAllocation (hk : 0 < k) (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) : ∃ l x, GraphicalAllocation U p y l x := by
  obtain ⟨x, hx⟩ := proposition_3_1b U.continuous_total p y
  obtain ⟨l, hl⟩ := optimal_graphicalAllocation U hk hy hx
  exact ⟨l, x, hl⟩

/-- A positive-income allocation uniquely determines its common marginal height. -/
theorem graphicalAllocation_height_unique {p : PositivePrices k} {y : ℝ≥0}
    (hy : 0 < (y : ℝ)) {l m : ℝ} {x : NonnegativeOrthant k}
    (hl : GraphicalAllocation U p y l x) (hm : GraphicalAllocation U p y m x) : l = m := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < x.val j := by
    by_contra! hn
    have hz : x = ZeroBundle k := Subtype.ext (funext (fun j => le_antisymm (hn j) (x.property j)))
    have he := hl.2.1
    rw [hz, expenditure_zero] at he
    linarith
  have h := (hl.2.2 j).2.2 hj
  rw [(hm.2.2 j).2.2 hj] at h
  exact (mul_right_cancel₀ (p.property j).ne' h).symm

/-- **Problem 3.8:** the graphical procedure has one and only one height-and-bundle solution. -/
theorem problem_3_8 (hk : 0 < k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    ∃! z : ℝ × NonnegativeOrthant k, GraphicalAllocation U p y z.1 z.2 := by
  obtain ⟨l, x, hx⟩ := exists_graphicalAllocation U hk p y hy
  refine ⟨(l, x), hx, ?_⟩
  intro z hz
  have he : z.2 = x := marshallianDemand_subsingleton
    (U.strictQuasiConcave_total hs) p y (graphicalAllocation_optimal U hz)
    (graphicalAllocation_optimal U hx)
  apply Prod.ext
  · exact graphicalAllocation_height_unique U hy (he ▸ hz) hx
  · exact he

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quasi-linear marginal conditions, including the zero-numeraire corner

Kreps I, Problem 3.9, p. 65. Append the linear utility of the final commodity
to the strictly concave nonmoney components. The common marginal height is at
least the reciprocal of the numeraire price, with equality whenever numeraire
consumption is positive. Thus positive-numeraire choices have income-independent
nonmoney quantities. No asymptotic condition on the marginal utilities is added.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- Append the source's linear final commodity to the nonlinear component family. -/
def SeparableMarginals.withNumeraire (U : SeparableMarginals k) : SeparableMarginals (k + 1) where
  utility := Fin.lastCases (fun t => t) U.utility
  marginal := Fin.lastCases (fun _ => 1) U.marginal
  concave := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ _ => le_rfl⟩
    · simpa only [Fin.lastCases_castSucc] using U.concave j
  increasing := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact fun _ _ _ _ h => h
    · simpa only [Fin.lastCases_castSucc] using U.increasing j
  hasDeriv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact fun t _ => (hasDerivAt_id t).hasDerivWithinAt
    · simpa only [Fin.lastCases_castSucc] using U.hasDeriv j
  continuous_marginal := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      exact continuousOn_const
    · simpa only [Fin.lastCases_castSucc] using U.continuous_marginal j

/-- The appended objective is exactly the source's sum plus the last commodity. -/
theorem withNumeraire_total (U : SeparableMarginals k) (x : Fin (k + 1) → ℝ) :
    U.withNumeraire.total x = U.total (fun j => x j.castSucc) + x (Fin.last k) := by
  simp [SeparableMarginals.total, SeparableMarginals.withNumeraire, Fin.sum_univ_castSucc]

/-- The first prices, excluding the linear numeraire price. -/
def NonmoneyPrices (p : PositivePrices (k + 1)) : PositivePrices k :=
  ⟨fun j => p.val j.castSucc, fun j => p.property j.castSucc⟩

/-- Nonmoney quantities of a complete consumption bundle. -/
def NonmoneyBundle (x : NonnegativeOrthant (k + 1)) : NonnegativeOrthant k :=
  ⟨fun j => x.val j.castSucc, fun j => x.property j.castSucc⟩

/-- The exact clipped marginal conditions for nonlinear goods and the linear numeraire. -/
def QuasiLinearAllocation (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (y : ℝ≥0) (l : ℝ) (x : NonnegativeOrthant (k + 1)) : Prop :=
  Expenditure p x = (y : ℝ) ∧ 1 / p.val (Fin.last k) ≤ l ∧
    (∀ j, MarginalGraph U (NonmoneyPrices p) j l (x.val j.castSucc)) ∧
    (0 < x.val (Fin.last k) → l = 1 / p.val (Fin.last k))

/-- The numeraire inequalities are exactly its specialization of the common-height graph. -/
theorem quasiLinearAllocation_iff_graphical (U : SeparableMarginals k)
    (p : PositivePrices (k + 1)) (y : ℝ≥0) (l : ℝ) (x : NonnegativeOrthant (k + 1)) :
    QuasiLinearAllocation U p y l x ↔ GraphicalAllocation U.withNumeraire p y l x := by
  have hp := p.property (Fin.last k)
  constructor
  · rintro ⟨he, hl, hn, hlast⟩
    refine ⟨(one_div_pos.mpr hp).trans_le hl, he, ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_)
    · simp only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_last]
      refine ⟨x.property _, (div_le_iff₀ hp).mp hl, ?_⟩
      intro hx
      rw [hlast hx]
      exact (div_mul_cancel₀ 1 hp.ne').symm
    · simpa only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_castSucc,
        NonmoneyPrices] using hn j
  · rintro ⟨_, he, hm⟩
    have hlast := hm (Fin.last k)
    simp only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_last] at hlast
    refine ⟨he, (div_le_iff₀ hp).mpr hlast.2.1, ?_, ?_⟩
    · intro j
      simpa only [MarginalGraph, SeparableMarginals.withNumeraire, Fin.lastCases_castSucc,
        NonmoneyPrices] using hm j.castSucc
    · intro hx
      exact ((div_eq_iff hp.ne').mpr (hlast.2.2 hx)).symm

/-- **Problem 3.9:** the full positive-income demand is exactly the quasi-linear allocation rule. -/
theorem problem_3_9 (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (y : ℝ≥0) (hy : 0 < (y : ℝ)) (x : NonnegativeOrthant (k + 1)) :
    x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y ↔
      ∃ l, QuasiLinearAllocation U p y l x := by
  rw [demand_iff_graphicalAllocation U.withNumeraire (Nat.zero_lt_succ k) p y hy x]
  exact exists_congr (fun l => (quasiLinearAllocation_iff_graphical U p y l x).symm)

/-- The quasi-linear marginal rule is sufficient at every income, including zero. -/
theorem quasiLinearAllocation_optimal (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) :
    x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y :=
  graphicalAllocation_optimal U.withNumeraire
    ((quasiLinearAllocation_iff_graphical U p y l x).mp h)

/-- A strictly larger height forces zero numeraire consumption, the low-wealth corner. -/
theorem quasiLinear_height_strict_numeraire_zero (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) (hl : 1 / p.val (Fin.last k) < l) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  apply le_of_not_gt
  intro hx
  exact hl.ne' (h.2.2.2 hx)

/-- At positive numeraire consumption, nonmoney quantities solve one income-free graph. -/
theorem quasiLinear_positive_numeraire_graph (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {l : ℝ} {x : NonnegativeOrthant (k + 1)}
    (h : QuasiLinearAllocation U p y l x) (hx : 0 < x.val (Fin.last k)) :
    ∀ j, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) (x.val j.castSucc) := by
  rw [← h.2.2.2 hx]
  exact h.2.2.1

/-- Two positive-numeraire optima have identical nonmoney consumption at any two incomes. -/
theorem quasiLinear_nonmoney_independent (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {y z : ℝ≥0} {l m : ℝ}
    {x w : NonnegativeOrthant (k + 1)} (hx : QuasiLinearAllocation U p y l x)
    (hw : QuasiLinearAllocation U p z m w)
    (hxpos : 0 < x.val (Fin.last k)) (hwpos : 0 < w.val (Fin.last k)) :
    NonmoneyBundle x = NonmoneyBundle w := by
  apply Subtype.ext
  funext j
  exact marginalGraph_unique U (NonmoneyPrices p) j (hs j)
    (quasiLinear_positive_numeraire_graph U hx hxpos j)
    (quasiLinear_positive_numeraire_graph U hw hwpos j)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Unique quasi-linear demand

Kreps I, Problem 3.9, p. 65. Strict concavity of the nonmoney components fixes
their quantities at any two optima. Budget exhaustion then fixes the linear
numeraire as well. The proof includes zero income and does not falsely assert
strict concavity of the total utility in the numeraire direction.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- A strictly concave component has the same quantity at any two maxima of a concave sum. -/
theorem strict_component_equal_at_maxima (U : SeparableMarginals k) (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices k} {y : ℝ≥0} {x z : NonnegativeOrthant k}
    (hx : x ∈ MarshallianDemand (fun w => U.total w.val) p y)
    (hz : z ∈ MarshallianDemand (fun w => U.total w.val) p y) : x.val j = z.val j := by
  by_contra hne
  let w := Mix (convex_Ici (0 : Fin k → ℝ)) x z (1 / 2) (by norm_num)
  have hw : w ∈ BudgetSet p y := budgetSet_convex p y x hx.1 z hz.1 (1 / 2) (by norm_num)
  have hstrict : (1 / 2) * U.total x.val + (1 / 2) * U.total z.val < U.total w.val := by
    change (1 / 2) * (∑ i, U.utility i (x.val i)) +
      (1 / 2) * (∑ i, U.utility i (z.val i)) <
      ∑ i, U.utility i ((1 / 2) * x.val i + (1 - 1 / 2) * z.val i)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro i _
      convert (U.concave i).2 (x.property i) (z.property i)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
        (by ring : (1 / 2 : ℝ) + (1 - 1 / 2) = 1) using 1
      norm_num
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      convert hs.2 (x.property j) (z.property j) hne
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 - 1 / 2)
        (by ring : (1 / 2 : ℝ) + (1 - 1 / 2) = 1) using 1
      norm_num
  have hbound := hx.2 w hw
  have hreverse := hz.2 x hx.1
  change U.total w.val ≤ U.total x.val at hbound
  change U.total x.val ≤ U.total z.val at hreverse
  linarith

/-- Expenditure separates into nonmoney expenditure and the final commodity's cost. -/
theorem expenditure_nonmoney_split (p : PositivePrices (k + 1))
    (x : NonnegativeOrthant (k + 1)) :
    Expenditure p x = Expenditure (NonmoneyPrices p) (NonmoneyBundle x) +
      p.val (Fin.last k) * x.val (Fin.last k) := by
  simp [Expenditure, NonmoneyPrices, NonmoneyBundle, Fin.sum_univ_castSucc]

/-- The quasi-linear consumer has at most one optimum, despite the linear numeraire. -/
theorem quasiLinear_demand_subsingleton (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (y : ℝ≥0) :
    (MarshallianDemand (fun z => U.withNumeraire.total z.val) p y).Subsingleton := by
  intro x hx z hz
  by_cases hy : y = 0
  · subst y
    rw [marshallianDemand_zero] at hx hz
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hz).symm
  have hyn : 0 < (y : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hy)
  have hnon (j : Fin k) : x.val j.castSucc = z.val j.castSucc :=
    strict_component_equal_at_maxima U.withNumeraire j.castSucc
      (by simpa [SeparableMarginals.withNumeraire] using hs j) hx hz
  obtain ⟨l, hl⟩ := (problem_3_9 U p y hyn x).mp hx
  obtain ⟨m, hm⟩ := (problem_3_9 U p y hyn z).mp hz
  have he : Expenditure (NonmoneyPrices p) (NonmoneyBundle x) =
      Expenditure (NonmoneyPrices p) (NonmoneyBundle z) := by
    unfold Expenditure
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun q => p.val j.castSucc * q) (hnon j))
  have hbudget : Expenditure p x = Expenditure p z := hl.1.trans hm.1.symm
  rw [expenditure_nonmoney_split, expenditure_nonmoney_split, he] at hbudget
  have hlast : x.val (Fin.last k) = z.val (Fin.last k) :=
    (mul_left_cancel₀ (p.property (Fin.last k)).ne' (add_left_cancel hbudget))
  apply Subtype.ext
  funext j
  exact Fin.lastCases hlast hnon j

/-- Existence and uniqueness in Problem 3.9 follow from its primitive hypotheses at every income. -/
theorem quasiLinear_unique_demand (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (y : ℝ≥0) :
    ∃! x, x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y := by
  obtain ⟨x, hx⟩ := proposition_3_1b U.withNumeraire.continuous_total p y
  exact ⟨x, hx, fun z hz => quasiLinear_demand_subsingleton U hs p y hz hx⟩

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The quasi-linear wealth threshold and its possible absence

Kreps I, Problem 3.9, p. 65. If the nonmoney marginal intersections at the
reciprocal numeraire price exist, their cost is the exact wealth threshold.
At and above it, demand buys those fixed nonmoney quantities and spends the
residual on the numeraire. Below it, numeraire demand is zero. Without such
finite intersections, numeraire demand is zero at every income; the source's
assumptions do not impose a zero limiting marginal utility.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- The income-independent nonmoney intersections at the numeraire's marginal height. -/
def NumeraireTarget (U : SeparableMarginals k) (p : PositivePrices (k + 1))
    (q : NonnegativeOrthant k) : Prop :=
  ∀ j, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) (q.val j)

/-- Buy fixed nonmoney quantities and allocate all remaining income to the last good. -/
noncomputable def NumeraireResidualBundle (p : PositivePrices (k + 1))
    (q : NonnegativeOrthant k) (y : ℝ≥0)
    (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) : NonnegativeOrthant (k + 1) :=
  ⟨Fin.lastCases (((y : ℝ) - Expenditure (NonmoneyPrices p) q) / p.val (Fin.last k)) q.val, by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last, Pi.zero_apply] using
        div_nonneg (sub_nonneg.mpr hy) (p.property (Fin.last k)).le
    · simpa only [Fin.lastCases_castSucc, Pi.zero_apply] using q.property j⟩

/-- The residual construction preserves every nonmoney quantity. -/
theorem nonmoney_residualBundle (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    NonmoneyBundle (NumeraireResidualBundle p q y hy) = q := by
  apply Subtype.ext
  ext j
  simp [NonmoneyBundle, NumeraireResidualBundle]

/-- The residual construction exhausts the stated income exactly. -/
theorem residualBundle_expenditure (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    Expenditure p (NumeraireResidualBundle p q y hy) = (y : ℝ) := by
  rw [expenditure_nonmoney_split, nonmoney_residualBundle]
  simp only [NumeraireResidualBundle, Fin.lastCases_last]
  rw [mul_div_cancel₀ _ (p.property _).ne']
  ring

/-- At and above the target cost, the source's residual-income formula is optimal. -/
theorem numeraire_target_optimal (U : SeparableMarginals k)
    (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k) (hq : NumeraireTarget U p q)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    NumeraireResidualBundle p q y hy ∈
      MarshallianDemand (fun z => U.withNumeraire.total z.val) p y := by
  apply quasiLinearAllocation_optimal U (l := 1 / p.val (Fin.last k))
  refine ⟨residualBundle_expenditure p q y hy, le_rfl, ?_, fun _ => rfl⟩
  intro j
  simpa only [NumeraireResidualBundle, Fin.lastCases_castSucc] using hq j

/-- Strict concavity makes the high-wealth formula the entire demand set. -/
theorem numeraire_target_demand (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices (k + 1)) (q : NonnegativeOrthant k) (hq : NumeraireTarget U p q)
    (y : ℝ≥0) (hy : Expenditure (NonmoneyPrices p) q ≤ (y : ℝ)) :
    MarshallianDemand (fun z => U.withNumeraire.total z.val) p y =
      {NumeraireResidualBundle p q y hy} := by
  have hopt := numeraire_target_optimal U p q hq y hy
  ext x
  exact ⟨fun hx => Set.mem_singleton_iff.mpr
    (quasiLinear_demand_subsingleton U hs p y hx hopt),
    fun hx => (Set.mem_singleton_iff.mp hx).symm ▸ hopt⟩

/-- Positive numeraire consumption forces a finite target and strictly exceeds its cost. -/
theorem positive_numeraire_target (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} {y : ℝ≥0} {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y)
    (hxpos : 0 < x.val (Fin.last k)) :
    NumeraireTarget U p (NonmoneyBundle x) ∧
      Expenditure (NonmoneyPrices p) (NonmoneyBundle x) < (y : ℝ) := by
  have hcostpos : 0 < p.val (Fin.last k) * x.val (Fin.last k) :=
    mul_pos (p.property _) hxpos
  have hy : 0 < (y : ℝ) :=
    hcostpos.trans_le ((commodity_expenditure_le p x _).trans hx.1)
  obtain ⟨l, hl⟩ := (problem_3_9 U p y hy x).mp hx
  refine ⟨quasiLinear_positive_numeraire_graph U hl hxpos, ?_⟩
  have he := hl.1
  rw [expenditure_nonmoney_split] at he
  linarith

/-- Two finite nonmoney targets coincide under the source's strict component concavity. -/
theorem numeraire_target_unique (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {q t : NonnegativeOrthant k}
    (hq : NumeraireTarget U p q) (ht : NumeraireTarget U p t) : q = t := by
  apply Subtype.ext
  funext j
  exact marginalGraph_unique U (NonmoneyPrices p) j (hs j) (hq j) (ht j)

/-- Below the target cost, the unique optimum consumes no numeraire. -/
theorem below_target_numeraire_zero (U : SeparableMarginals k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {p : PositivePrices (k + 1)} {q : NonnegativeOrthant k} (hq : NumeraireTarget U p q)
    {y : ℝ≥0} (hy : (y : ℝ) ≤ Expenditure (NonmoneyPrices p) q)
    {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  apply le_of_not_gt
  intro hxpos
  obtain ⟨ht, hcost⟩ := positive_numeraire_target U hx hxpos
  rw [numeraire_target_unique U hs ht hq] at hcost
  exact (not_lt_of_ge hy) hcost

/-- If the finite target does not exist, the numeraire remains unconsumed at every income. -/
theorem no_target_numeraire_zero (U : SeparableMarginals k)
    {p : PositivePrices (k + 1)} (hn : ¬∃ q, NumeraireTarget U p q)
    {y : ℝ≥0} {x : NonnegativeOrthant (k + 1)}
    (hx : x ∈ MarshallianDemand (fun z => U.withNumeraire.total z.val) p y) :
    x.val (Fin.last k) = 0 := by
  apply le_antisymm _ (x.property _)
  exact le_of_not_gt (fun hp => hn ⟨_, (positive_numeraire_target U hx hp).1⟩)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence of finite marginal intersections

Kreps I, Problems 3.8-3.9, p. 65. A clipped marginal intersection exists exactly
when the marginal reaches or crosses the proposed height at some finite
quantity. The intermediate value theorem supplies the intersection. Applied to
the numeraire height, this gives an exact criterion for a finite wealth threshold
without imposing an unstated limiting-marginal assumption.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- A continuous marginal curve has a clipped intersection exactly when it reaches the height. -/
theorem exists_marginalGraph_iff (U : SeparableMarginals k) (p : PositivePrices k)
    (j : Fin k) (l : ℝ) :
    (∃ q, MarginalGraph U p j l q) ↔ ∃ t, 0 ≤ t ∧ U.marginal j t ≤ l * p.val j := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.1, hq.2.1⟩
  · rintro ⟨t, ht, hmt⟩
    by_cases hzero : U.marginal j 0 ≤ l * p.val j
    · exact ⟨0, le_rfl, hzero, fun h => (lt_irrefl _ h).elim⟩
    · have hc : ContinuousOn (U.marginal j) (Icc 0 t) :=
        (U.continuous_marginal j).mono (fun _ h => h.1)
      obtain ⟨q, hq, he⟩ := intermediate_value_Icc' ht hc
        ⟨hmt, (lt_of_not_ge hzero).le⟩
      exact ⟨q, hq.1, he.le, fun _ => he⟩

/-- Strictly decreasing component curves choose zero exactly above their initial marginal. -/
theorem marginalGraph_zero_iff (U : SeparableMarginals k) (p : PositivePrices k)
    (j : Fin k) (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j))
    {l q : ℝ} (hq : MarginalGraph U p j l q) : q = 0 ↔ U.perDollar p j 0 ≤ l := by
  constructor
  · intro he
    subst q
    exact (div_le_iff₀ (p.property j)).mpr hq.2.1
  · intro h
    exact marginalGraph_unique U p j hs hq ((marginalGraph_iff U p j l 0).mpr (Or.inl ⟨rfl, h⟩))

/-- The finite numeraire threshold exists exactly when every nonmoney curve reaches its height. -/
theorem numeraireTarget_exists_iff (U : SeparableMarginals k) (p : PositivePrices (k + 1)) :
    (∃ q, NumeraireTarget U p q) ↔
      ∀ j, ∃ t, 0 ≤ t ∧ U.marginal j t ≤ p.val j.castSucc / p.val (Fin.last k) := by
  constructor
  · rintro ⟨q, hq⟩ j
    refine ⟨q.val j, q.property j, ?_⟩
    convert (hq j).2.1 using 1
    simp only [NonmoneyPrices]
    ring
  · intro h
    have hg : ∀ j, ∃ q, MarginalGraph U (NonmoneyPrices p) j (1 / p.val (Fin.last k)) q := by
      intro j
      apply (exists_marginalGraph_iff U (NonmoneyPrices p) j _).mpr
      obtain ⟨t, ht, hm⟩ := h j
      refine ⟨t, ht, ?_⟩
      convert hm using 1
      simp only [NonmoneyPrices]
      ring
    choose q hq using hg
    exact ⟨⟨q, fun j => (hq j).1⟩, hq⟩

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One-sided necessary conditions

Kreps I, Problem 3.13, p. 65. Only actual one-sided derivatives are used.
The existence of coordinate partial derivatives does not supply a multivariate
first-order expansion along commodity exchanges.
-/

namespace Kreps.ConsumerDemand

open Set Filter
open scoped Topology NNReal

/-- A right derivative at a one-sided maximum is nonpositive. -/
theorem right_derivative_nonpos {f : ℝ → ℝ} {a d : ℝ}
    (hm : IsLocalMaxOn f (Ici a) a) (hd : HasDerivWithinAt f d (Ici a) a) : d ≤ 0 := by
  have ht : (1 : ℝ) ∈ posTangentConeAt (Ici a) a :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Ici (𝕜 := ℝ) a).segment_subset (by simp) (by simp))
  simpa using hm.hasFDerivWithinAt_nonpos hd ht

/-- A left derivative at a one-sided maximum is nonnegative. -/
theorem left_derivative_nonneg {f : ℝ → ℝ} {a d : ℝ}
    (hm : IsLocalMaxOn f (Iic a) a) (hd : HasDerivWithinAt f d (Iic a) a) : 0 ≤ d := by
  have ht : (-1 : ℝ) ∈ posTangentConeAt (Iic a) a :=
    mem_posTangentConeAt_of_segment_subset
      ((convex_Iic (𝕜 := ℝ) a).segment_subset (by simp) (by simp))
  have h := hm.hasFDerivWithinAt_nonpos hd ht
  simpa [UtilityPref] using h

/-- Varying one coordinate gives a continuous expenditure function. -/
theorem coordinate_expenditure_continuous {k : ℕ} (p : PositivePrices k)
    (x : Fin k → ℝ) (j : Fin k) :
    Continuous (fun t : ℝ => ∑ i, p.val i * Function.update x j t i) := by
  apply continuous_finsetSum
  intro i _
  by_cases h : i = j
  · subst i
    convert (continuous_const.mul continuous_id :
      Continuous (fun t : ℝ => p.val j * t)) using 1
    funext t
    simp
  · simp only [Function.update_of_ne h]
    exact continuous_const

/-- Reducing a positive consumed coordinate is locally feasible, regardless of budget slack. -/
theorem demand_coordinate_left_max {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y) (j : Fin k)
    (hx : 0 < x.val j) :
    IsLocalMaxOn (fun t => u (Function.update x.val j t)) (Iic (x.val j)) (x.val j) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hx)] with t ht hpos
  have hn : 0 ≤ Function.update x.val j t := by
    intro i
    by_cases h : i = j
    · subst i
      simpa using hpos.le
    · simpa [Function.update_of_ne h] using x.property i
  have hb : (∑ i, p.val i * Function.update x.val j t i) ≤ (y : ℝ) := by
    apply le_trans _ hm.1
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i = j
    · subst i
      simpa using mul_le_mul_of_nonneg_left ht (p.property j).le
    · simp [Function.update_of_ne h]
  have h := hm.2 ⟨Function.update x.val j t, hn⟩ hb
  simpa [UtilityPref] using h

/-- At slack budgets increasing a coordinate is locally feasible, including at zero. -/
theorem demand_coordinate_right_max {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y) (j : Fin k)
    (hslack : Expenditure p x < (y : ℝ)) :
    IsLocalMaxOn (fun t => u (Function.update x.val j t)) (Ici (x.val j)) (x.val j) := by
  have hc := (coordinate_expenditure_continuous p x.val j).continuousAt (x := x.val j)
  have he : (∑ i, p.val i * Function.update x.val j (x.val j) i) < (y : ℝ) := by
    simpa [Expenditure] using hslack
  have hev := hc.eventually (isOpen_Iio.mem_nhds he)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds hev] with t ht hcost
  have hn : 0 ≤ Function.update x.val j t := by
    intro i
    by_cases h : i = j
    · subst i
      simpa using (x.property j).trans ht
    · simpa [Function.update_of_ne h] using x.property i
  have h := hm.2 ⟨Function.update x.val j t, hn⟩ hcost.le
  simpa [UtilityPref] using h

/-- Any feasible path with an actual right derivative has a nonpositive derivative
at an optimum. No multivariate derivative is inferred from coordinate derivatives. -/
theorem demand_feasible_path_derivative_nonpos {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand u p y) {path : ℝ → NonnegativeOrthant k}
    (hzero : path 0 = x) (hfeas : ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, path t ∈ BudgetSet p y)
    {d : ℝ} (hd : HasDerivWithinAt (fun t => u (path t)) d (Ici 0) 0) : d ≤ 0 := by
  apply right_derivative_nonpos _ hd
  filter_upwards [hfeas] with t ht
  simpa [hzero, UtilityPref] using hm.2 (path t) ht

/-- **Problem 3.13:** necessary coordinate conditions use genuine left and right partials.
At positive quantities the left marginal is nonnegative; at a slack budget every
right marginal is nonpositive. Directional exchange tests are given separately above. -/
theorem problem_3_13 {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hm : x ∈ MarshallianDemand (fun z => u z.val) p y)
    (left right : Fin k → ℝ)
    (hl : ∀ j, 0 < x.val j → HasDerivWithinAt
      (fun t => u (Function.update x.val j t)) (left j) (Iic (x.val j)) (x.val j))
    (hr : ∀ j, HasDerivWithinAt
      (fun t => u (Function.update x.val j t)) (right j) (Ici (x.val j)) (x.val j)) :
    (∀ j, 0 < x.val j → 0 ≤ left j) ∧
      (Expenditure p x < (y : ℝ) → ∀ j, right j ≤ 0) := by
  constructor
  · intro j hj
    exact left_derivative_nonneg (demand_coordinate_left_max hm j hj) (hl j hj)
  · intro hs j
    exact right_derivative_nonpos (demand_coordinate_right_max hm j hs) (hr j)

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Differentiability is not an ordinal property

Kreps I, p. 63. This is a constructed witness, not a formula printed in the
book: an increasing continuous transform of linear utility introduces a kink
at positive consumption. The same preference retains its smooth linear
representation while the transformed representation is not differentiable.
-/

namespace Kreps.ConsumerDemand

/-- An increasing continuous transformation with a kink at the positive utility level one. -/
noncomputable def KinkTransform (t : ℝ) : ℝ := t + |t - 1| / 2

/-- The kink transformation is strictly increasing on all real utility levels. -/
theorem kinkTransform_strictMono : StrictMono KinkTransform := by
  intro x z hxz
  unfold KinkTransform
  by_cases hx : x ≤ 1
  · by_cases hz : z ≤ 1
    · rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hz)]
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_pos (sub_pos.mpr (lt_of_not_ge hz))]
      linarith
  · have hz : 1 < z := (lt_of_not_ge hx).trans hxz
    rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hx)), abs_of_pos (sub_pos.mpr hz)]
    linarith

/-- The kink transformation is continuous. -/
theorem kinkTransform_continuous : Continuous KinkTransform := by
  exact continuous_id.add ((continuous_id.sub continuous_const).abs.div_const 2)

/-- The transformed function is not differentiable at its positive kink. -/
theorem kinkTransform_not_differentiableAt : ¬DifferentiableAt ℝ KinkTransform 1 := by
  intro hd
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t - 1|) 1 := by
    convert ((hd.sub (differentiableAt_id (x := 1))).const_mul 2) using 1
    funext t
    change |t - 1| = 2 * (KinkTransform t - t)
    unfold KinkTransform
    ring
  have houter : DifferentiableAt ℝ (fun t : ℝ => |t - 1|) ((fun t : ℝ => t + 1) 0) := by
    simpa using habs
  have hshift := houter.comp 0 ((differentiableAt_id (x := (0 : ℝ))).add_const 1)
  apply not_differentiableAt_abs_zero
  convert! hshift using 1
  ext t
  simp

/-- On the actual one-good nonnegative consumption domain the transform represents linear tastes. -/
theorem kinkTransform_represents_linear :
    Represents (fun x : NonnegativeOrthant 1 => KinkTransform (x.val 0))
      (UtilityPref (fun x : NonnegativeOrthant 1 => x.val 0)) := by
  intro x z
  exact kinkTransform_strictMono.le_iff_le.symm

/-- The nonnegative-domain restriction does not remove the kink at consumption one. -/
theorem kinkTransform_not_differentiableWithinAt :
    ¬DifferentiableWithinAt ℝ KinkTransform (Set.Ici 0) 1 := by
  intro hd
  exact kinkTransform_not_differentiableAt (hd.differentiableAt (Ici_mem_nhds (by norm_num)))

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Coordinate partial derivatives do not imply common multipliers

Kreps I, Problem 3.13, p. 65, asks for necessary conditions when continuous
utility has one-sided coordinate derivatives. This constructed example shows
why those derivatives cannot simply replace a multivariate derivative in the
usual common-multiplier conditions. The source does not assert that replacement.
At its unique optimum both ordinary coordinate derivatives exist, but the
derivative along a budget-preserving exchange is not their linear combination.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- A continuous piecewise linear utility with incompatible coordinate marginal ratios. -/
def PartialDerivativeUtility (z : Fin 2 → ℝ) : ℝ :=
  z 0 + 2 * z 1 - 2 * min |z 0 - 1| |z 1 - 1|

/-- The strictly positive unit prices for the coordinate-derivative example. -/
def PartialDerivativePrices : PositivePrices 2 := ⟨![1, 1], by intro j; fin_cases j <;> norm_num⟩

/-- The candidate with one unit of each good. -/
def PartialDerivativeBundle : NonnegativeOrthant 2 :=
  ⟨![1, 1], by intro j; fin_cases j <;> norm_num⟩

/-- The counterexample utility is continuous on the whole ambient commodity space. -/
theorem partialDerivativeUtility_continuous : Continuous PartialDerivativeUtility := by
  unfold PartialDerivativeUtility
  fun_prop

/-- Every coordinate slice has finite left and right derivatives at every ambient point. -/
theorem partialDerivativeUtility_one_sided (x : Fin 2 → ℝ) (j : Fin 2) :
    DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
        (Iic (x j)) (x j) ∧
      DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
        (Ici (x j)) (x j) := by
  have hl (A B c t : ℝ) :
      DifferentiableWithinAt ℝ (fun r => A * r + B - 2 * min |r - 1| c) (Iic t) t ∧
        DifferentiableWithinAt ℝ (fun r => A * r + B - 2 * min |r - 1| c) (Ici t) t := by
    have hlin : Differentiable ℝ (fun r : ℝ => A * r + B) := by fun_prop
    exact ⟨hlin.differentiableAt.differentiableWithinAt.sub
      ((cappedAbs_one_sided 1 c t).1.const_mul 2),
      hlin.differentiableAt.differentiableWithinAt.sub
        ((cappedAbs_one_sided 1 c t).2.const_mul 2)⟩
  fin_cases j
  · convert! hl 1 (2 * x 1) |x 1 - 1| (x 0) using 1 <;>
      simp [PartialDerivativeUtility]
  · convert! hl 2 (x 0) |x 0 - 1| (x 1) using 1 <;>
      simp [PartialDerivativeUtility, min_comm, add_comm]

/-- The candidate exhausts income two and gives utility three. -/
theorem partialDerivativeBundle_values :
    Expenditure PartialDerivativePrices PartialDerivativeBundle = 2 ∧
      PartialDerivativeUtility PartialDerivativeBundle.val = 3 := by
  norm_num [Expenditure, PartialDerivativePrices, PartialDerivativeBundle,
    PartialDerivativeUtility, Fin.sum_univ_two]

/-- Every affordable bundle has utility at most three, with equality only at the candidate. -/
theorem partialDerivativeUtility_budget_bound {z : NonnegativeOrthant 2}
    (hz : z ∈ BudgetSet PartialDerivativePrices 2) :
    PartialDerivativeUtility z.val ≤ 3 ∧
      (3 ≤ PartialDerivativeUtility z.val → z = PartialDerivativeBundle) := by
  have hb : z.val 0 + z.val 1 ≤ 2 := by
    simpa [BudgetSet, Expenditure, PartialDerivativePrices, Fin.sum_univ_two] using hz
  have hm : 0 ≤ min |z.val 0 - 1| |z.val 1 - 1| :=
    le_min (abs_nonneg _) (abs_nonneg _)
  by_cases h1 : z.val 1 ≤ 1
  · constructor
    · unfold PartialDerivativeUtility
      linarith
    · intro hu
      have he1 : z.val 1 = 1 := by unfold PartialDerivativeUtility at hu; linarith
      have he0 : z.val 0 = 1 := by
        simp only [PartialDerivativeUtility, he1, sub_self, abs_zero,
          min_eq_right (abs_nonneg (z.val 0 - 1))] at hu
        linarith
      apply Subtype.ext
      funext j
      fin_cases j
      · simpa [PartialDerivativeBundle] using he0
      · simpa [PartialDerivativeBundle] using he1
  · have h1' : 1 < z.val 1 := lt_of_not_ge h1
    have h0 : z.val 0 < 1 := by linarith
    have hmin : min |z.val 0 - 1| |z.val 1 - 1| = z.val 1 - 1 := by
      rw [abs_of_neg (sub_neg.mpr h0), abs_of_pos (sub_pos.mpr h1')]
      apply min_eq_right
      linarith
    have hu : PartialDerivativeUtility z.val < 3 := by
      rw [PartialDerivativeUtility, hmin]
      linarith
    exact ⟨hu.le, fun hh => (not_lt_of_ge hh hu).elim⟩

/-- The example has the displayed unique global demand on the entire nonnegative budget. -/
theorem partialDerivativeUtility_demand :
    MarshallianDemand (fun x => PartialDerivativeUtility x.val) PartialDerivativePrices 2 =
      {PartialDerivativeBundle} := by
  have hf : PartialDerivativeBundle ∈ BudgetSet PartialDerivativePrices 2 :=
    partialDerivativeBundle_values.1.le
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    apply (partialDerivativeUtility_budget_bound hz.1).2
    have h := hz.2 PartialDerivativeBundle hf
    simpa only [UtilityPref, partialDerivativeBundle_values.2] using h
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst z
    refine ⟨hf, fun z hz => ?_⟩
    change PartialDerivativeUtility z.val ≤ PartialDerivativeUtility PartialDerivativeBundle.val
    rw [partialDerivativeBundle_values.2]
    exact (partialDerivativeUtility_budget_bound hz).1

/-- At the optimum the first coordinate slice is the affine function with slope one. -/
theorem partialDerivativeUtility_first_slice (t : ℝ) :
    PartialDerivativeUtility (Function.update PartialDerivativeBundle.val 0 t) = t + 2 := by
  simp [PartialDerivativeUtility, PartialDerivativeBundle]

/-- At the optimum the second coordinate slice is the affine function with slope two. -/
theorem partialDerivativeUtility_second_slice (t : ℝ) :
    PartialDerivativeUtility (Function.update PartialDerivativeBundle.val 1 t) = 1 + 2 * t := by
  simp [PartialDerivativeUtility, PartialDerivativeBundle]

/-- Both ordinary coordinate derivatives exist at the optimum and equal one and two. -/
theorem partialDerivativeUtility_partials (j : Fin 2) :
    HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val j t)) (![1, 2] j) 1 := by
  fin_cases j
  · change HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val 0 t)) 1 1
    convert (hasDerivAt_id (1 : ℝ)).add_const 2 using 1
    funext t
    exact partialDerivativeUtility_first_slice t
  · change HasDerivAt (fun t => PartialDerivativeUtility
      (Function.update PartialDerivativeBundle.val 1 t)) 2 1
    convert ((hasDerivAt_id (1 : ℝ)).const_mul 2).const_add 1 using 1
    · funext t
      exact partialDerivativeUtility_second_slice t
    · norm_num

/-- The actual coordinate derivatives cannot satisfy the common-multiplier conditions. -/
theorem partialDerivativeUtility_no_common_multiplier :
    ¬CombinedOptimality PartialDerivativePrices 2 PartialDerivativeBundle ![1, 2] := by
  rintro ⟨_, l, _, _, heq, _⟩
  have h0 := heq 0 (by norm_num [PartialDerivativeBundle])
  have h1 := heq 1 (by norm_num [PartialDerivativeBundle])
  norm_num [PartialDerivativePrices] at h0 h1
  linarith

/-- On a budget-preserving exchange the utility has a kink invisible to the partials. -/
theorem partialDerivativeUtility_exchange (t : ℝ) :
    PartialDerivativeUtility ![1 - t, 1 + t] = 3 + t - 2 * |t| := by
  have h0 : 1 - t - 1 = -t := by ring
  have h1 : 1 + t - 1 = t := by ring
  simp only [PartialDerivativeUtility, Matrix.cons_val_zero, Matrix.cons_val_one,
    h0, h1, abs_neg, min_self]
  ring

/-- The right exchange derivative is minus one, rather than the partial-based prediction one. -/
theorem partialDerivativeUtility_exchange_right :
    HasDerivWithinAt (fun t => PartialDerivativeUtility ![1 - t, 1 + t]) (-1) (Ici 0) 0 := by
  have hd : HasDerivWithinAt (fun t : ℝ => 3 - t) (-1) (Ici 0) 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (3 : ℝ)).sub (hasDerivAt_id 0)).hasDerivWithinAt using 1
    norm_num
  apply hd.congr_of_mem _ (by simp)
  intro t ht
  rw [partialDerivativeUtility_exchange, abs_of_nonneg ht]
  ring

/-- **Problem 3.13 limitation:** its primitive regularity does not imply common multipliers
formed from the coordinate derivatives, even at a unique interior optimum. -/
theorem problem_3_13_coordinate_multiplier_limitation :
    Continuous PartialDerivativeUtility ∧
      (∀ x : Fin 2 → ℝ, ∀ j : Fin 2,
        DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
            (Iic (x j)) (x j) ∧
          DifferentiableWithinAt ℝ (fun t => PartialDerivativeUtility (Function.update x j t))
            (Ici (x j)) (x j)) ∧
      MarshallianDemand (fun x => PartialDerivativeUtility x.val) PartialDerivativePrices 2 =
        {PartialDerivativeBundle} ∧
      (∀ j : Fin 2, HasDerivAt (fun t => PartialDerivativeUtility
        (Function.update PartialDerivativeBundle.val j t)) (![1, 2] j) 1) ∧
      ¬CombinedOptimality PartialDerivativePrices 2 PartialDerivativeBundle ![1, 2] :=
  ⟨partialDerivativeUtility_continuous, partialDerivativeUtility_one_sided,
    partialDerivativeUtility_demand, partialDerivativeUtility_partials,
    partialDerivativeUtility_no_common_multiplier⟩

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The positive-domain logarithmic problem

Kreps I, Problem 3.3(a-c), p. 64. Ordinary logarithms require strictly positive
consumption, so the logarithmic problem uses the positive part of the budget.
At positive income its unique solution agrees with full-domain Cobb-Douglas
demand. At zero income its menu is empty; the Cobb-Douglas problem still has
the unique feasible origin. Weighted-log concavity needs no normalization of
the positive weights.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- The budget menu on which ordinary, unshifted logarithms are defined. -/
def PositiveBudgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    Set (NonnegativeOrthant k) := {x | x ∈ BudgetSet p y ∧ ∀ j, 0 < x.val j}

/-- Logarithmic demand uses only feasible bundles with positive consumption in every good. -/
noncomputable def LogarithmicDemand {k : ℕ} (a : Fin k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  PrefChoice (UtilityPref (ShiftedLogUtility a 0)) (PositiveBudgetSet p y)

/-- The logarithmic transform identity is asserted only at positive consumption. -/
theorem log_cobbDouglas {k : ℕ} (a : Fin k → ℝ) (x : NonnegativeOrthant k)
    (hx : ∀ j, 0 < x.val j) : Real.log (CobbDouglas a x) = ShiftedLogUtility a 0 x :=
  log_shiftedCobbDouglas a 0 x (fun j => by simpa using hx j)

/-- **Problem 3.3(a):** weighted logarithms have the expenditure-share demand at positive income. -/
theorem problem_3_3a {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    LogarithmicDemand a p y = {CobbDouglasBundle a ha p y} := by
  let x := CobbDouglasBundle a ha p y
  have ho := cobbDouglasBundle_optimality a ha p y hy
  have hxpos : ∀ j, 0 < x.val j + (0 : Fin k → ℝ) j :=
    fun j => by simpa [x] using cobbDouglasBundle_pos a ha p y hy j
  have hx : x ∈ PositiveBudgetSet p y :=
    ⟨ho.1, cobbDouglasBundle_pos a ha p y hy⟩
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hstrict := shiftedLog_strict_optimality a 0 ha hxpos ho hz.1.1
      (fun j => by simpa using hz.1.2 j) hne
    exact (not_lt_of_ge (hz.2 x hx)) hstrict
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    refine ⟨hx, fun w hw => ?_⟩
    change ShiftedLogUtility a 0 w ≤ ShiftedLogUtility a 0 x
    by_cases he : w = x
    · rw [he]
    · exact (shiftedLog_strict_optimality a 0 ha hxpos ho hw.1
        (fun j => by simpa using hw.2 j) he).le

/-- **Problem 3.3(b):** log and Cobb-Douglas demand coincide at every positive income. -/
theorem problem_3_3b {k : ℕ} [NeZero k] (a : Fin k → ℝ) (ha : ∀ j, 0 < a j)
    (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ)) :
    LogarithmicDemand a p y = MarshallianDemand (CobbDouglas a) p y := by
  rw [problem_3_3a a ha p y hy, cobbDouglas_demand a ha p y]

/-- At zero income the ordinary logarithmic problem has no feasible positive bundle. -/
theorem logarithmicDemand_zero {k : ℕ} [NeZero k] (a : Fin k → ℝ)
    (p : PositivePrices k) : LogarithmicDemand a p 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hzero : x = ZeroBundle k := by
    have hbudget := hx.1.1
    rwa [budgetSet_zero, Set.mem_singleton_iff] at hbudget
  obtain ⟨j⟩ := (inferInstance : Nonempty (Fin k))
  have hpos := hx.1.2 j
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **Problem 3.3(c):** arbitrary positive weighted logarithms are concave on their true domain. -/
theorem problem_3_3c {k : ℕ} (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) :
    ConcaveOn ℝ {x : Fin k → ℝ | ∀ j, 0 < x j} (fun x => ∑ j, a j * Real.log (x j)) := by
  refine ⟨?_, ?_⟩
  · intro x hx z hz s t hs ht hst j
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hx j) (hz j) hs ht hst
  · intro x hx z hz s t hs ht hst
    change s * (∑ j, a j * Real.log (x j)) + t * (∑ j, a j * Real.log (z j)) ≤ _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left
      (strictConcaveOn_log_Ioi.concaveOn.2 (hx j) (hz j) hs ht hst) (ha j).le
    convert h using 1
    simp only [smul_eq_mul]
    ring

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Choice, preference, and utility

Kreps I, §1.1, pp. 1-4: feasible choice, finite nonemptiness, choice coherence,
complete and transitive preferences, and equations (1.1)-(1.3).

Choice is extended to the empty menu by the empty set. Nonemptiness is a separate
hypothesis, imposed only on finite nonempty menus in `FiniteNonempty`.
`FeasibleOn` and `CoherentOn` retain restricted menu domains for Problems 1.15-1.16.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Strict preference and indifference

Kreps I, §1.4, Propositions 1.9-1.10, pp. 9-10, and Problem 1.9, p. 26.
The two presentations of rational preference are equivalent: complete, transitive
weak preference, or asymmetric, negatively transitive strict preference.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Countable utility representation

Kreps I, §1.5, Propositions 1.11-1.12, pp. 10-12. Positive summable weights on a
countable separating subset give a utility representation. Conversely, rational
interval witnesses, together with attained minima above rational cutoffs, provide a
countable separating subset of any represented preference. This is the book's
countability argument with the gap case expressed without infimum notation.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Continuous preferences

Kreps I, Definition 1.13 and Proposition 1.14, pp. 13-14; Problem 1.11.
Continuity is expressed by openness of the strict graph. The metric characterization
uses exactly the common-radius condition in the definition. The contour results hold
on any topological space; the sequence equivalences require a sequential space.
-/

open Filter Topology

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Utility representation on the nonnegative orthant

Kreps I, Proposition 1.15, pp. 14-15. Connectedness supplies an intermediate
strict preference, and a countable dense subset supplies the separator required
by Proposition 1.12. This uses the alternative topological argument invited on p. 15.
The conclusion asserts a utility representation, without claiming its continuity.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# Monotonicity and insatiability

Kreps I, Section 2.1, pp. 31-32: Definitions 2.1 and 2.3, Proposition 2.2,
and the positive implications in Problem 2.6. Coordinatewise strict increases
are kept distinct from a weak increase with at least one strict coordinate.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Lexicographic preferences have no real utility representation

Kreps I, Problem 1.10, p. 26. On the unit square these preferences are complete
and transitive. A putative representation would put disjoint nonempty utility
intervals above each first coordinate; selecting a rational inside each interval
would inject the uncountable unit interval into the rationals.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# Continuous utility and intermediate indifference

Kreps I, the forward direction of Proposition 2.9, the compact-choice consequence
on p. 35, and Lemma 2.10, pp. 36, 38. The connected-image lemma proves the path
crossing result without assuming a continuous numerical representation. It is an
ingredient of that representation construction, not a use of the desired conclusion.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# Countable dense ranks for the general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. The general proof here uses Cantor's
isomorphism theorem on the interior ranks of a countable dense subset. It handles
attained and unattained extrema without assuming monotonicity. Problem 2.14's
particular recursive assignment is a separate source-map obligation.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# A bounded utility from dense rational ranks

The construction supporting the general Proposition 2.9 assigns each bundle
the supremum of its lower rational ranks. Adding zero makes every cut nonempty;
the rational scale lies in (0,1), so all cuts are bounded, even at extreme ranks.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# The general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. Countable dense ranks and their rational
completion give a continuous utility without any monotonicity assumption.
Open strict contours prove continuity at every bundle, including extreme ranks.
The proof works on any separable connected space and is specialized below to
every finite-dimensional nonnegative orthant, including dimension zero.
-/

namespace Kreps.ConsumerDemand.Representation

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

end Kreps.ConsumerDemand.Representation

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homotheticity of the explicit demand examples

Kreps I, Problem 3.10(a), p. 65. Unshifted Cobb-Douglas, linear and Leontief
preferences are homothetic. The ordinary logarithmic example has the same
scaling comparison on its positive domain; no utility is assigned to undefined
zero logarithms. Nonzero shifts require a separate classification.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Positive commodity scaling multiplies Cobb-Douglas utility by the total-exponent power. -/
theorem cobbDouglas_scale_pos {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) :
    CobbDouglas a (ScaleBundle t x) = (t : ℝ) ^ (∑ j, a j) * CobbDouglas a x := by
  unfold CobbDouglas ShiftedCobbDouglas
  simp only [ScaleBundle, Pi.zero_apply, add_zero]
  have hterm (j : Fin k) : ((t : ℝ) * x.val j) ^ a j =
      (t : ℝ) ^ a j * x.val j ^ a j := Real.mul_rpow t.property (x.property j)
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht]

/-- **Problem 3.10(a):** Cobb-Douglas preferences are homothetic without exponent normalization. -/
theorem cobbDouglas_homothetic {k : ℕ} (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (CobbDouglas a)) := by
  intro x z t hxz
  by_cases ht : 0 < (t : ℝ)
  · change CobbDouglas a (ScaleBundle t z) ≤ CobbDouglas a (ScaleBundle t x)
    rw [cobbDouglas_scale_pos a t ht, cobbDouglas_scale_pos a t ht]
    exact mul_le_mul_of_nonneg_left hxz (Real.rpow_pos_of_pos ht _).le
  · have ht0 : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property)
    subst t
    rw [scaleBundle_zero_scalar, scaleBundle_zero_scalar]
    exact le_rfl

/-- On positive consumption, scaling adds the same weighted logarithm to utility. -/
theorem weightedLog_scale_pos {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x : NonnegativeOrthant k) (hx : ∀ j, 0 < x.val j) :
    ShiftedLogUtility a 0 (ScaleBundle t x) =
      (∑ j, a j) * Real.log t + ShiftedLogUtility a 0 x := by
  unfold ShiftedLogUtility
  simp only [ScaleBundle, Pi.zero_apply, add_zero]
  simp_rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (hx _)), mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- **Problem 3.10(a), logarithms:** positive scaling preserves all defined log comparisons. -/
theorem logarithmic_positive_scaling_iff {k : ℕ} (a : Fin k → ℝ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (x z : NonnegativeOrthant k)
    (hx : ∀ j, 0 < x.val j) (hz : ∀ j, 0 < z.val j) :
    UtilityPref (ShiftedLogUtility a 0) (ScaleBundle t x) (ScaleBundle t z) ↔
      UtilityPref (ShiftedLogUtility a 0) x z := by
  unfold UtilityPref
  rw [weightedLog_scale_pos a t ht z hz, weightedLog_scale_pos a t ht x hx]
  exact add_le_add_iff_left _

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quasi-concave first-order sufficiency

Kreps I, Problem 3.11(a), p. 65. Only the first marginal utility is assumed
positive. The proof separates the supporting derivative of an upper contour
from the budget-slack perturbation justified by continuity.
-/

namespace Kreps.ConsumerDemand

open Set Filter
open scoped Topology NNReal

/-- A differentiable quasi-concave utility has a nonnegative derivative toward every
weakly better point in its convex upper contour, including boundary points. -/
theorem quasiconcave_direction_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {u : E → ℝ} {D : E →L[ℝ] ℝ} {x z : E}
    (hu : QuasiconcaveOn ℝ S u) (hd : HasFDerivWithinAt u D S x)
    (hx : x ∈ S) (hz : z ∈ S) (hbetter : u x ≤ u z) : 0 ≤ D (z - x) := by
  let T : Set E := {w | w ∈ S ∧ u x ≤ u w}
  have hmin : IsMinOn u T x := fun _ hw => hw.2
  exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg (hd.mono (fun _ hw => hw.1))
    (sub_mem_posTangentConeAt_of_segment_subset
      ((hu (u x)).segment_subset ⟨hx, le_rfl⟩ ⟨hz, hbetter⟩))

/-- Any strictly preferred affordable bundle can be made strictly affordable at positive
income while preserving the strict comparison. -/
theorem exists_better_strictly_affordable {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) (p : PositivePrices k) (y : ℝ≥0) (hy : 0 < (y : ℝ))
    {x z : NonnegativeOrthant k} (hz : z ∈ BudgetSet p y) (hbetter : u x < u z) :
    ∃ w : NonnegativeOrthant k, Expenditure p w < (y : ℝ) ∧ u x < u w := by
  let t : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  have ht0 (n) : 0 ≤ t n := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have ht1 (n) : t n < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hlim : Tendsto t atTop (𝓝 1) := by
    have he : t = fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) := by
      funext n
      dsimp [t]
      field_simp
      ring
    rw [he]
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let w : ℕ → NonnegativeOrthant k :=
    fun n => ⟨t n • z.val, fun j => mul_nonneg (ht0 n) (z.property j)⟩
  have hwlim : Tendsto w atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    simpa [w] using hlim.smul (tendsto_const_nhds (x := z.val))
  have hev : ∀ᶠ n in atTop, u x < u (w n) :=
    (hu.continuousAt.tendsto.comp hwlim).eventually (isOpen_Ioi.mem_nhds hbetter)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨w n, ?_, hn⟩
  have hcost : Expenditure p (w n) = t n * Expenditure p z := by
    simp [Expenditure, w, Finset.mul_sum, mul_left_comm]
  rw [hcost]
  calc
    t n * Expenditure p z ≤ t n * (y : ℝ) := mul_le_mul_of_nonneg_left hz (ht0 n)
    _ < (y : ℝ) := by nlinarith [ht1 n]

/-- **Problem 3.11(a):** quasi-concavity suffices if the first marginal is positive.
Only positivity at the candidate is needed; the book's global hypothesis implies it. -/
theorem problem_3_11a {k : ℕ} [NeZero k] {u : (Fin k → ℝ) → ℝ}
    {D : (Fin k → ℝ) →L[ℝ] ℝ} (p : PositivePrices k) (y : ℝ≥0)
    (hy : 0 < (y : ℝ)) {x : NonnegativeOrthant k}
    (hu : QuasiconcaveOn ℝ (Ici 0) u)
    (hc : Continuous (fun z : NonnegativeOrthant k => u z.val))
    (hd : HasFDerivWithinAt u D (Ici 0) x.val)
    (hpositive : 0 < MarginalUtility D 0) (ho : OptimalityConditions p y x D) :
    x ∈ MarshallianDemand (fun z => u z.val) p y := by
  obtain ⟨hfeas, l, hl, hm, hg, hs⟩ :=
    (combinedOptimality_iff_complementarity p y x (MarginalUtility D)).mp ho
  have hlpos : 0 < l := by
    by_contra hn
    have he : l = 0 := le_antisymm (le_of_not_gt hn) hl
    have h := hm 0
    rw [he, zero_mul] at h
    exact (not_le_of_gt hpositive) h
  have hprod (j) : MarginalUtility D j * x.val j = (l * p.val j) * x.val j := by
    nlinarith [hg j]
  have hgrad : D x.val = l * (y : ℝ) := by
    rw [derivative_coordinate_expansion]
    simp_rw [hprod]
    have he : (∑ j, l * p.val j * x.val j) = l * Expenditure p x := by
      simp [Expenditure, Finset.mul_sum, mul_assoc]
    rw [he]
    nlinarith
  refine ⟨hfeas, fun z hz => ?_⟩
  by_contra hn
  obtain ⟨w, hwcost, hwbetter⟩ := exists_better_strictly_affordable hc p y hy hz
    (lt_of_not_ge hn)
  have hnonneg := quasiconcave_direction_nonneg hu hd x.property w.property hwbetter.le
  have hupper : D (w.val - x.val) ≤ l * Expenditure p w - l * (y : ℝ) := by
    rw [map_sub, hgrad, derivative_coordinate_expansion]
    apply sub_le_sub_right
    calc
      (∑ j, MarginalUtility D j * w.val j) ≤ ∑ j, (l * p.val j) * w.val j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (w.property j))
      _ = l * Expenditure p w := by simp [Expenditure, Finset.mul_sum, mul_assoc]
  exact (not_lt_of_ge hnonneg) (hupper.trans_lt
    (sub_neg.mpr (mul_lt_mul_of_pos_left hwcost hlpos)))

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Robinson Crusoe's consumption and planting problem

Kreps I, Problem 3.14(a,d), pp. 65-66. The feasible planting interval is
`[0,e]`, including both endpoints and zero endowment, and the literal objective
is `U(e-x,f(x))`. The exercise invites sufficient assumptions: continuity of
the real-valued production and utility functions gives existence and Berge
continuity. Economic production monotonicity and `f(0)=0` are used in the
subsequent convexity module, not needed for these stronger topological facts.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal Topology
open Filter

/-- Planting cannot be negative or exceed the nonnegative initial endowment. -/
def CrusoeFeasible (e : ℝ≥0) : Set ℝ := Set.Icc 0 (e : ℝ)

/-- The exact two-period utility of current consumption and the crop produced by planting. -/
def CrusoeObjective (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) (e : ℝ≥0) (x : ℝ) : ℝ :=
  U ((e : ℝ) - x, f x)

/-- The entire set of optimal planting quantities. -/
def CrusoeDemand (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : ℝ≥0 → Set ℝ :=
  ParametricMaxima CrusoeFeasible (CrusoeObjective f U)

/-- The attained value, once continuity guarantees an optimum. -/
noncomputable def CrusoeValue (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : ℝ≥0 → ℝ :=
  ParametricValue CrusoeFeasible (CrusoeObjective f U)

/-- The zero planting choice is feasible for every endowment. -/
theorem crusoeFeasible_nonempty (e : ℝ≥0) : (CrusoeFeasible e).Nonempty :=
  ⟨0, le_rfl, e.property⟩

/-- Every planting menu is compact. -/
theorem crusoeFeasible_isCompact (e : ℝ≥0) : IsCompact (CrusoeFeasible e) := isCompact_Icc

/-- Joint continuity of the literal objective follows from continuity of production and utility. -/
theorem crusoeObjective_continuous {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) :
    Continuous (fun q : ℝ≥0 × ℝ => CrusoeObjective f U q.1 q.2) :=
  hU.comp (((continuous_subtype_val.comp continuous_fst).sub continuous_snd).prodMk
    (hf.comp continuous_snd))

/-- Truncating a reference planting quantity at the new endowment gives a feasible recovery. -/
theorem crusoeFeasible_continuous_selection (e : ℝ≥0) (x : ℝ) (hx : x ∈ CrusoeFeasible e) :
    ∃ s : ℝ≥0 → ℝ, Continuous s ∧ s e = x ∧ ∀ e', s e' ∈ CrusoeFeasible e' := by
  exact ⟨fun e' => min x (e' : ℝ), continuous_const.inf continuous_subtype_val,
    min_eq_left hx.2, fun e' => ⟨le_min hx.1 e'.property, min_le_right _ _⟩⟩

/-- Planting feasibility has the book's lower semicontinuity property, including at zero. -/
theorem crusoeFeasible_sequentialLower : SequentialLower CrusoeFeasible :=
  sequentialLower_of_continuous_selections crusoeFeasible_continuous_selection

/-- Limits of feasible planting quantities remain feasible at the limiting endowment. -/
theorem crusoeFeasible_sequentialUpper : SequentialUpper CrusoeFeasible := by
  intro e x e₀ x₀ he hx hm
  refine ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hx
    (Eventually.of_forall (fun n => (hm n).1)), ?_⟩
  exact le_of_tendsto_of_tendsto hx (continuous_subtype_val.continuousAt.tendsto.comp he)
    (Eventually.of_forall (fun n => (hm n).2))

/-- Nearby endowments share a common compact planting bound. -/
theorem crusoeFeasible_localCompactBound : LocalCompactBound CrusoeFeasible := by
  intro e
  refine ⟨Set.Icc 0 ((e : ℝ) + 1), isCompact_Icc, ?_⟩
  have he : ∀ᶠ e' : ℝ≥0 in 𝓝 e, (e' : ℝ) < (e : ℝ) + 1 :=
    (continuous_subtype_val.continuousAt (x := e)).eventually
      (isOpen_Iio.mem_nhds (show (e : ℝ) < (e : ℝ) + 1 by linarith))
  filter_upwards [he] with e' he'
  intro x hx
  exact ⟨hx.1, hx.2.trans he'.le⟩

/-- **Problem 3.14(a):** continuous production and utility guarantee an optimal planting choice. -/
theorem problem_3_14a {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (e : ℝ≥0) : (CrusoeDemand f U e).Nonempty := by
  exact parametricMaxima_nonempty (crusoeFeasible_isCompact e) (crusoeFeasible_nonempty e)
    ((crusoeObjective_continuous hf hU).comp (continuous_const.prodMk continuous_id))

/-- **Problem 3.14(d):** the value is continuous and optimal planting is upper semicontinuous. -/
theorem problem_3_14d {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) :
    SequentialUpper (CrusoeDemand f U) ∧ LocalCompactBound (CrusoeDemand f U) ∧
      Continuous (CrusoeValue f U) :=
  (maximum_theorem (crusoeObjective_continuous hf hU) crusoeFeasible_sequentialLower
    crusoeFeasible_sequentialUpper crusoeFeasible_localCompactBound crusoeFeasible_nonempty).2

/-- The value is the actual utility of any optimal planting quantity. -/
theorem crusoeValue_eq_of_optimum {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ} {e : ℝ≥0} {x : ℝ}
    (hx : x ∈ CrusoeDemand f U e) : CrusoeValue f U e = U ((e : ℝ) - x, f x) :=
  parametricValue_eq_of_maximum hx

/-- The full set of optimal planting quantities is compact. -/
theorem crusoeDemand_isCompact {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (e : ℝ≥0) : IsCompact (CrusoeDemand f U e) :=
  (problem_3_14d hf hU).1.isCompact (problem_3_14d hf hU).2.1 e

/-- At zero endowment the unique possible planting quantity is zero. -/
theorem crusoeDemand_zero (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : CrusoeDemand f U 0 = {0} := by
  ext x
  simp only [CrusoeDemand, ParametricMaxima, CrusoeFeasible, NNReal.coe_zero, Set.Icc_self,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
  exact ⟨And.left, fun h => ⟨h, by rw [h]⟩⟩

/-- Uniqueness everywhere gives a continuous selection and lower semicontinuous optimal planting. -/
theorem crusoeDemand_continuous_of_unique {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (hu : ∀ e, (CrusoeDemand f U e).Subsingleton) :
    ∃ s : ℝ≥0 → ℝ, Continuous s ∧ (∀ e, CrusoeDemand f U e = {s e}) ∧
      SequentialLower (CrusoeDemand f U) := by
  classical
  let s : ℝ≥0 → ℝ := fun e => Classical.choose (problem_3_14a hf hU e)
  have hs (e) : s e ∈ CrusoeDemand f U e := Classical.choose_spec (problem_3_14a hf hU e)
  have heq (e) : CrusoeDemand f U e = {s e} :=
    Set.Subset.antisymm (fun _ hx => (hu e hx (hs e))) (Set.singleton_subset_iff.mpr (hs e))
  have hfun : CrusoeDemand f U = fun e => {s e} := funext heq
  have hc : Continuous s := by
    apply continuous_of_singleton_correspondence
    · rw [← hfun]
      exact (problem_3_14d hf hU).1
    · rw [← hfun]
      exact (problem_3_14d hf hU).2.1
  refine ⟨s, hc, heq, sequentialLower_of_continuous_selections ?_⟩
  intro e x hx
  refine ⟨s, hc, ?_, hs⟩
  have hxeq : x = s e := by rwa [heq e, Set.mem_singleton_iff] at hx
  exact hxeq.symm

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Convexity and two uniqueness routes for Robinson Crusoe

Kreps I, Problem 3.14(b-c), p. 66. Concave production, concave utility, and
monotonicity in future consumption make the planting objective concave. Strict
concavity of utility is one sufficient uniqueness condition. Alternatively,
strictly concave production and strictly increasing future utility suffice.
Production is only required to be nondecreasing on its nonnegative domain,
with zero output from zero planting, as in the source.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- Future consumption weakly increases utility at a fixed nonnegative current consumption. -/
def MonotoneFutureUtility (U : ℝ × ℝ → ℝ) : Prop :=
  ∀ c, 0 ≤ c → MonotoneOn (fun z => U (c, z)) (Set.Ici 0)

/-- Future consumption strictly increases utility at every nonnegative current consumption. -/
def StrictlyMonotoneFutureUtility (U : ℝ × ℝ → ℝ) : Prop :=
  ∀ c, 0 ≤ c → StrictMonoOn (fun z => U (c, z)) (Set.Ici 0)

/-- The source's production assumptions guarantee nonnegative future consumption. -/
theorem crusoe_production_nonneg {f : ℝ → ℝ} (hm : MonotoneOn f (Set.Ici 0))
    (h0 : f 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  rwa [h0] at h

/-- A feasible planting quantity gives a nonnegative two-period consumption stream. -/
theorem crusoe_stream_nonneg {f : ℝ → ℝ} (hm : MonotoneOn f (Set.Ici 0))
    (h0 : f 0 = 0) (e : ℝ≥0) {x : ℝ} (hx : x ∈ CrusoeFeasible e) :
    ((e : ℝ) - x, f x) ∈ Set.Ici (0 : ℝ × ℝ) :=
  ⟨sub_nonneg.mpr hx.2, crusoe_production_nonneg hm h0 hx.1⟩

/-- Concavity of production and utility composes through nondecreasing future utility. -/
theorem crusoeObjective_concave {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : ConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    ConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hmix : s * x + t * z ∈ CrusoeFeasible e := (convex_Icc _ _) hx hz hs ht hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hs ht hst
  have hfconc := hf.2 hx.1 hz.1 hs ht hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs hxU.2) (mul_nonneg ht hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) ≤ _
  change _ ≤ U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans hmono

/-- Strict concavity of utility gives strict concavity of the planting objective. -/
theorem crusoeObjective_strictConcave_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : StrictConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz hne s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hpair : ((e : ℝ) - x, f x) ≠ ((e : ℝ) - z, f z) := by
    intro he
    have h := congrArg Prod.fst he
    exact hne (by dsimp at h; linarith)
  have hmix : s * x + t * z ∈ CrusoeFeasible e :=
    (convex_Icc _ _) hx hz hs.le ht.le hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hpair hs ht hst
  have hfconc := hf.2 hx.1 hz.1 hs.le ht.le hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs.le hxU.2) (mul_nonneg ht.le hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) < _
  change _ < U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans_le hmono

/-- Strict production concavity suffices when utility strictly values future consumption. -/
theorem crusoeObjective_strictConcave_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) (e : ℝ≥0) :
    StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz hne s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hmix : s * x + t * z ∈ CrusoeFeasible e :=
    (convex_Icc _ _) hx hz hs.le ht.le hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hs.le ht.le hst
  have hfconc := hf.2 hx.1 hz.1 hne hs ht hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs.le hxU.2) (mul_nonneg ht.le hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) < _
  change _ ≤ U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans_lt hmono

/-- **Problem 3.14(b):** these primitive concavity assumptions give a convex solution set. -/
theorem problem_3_14b {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : ConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    Convex ℝ (CrusoeDemand f U e) := by
  have hc := crusoeObjective_concave hm h0 hf hU hUm e
  intro x hx z hz s t hs ht hst
  refine ⟨hc.1 hx.1 hz.1 hs ht hst, fun w hw => ?_⟩
  have hconc := hc.2 hx.1 hz.1 hs ht hst
  have hxw := mul_le_mul_of_nonneg_left (hx.2 w hw) hs
  have hzw := mul_le_mul_of_nonneg_left (hz.2 w hw) ht
  change s * CrusoeObjective f U e x + t * CrusoeObjective f U e z ≤ _ at hconc
  have hwid : s * CrusoeObjective f U e w + t * CrusoeObjective f U e w =
      CrusoeObjective f U e w := by rw [← add_mul, hst, one_mul]
  linarith

/-- A strictly concave planting objective has at most one maximizer. -/
theorem crusoeDemand_subsingleton_of_strictConcave {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    {e : ℝ≥0} (hc : StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e)) :
    (CrusoeDemand f U e).Subsingleton := by
  intro x hx z hz
  exact hc.eq_of_isMaxOn hx.2 hz.2 hx.1 hz.1

/-- **Problem 3.14(c), first route:** strict utility concavity plus continuity gives uniqueness. -/
theorem problem_3_14c_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hU : StrictConcaveOn ℝ (Set.Ici 0) U)
    (hUm : MonotoneFutureUtility U) (e : ℝ≥0) : ∃! x, x ∈ CrusoeDemand f U e := by
  obtain ⟨x, hx⟩ := problem_3_14a hfc hUc e
  have hs := crusoeDemand_subsingleton_of_strictConcave
    (crusoeObjective_strictConcave_utility hm h0 hf hU hUm e)
  exact ⟨x, hx, fun z hz => hs hz hx⟩

/-- **Problem 3.14(c), second route:** strict production concavity also gives uniqueness. -/
theorem problem_3_14c_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) (e : ℝ≥0) : ∃! x, x ∈ CrusoeDemand f U e := by
  obtain ⟨x, hx⟩ := problem_3_14a hfc hUc e
  have hs := crusoeDemand_subsingleton_of_strictConcave
    (crusoeObjective_strictConcave_production hm h0 hf hU hUm e)
  exact ⟨x, hx, fun z hz => hs hz hx⟩

/-- **Problem 3.14(d):** the strict-utility assumptions also ensure lower semicontinuous demand. -/
theorem problem_3_14d_lower_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hU : StrictConcaveOn ℝ (Set.Ici 0) U)
    (hUm : MonotoneFutureUtility U) : SequentialLower (CrusoeDemand f U) := by
  obtain ⟨_, _, _, hl⟩ := crusoeDemand_continuous_of_unique hfc hUc (fun e =>
    crusoeDemand_subsingleton_of_strictConcave
      (crusoeObjective_strictConcave_utility hm h0 hf hU hUm e))
  exact hl

/-- **Problem 3.14(d):** the strict-production assumptions likewise give lower semicontinuity. -/
theorem problem_3_14d_lower_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) : SequentialLower (CrusoeDemand f U) := by
  obtain ⟨_, _, _, hl⟩ := crusoeDemand_continuous_of_unique hfc hUc (fun e =>
    crusoeDemand_subsingleton_of_strictConcave
      (crusoeObjective_strictConcave_production hm h0 hf hU hUm e))
  exact hl

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homothetic classification of the smooth separable examples

Kreps I, Problem 3.10(a), p. 65, for the families in Problems 3.8-3.9.
With at least two goods, a strictly concave component and finite positive initial
marginals prevent homotheticity. Choose prices making a unit corner optimal,
while its doubled bundle fails a companion good's marginal inequality. This
uses the source's finite derivative at zero, rather than assuming a CES form.
The one-good exception is handled separately.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

variable {k : ℕ}

/-- A strict concave component and a companion rule out homothetic smooth separable preference. -/
theorem separable_not_homothetic (U : SeparableMarginals k) (i j : Fin k) (hij : j ≠ i)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility i)) :
    ¬HomotheticPreference (UtilityPref (fun x : NonnegativeOrthant k => U.total x.val)) := by
  classical
  let b := (U.marginal i 1 + U.marginal i 2) / 2
  have h12 : U.marginal i 2 < U.marginal i 1 :=
    U.marginal_strictAnti i hs (by norm_num) (by norm_num) (by norm_num)
  have hbpos : 0 < b := by
    have h := U.marginal_pos i (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [b]
    linarith
  have hb1 : b < U.marginal i 1 := by dsimp [b]; linarith
  have hb2 : U.marginal i 2 < b := by dsimp [b]; linarith
  let p : PositivePrices k := ⟨fun a => if a = i then 1 else U.marginal a 0 / b, by
    intro a
    change 0 < if a = i then 1 else U.marginal a 0 / b
    split_ifs
    · exact zero_lt_one
    · exact div_pos (U.marginal_pos a le_rfl) hbpos⟩
  let x : NonnegativeOrthant k := ⟨Pi.single i 1, by
    intro a
    by_cases ha : a = i <;> simp [ha]⟩
  have hpi : p.val i = 1 := by simp [p]
  have hpother (a : Fin k) (ha : a ≠ i) : b * p.val a = U.marginal a 0 := by
    simp only [p, ite_eq_right ha]
    exact mul_div_cancel₀ _ hbpos.ne'
  have hgraph : GraphicalAllocation U p 1 (U.marginal i 1) x := by
    refine ⟨U.marginal_pos i (by norm_num), ?_, ?_⟩
    · simp [Expenditure, p, x, Pi.single_apply]
    · intro a
      by_cases ha : a = i
      · subst a
        simp [MarginalGraph, x, hpi]
      · have hxa : x.val a = 0 := by simp [x, ha]
        rw [hxa]
        refine ⟨le_rfl, ?_, fun h => (lt_irrefl _ h).elim⟩
        rw [← hpother a ha]
        exact mul_le_mul_of_nonneg_right hb1.le (p.property a).le
  have hopt := graphicalAllocation_optimal U hgraph
  intro hh
  have hscaled := homothetic_choice_scale_pos hh p 1 (a := 2) (by norm_num) hopt
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨l, hl⟩ := optimal_graphicalAllocation U hk (by norm_num) hscaled
  have hxi : (ScaleBundle 2 x).val i = 2 := by simp [ScaleBundle, x, Pi.single_apply]
  have hxj : (ScaleBundle 2 x).val j = 0 := by simp [ScaleBundle, x, Pi.single_apply, hij]
  have hli := (hl.2.2 i).2.2 (by rw [hxi]; norm_num)
  rw [hxi, hpi, mul_one] at hli
  have hlj := (hl.2.2 j).2.1
  rw [hxj, ← hli, ← hpother j hij] at hlj
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hb2 (p.property j))) hlj

/-- Problem 3.8's family is nonhomothetic whenever there are at least two commodities. -/
theorem problem_3_10a_separable (U : SeparableMarginals k) (hk : 2 ≤ k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    ¬HomotheticPreference (UtilityPref (fun x : NonnegativeOrthant k => U.total x.val)) :=
  separable_not_homothetic U ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp) (hs _)

/-- Problem 3.9 is nonhomothetic when at least one nonlinear commodity accompanies the numeraire. -/
theorem problem_3_10a_quasiLinear (U : SeparableMarginals k) (hk : 0 < k)
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    ¬HomotheticPreference
      (UtilityPref (fun x : NonnegativeOrthant (k + 1) => U.withNumeraire.total x.val)) := by
  let i : Fin k := ⟨0, hk⟩
  apply separable_not_homothetic U.withNumeraire i.castSucc (Fin.last k)
    (by intro he; have hv := congrArg Fin.val he; simp [i] at hv; omega)
  simpa only [SeparableMarginals.withNumeraire, Fin.lastCases_castSucc] using hs i

/-- Strictly increasing scalar components make their total strictly increasing on the orthant. -/
theorem SeparableMarginals.strictMono_total (U : SeparableMarginals k) :
    StrictMono (fun x : NonnegativeOrthant k => U.total x.val) := by
  intro x z hxz
  obtain ⟨hle, j, hj⟩ := Pi.lt_def.mp (show x.val < z.val from hxz)
  apply Finset.sum_lt_sum
  · exact fun i _ => (U.increasing i).monotoneOn (x.property i) (z.property i) (hle i)
  · exact ⟨j, Finset.mem_univ j, U.increasing j (x.property j) (z.property j) hj⟩

/-- With just one good, every strictly increasing utility has homothetic preference. -/
theorem one_good_strictMono_homothetic {u : NonnegativeOrthant 1 → ℝ} (hu : StrictMono u) :
    HomotheticPreference (UtilityPref u) := by
  intro x z a hxz
  have hz : z ≤ x := by
    intro j
    fin_cases j
    apply le_of_not_gt
    intro hlt
    have horder : x < z := by
      apply lt_iff_le_not_ge.mpr
      refine ⟨?_, fun h => (not_le_of_gt hlt) (h 0)⟩
      intro j
      fin_cases j
      exact hlt.le
    exact (not_le_of_gt (hu horder)) hxz
  exact hu.monotone (fun j => mul_le_mul_of_nonneg_left (hz j) a.property)

/-- The one-good exception to Problem 3.8's negative classification is explicit. -/
theorem problem_3_10a_separable_one_good (U : SeparableMarginals 1) :
    HomotheticPreference (UtilityPref (fun x : NonnegativeOrthant 1 => U.total x.val)) :=
  one_good_strictMono_homothetic U.strictMono_total

/-- With no nonlinear goods, Problem 3.9 is a single linear numeraire and is homothetic. -/
theorem problem_3_10a_numeraire_only (U : SeparableMarginals 0) :
    HomotheticPreference
      (UtilityPref (fun x : NonnegativeOrthant 1 => U.withNumeraire.total x.val)) :=
  one_good_strictMono_homothetic U.withNumeraire.strictMono_total

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The three numerical demands in Problem 3.4

Kreps I, Problem 3.4, p. 64. The utility and prices below are exactly the
printed example. Income 16.4 is the exact rational number 82/5. Each answer is
proved to be the entire singleton demand set, including comparison with all
boundary bundles, rather than merely a solution of first-order equations.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- The exact logarithmic utility in Problem 3.4. -/
noncomputable def Problem34Utility (x : NonnegativeOrthant 3) : ℝ :=
  Real.log (x.val 0 + 2) + 2 * Real.log (x.val 1 + 3) + 4 * Real.log (x.val 2 + 2)

/-- The exact prices in Problem 3.4, in the same commodity order. -/
def Problem34Prices : PositivePrices 3 :=
  ⟨![2, 3, 1], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at income 5. -/
def Problem34BundleFive : NonnegativeOrthant 3 :=
  ⟨![0, 0, 5], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at the exact decimal income 16.4. -/
noncomputable def Problem34BundleSixteenPointFour : NonnegativeOrthant 3 :=
  ⟨![6 / 25, 0, 398 / 25], fun j => by fin_cases j <;> norm_num⟩

/-- The demanded bundle at income 100. -/
noncomputable def Problem34BundleHundred : NonnegativeOrthant 3 :=
  ⟨![87 / 14, 167 / 21, 446 / 7], fun j => by fin_cases j <;> norm_num⟩

/-- The printed expression is a specialization of weighted shifted logarithms. -/
theorem problem34Utility_eq : Problem34Utility = ShiftedLogUtility ![1, 2, 4] ![2, 3, 2] := by
  funext x
  simp [Problem34Utility, ShiftedLogUtility, Fin.sum_univ_succ, add_assoc]

/-- **Problem 3.4, income 5:** only the third good is consumed. -/
theorem problem_3_4_five :
    MarshallianDemand Problem34Utility Problem34Prices 5 = {Problem34BundleFive} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 4 / 7, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleFive, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleFive]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleFive]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleFive, Fin.sum_univ_succ]

/-- **Problem 3.4, income 16.4:** the first and third goods are consumed. -/
theorem problem_3_4_sixteenPointFour :
    MarshallianDemand Problem34Utility Problem34Prices (82 / 5) =
      {Problem34BundleSixteenPointFour} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 25 / 112, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleSixteenPointFour,
      Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleSixteenPointFour]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleSixteenPointFour]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleSixteenPointFour, Fin.sum_univ_succ]

/-- **Problem 3.4, income 100:** all three goods are consumed. -/
theorem problem_3_4_hundred :
    MarshallianDemand Problem34Utility Problem34Prices 100 = {Problem34BundleHundred} := by
  rw [problem34Utility_eq]
  apply shiftedLog_demand_of_positive_shifts
    (ha := fun j => by fin_cases j <;> norm_num)
    (hγ := fun j => by fin_cases j <;> norm_num)
  refine ⟨?_, 7 / 115, by norm_num, ?_, ?_, ?_⟩
  · norm_num [BudgetSet, Expenditure, Problem34Prices, Problem34BundleHundred, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleHundred]
  · intro j
    fin_cases j <;> norm_num [LogMarginals, Problem34Prices, Problem34BundleHundred]
  · norm_num [Expenditure, Problem34Prices, Problem34BundleHundred, Fin.sum_univ_succ]

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homothetic classification of shifted products

Kreps I, Problem 3.10(a), p. 65, for Problems 3.4-3.5. In two or more goods,
positive-exponent shifted Cobb-Douglas preferences are homothetic exactly when
every shift vanishes. With one good, all the increasing shifted products are
homothetic. The literal shifted-log example in Problem 3.4 is nonhomothetic.
The proof uses the already proved full-domain demand procedure, not assumed
interior first-order conditions for a logarithm at boundary bundles.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

variable {k : ℕ}

/-- A positive shift changes interior marginal ratios under scaling and rules out homotheticity. -/
theorem shiftedProduct_not_homothetic (a γ : Fin k → ℝ) (ha : ∀ n, 0 < a n)
    (hγ : ∀ n, 0 ≤ γ n) (i j : Fin k) (hij : j ≠ i) (hi : 0 < γ i) :
    ¬HomotheticPreference (UtilityPref (ShiftedCobbDouglas a γ)) := by
  classical
  have hk : k ≠ 0 := by have h := i.isLt; omega
  let := NeZero.mk hk
  let x : NonnegativeOrthant k := ⟨fun n => if n = i then γ i else γ n + 1, by
    intro n
    change 0 ≤ if n = i then γ i else γ n + 1
    split_ifs
    · exact hi.le
    · linarith [hγ n]⟩
  have hxpos (n : Fin k) : 0 < x.val n := by
    change 0 < if n = i then γ i else γ n + 1
    split_ifs
    · exact hi
    · linarith [hγ n]
  have hxshift (n : Fin k) : 0 < x.val n + γ n := add_pos_of_pos_of_nonneg (hxpos n) (hγ n)
  let p : PositivePrices k := ⟨fun n => a n / (x.val n + γ n),
    fun n => div_pos (ha n) (hxshift n)⟩
  let y : ℝ≥0 := ⟨Expenditure p x, expenditure_nonneg p x⟩
  have hy : 0 < (y : ℝ) :=
    (mul_pos (p.property i) (hxpos i)).trans_le (commodity_expenditure_le p x i)
  have ho : CombinedOptimality p y x (LogMarginals a γ x) := by
    refine ⟨(show Expenditure p x ≤ Expenditure p x from le_rfl),
      1, zero_le_one, ?_, ?_, ?_⟩
    · intro n
      simp [LogMarginals, p]
    · intro n _
      simp [LogMarginals, p]
    · intro h
      exact (lt_irrefl _ h).elim
  have hopt : x ∈ MarshallianDemand (ShiftedCobbDouglas a γ) p y := by
    rw [shiftedCobbDouglas_demand_of_optimality a γ ha hγ hxshift ho]
    exact Set.mem_singleton x
  intro hh
  have hscaled := homothetic_choice_scale_pos hh p y (a := 2) (by norm_num) hopt
  change ScaleBundle 2 x ∈ MarshallianDemand (ShiftedCobbDouglas a γ) p (2 * y) at hscaled
  obtain ⟨l, hl, hcost⟩ := exists_waterfill_multiplier a γ ha hγ p (2 * y) (by
    change 0 < (2 : ℝ) * (y : ℝ)
    positivity)
  have he : ScaleBundle 2 x = WaterfillBundle a γ p l := by
    rw [shiftedProduct_demand_of_waterfill a γ ha hγ p (2 * y) hl hcost] at hscaled
    exact Set.mem_singleton_iff.mp hscaled
  have hratio (n : Fin k) : x.val n + γ n = l * (2 * x.val n + γ n) := by
    have hpos : 0 < (WaterfillBundle a γ p l).val n := by
      rw [← he]
      change 0 < (2 : ℝ) * x.val n
      exact mul_pos (by norm_num) (hxpos n)
    have hm := waterfillBundle_marginal_eq a γ ha p hl n hpos
    rw [← he] at hm
    change a n / ((2 : ℝ) * x.val n + γ n) = l * (a n / (x.val n + γ n)) at hm
    have hd : 0 < 2 * x.val n + γ n := by nlinarith [hxpos n, hγ n]
    field_simp [(hxshift n).ne', hd.ne'] at hm
    apply mul_left_cancel₀ (ha n).ne'
    nlinarith [hm]
  have hri := hratio i
  have hrj := hratio j
  simp only [x, ite_eq_left] at hri
  simp only [x, ite_eq_right hij] at hrj
  have hprod : (2 - 3 * l) * γ i = 0 := by nlinarith [hri]
  have heq := (mul_eq_zero.mp hprod).resolve_right hi.ne'
  have hlval : l = 2 / 3 := by linarith
  rw [hlval] at hrj
  linarith

/-- **Problem 3.10(a), shifted products:** in at least two goods all shifts must vanish. -/
theorem shiftedProduct_homothetic_iff_zero_shifts (a γ : Fin k → ℝ)
    (ha : ∀ n, 0 < a n) (hγ : ∀ n, 0 ≤ γ n) (hk : 2 ≤ k) :
    HomotheticPreference (UtilityPref (ShiftedCobbDouglas a γ)) ↔ γ = 0 := by
  constructor
  · intro hh
    funext i
    apply le_antisymm _ (hγ i)
    apply le_of_not_gt
    intro hi
    let zero : Fin k := ⟨0, by omega⟩
    let one : Fin k := ⟨1, by omega⟩
    have hj : ∃ j : Fin k, j ≠ i := by
      by_cases he : i = zero
      · refine ⟨one, ?_⟩
        rw [he]
        simp [one, zero]
      · exact ⟨zero, Ne.symm he⟩
    obtain ⟨j, hij⟩ := hj
    exact shiftedProduct_not_homothetic a γ ha hγ i j hij hi hh
  · rintro rfl
    exact cobbDouglas_homothetic a

/-- A single increasing shifted-product good is the dimensional exception. -/
theorem shiftedProduct_one_good_homothetic (a γ : Fin 1 → ℝ)
    (ha : ∀ n, 0 < a n) (hγ : ∀ n, 0 ≤ γ n) :
    HomotheticPreference (UtilityPref (ShiftedCobbDouglas a γ)) := by
  apply one_good_strictMono_homothetic
  intro x z hxz
  obtain ⟨_, j, hj⟩ := Pi.lt_def.mp (show x.val < z.val from hxz)
  fin_cases j
  change x.val 0 < z.val 0 at hj
  simpa [ShiftedCobbDouglas, Fin.prod_univ_succ] using
    Real.rpow_lt_rpow (add_nonneg (x.property 0) (hγ 0))
      (by linarith : x.val 0 + γ 0 < z.val 0 + γ 0) (ha 0)

/-- The literal shifted-log utility in Problem 3.4 fails homothetic income scaling. -/
theorem problem_3_10a_shifted_log : ¬HomotheticPreference (UtilityPref Problem34Utility) := by
  intro hh
  have hx : Problem34BundleFive ∈ MarshallianDemand Problem34Utility Problem34Prices 5 := by
    rw [problem_3_4_five]
    exact Set.mem_singleton _
  have hs := homothetic_choice_scale_pos hh Problem34Prices 5 (a := 20) (by norm_num) hx
  change ScaleBundle 20 Problem34BundleFive ∈
    MarshallianDemand Problem34Utility Problem34Prices (20 * 5) at hs
  have hnum : (20 : ℝ≥0) * 5 = 100 := by norm_num
  rw [hnum, problem_3_4_hundred] at hs
  have he := congrArg (fun x : NonnegativeOrthant 3 => x.val 0) (Set.mem_singleton_iff.mp hs)
  norm_num [ScaleBundle, Problem34BundleFive, Problem34BundleHundred] at he

end Kreps.ConsumerDemand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Stationary but strictly increasing utility

Kreps I, Problems 3.11(b) and 3.12, p. 65. The constructed one-good utility
`(x - 1)^3` has a zero derivative at one unit. At income two this is a nonoptimal
stationary candidate; at income one it is the unique optimum and forces a zero
multiplier. The formula is our witness, not a formula printed in the book.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- The one-good stationary cubic, defined on the ambient line of bundles. -/
def StationaryCubic (x : Fin 1 → ℝ) : ℝ := (x 0 - 1) ^ 3

/-- A one-good consumption quantity as a bundle. -/
def SingleQuantity (q : ℝ≥0) : NonnegativeOrthant 1 := ⟨fun _ => q, fun _ => q.property⟩

/-- The unit price for the cubic examples. -/
def UnitPrice : PositivePrices 1 := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- The scalar cubic is strictly increasing despite its stationary point. -/
theorem stationaryCubic_increasing {a b : ℝ} (h : a < b) :
    (a - 1) ^ 3 < (b - 1) ^ 3 :=
  (Odd.strictMono_pow (by decide : Odd 3)) (sub_lt_sub_right h 1)

/-- The utility is continuously differentiable on the whole ambient space. -/
theorem stationaryCubic_contDiff : ContDiff ℝ 1 StationaryCubic := by
  unfold StationaryCubic
  fun_prop

/-- Local insatiability holds at every nonnegative quantity, including zero and one. -/
theorem stationaryCubic_locallyInsatiable :
    LocallyInsatiable (UtilityPref (fun x : NonnegativeOrthant 1 => StationaryCubic x.val)) := by
  apply Representation.strictAllIncrease_locallyInsatiable
  intro x y h
  have hs := stationaryCubic_increasing (h 0)
  exact ⟨hs.le, not_le_of_gt hs⟩

/-- The actual derivative at one unit is the zero linear functional. -/
theorem stationaryCubic_derivative_one :
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
    (x := (SingleQuantity 1).val)).sub_const 1 |>.pow 3
  convert h using 1 <;> first | rfl | simp [SingleQuantity]

/-- At either income, the stationary candidate satisfies the exact combined conditions. -/
theorem stationaryCubic_conditions {y : ℝ≥0} (hy : 1 ≤ y) :
    OptimalityConditions UnitPrice y (SingleQuantity 1) 0 := by
  refine ⟨?_, 0, le_rfl, ?_, ?_, ?_⟩
  · change Expenditure UnitPrice (SingleQuantity 1) ≤ (y : ℝ)
    simpa [Expenditure, UnitPrice, SingleQuantity] using (show (1 : ℝ) ≤ y from hy)
  · intro j
    simp [MarginalUtility]
  · intro j _
    simp [MarginalUtility]
  · intro _
    rfl

/-- **Problem 3.11(b):** the stationary candidate at income two is strictly suboptimal. -/
theorem stationaryCubic_nonoptimal :
    SingleQuantity 1 ∉ MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 2 := by
  intro h
  have hb : SingleQuantity 2 ∈ BudgetSet UnitPrice 2 := by
    norm_num [BudgetSet, Expenditure, UnitPrice, SingleQuantity]
  have hc := h.2 (SingleQuantity 2) hb
  norm_num [UtilityPref, StationaryCubic, SingleQuantity] at hc

/-- Strictly increasing one-good cubic preferences are strictly convex. -/
theorem stationaryCubic_strictlyConvex :
    StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (UtilityPref (fun x => StationaryCubic x.val)) := by
  intro x y hne hxy a ha
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  have hle : y.val 0 ≤ x.val 0 := hf.le_iff_le.mp hxy
  have hneq : x.val 0 ≠ y.val 0 := by
    intro h
    apply hne
    apply Subtype.ext
    funext i
    fin_cases i
    exact h
  have hlt : y.val 0 < x.val 0 := lt_of_le_of_ne hle (Ne.symm hneq)
  have hm : y.val 0 < a * x.val 0 + (1 - a) * y.val 0 := by
    nlinarith [mul_pos ha.1 (sub_pos.mpr hlt)]
  have h := stationaryCubic_increasing hm
  exact ⟨h.le, not_le_of_gt h⟩

/-- The witness also satisfies the quasi-concavity premise of Problem 3.11. -/
theorem stationaryCubic_quasiConcave :
    QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (fun x => StationaryCubic x.val) := by
  intro x y a ha
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  change min ((x.val 0 - 1) ^ 3) ((y.val 0 - 1) ^ 3) ≤
    ((a * x.val 0 + (1 - a) * y.val 0) - 1) ^ 3
  by_cases h : x.val 0 ≤ y.val 0
  · exact (min_le_left _ _).trans (hf.monotone (by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr h)]))
  · exact (min_le_right _ _).trans (hf.monotone (by
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr (le_of_not_ge h))]))

/-- At unit price the unique demand is the entire income, including zero income. -/
theorem stationaryCubic_demand (y : ℝ≥0) :
    MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice y = {SingleQuantity y} := by
  have hf : StrictMono (fun t : ℝ => (t - 1) ^ 3) := fun _ _ => stationaryCubic_increasing
  have hb : SingleQuantity y ∈ BudgetSet UnitPrice y := by
    simp [BudgetSet, Expenditure, UnitPrice, SingleQuantity]
  ext x
  constructor
  · intro hx
    have hlow : (y : ℝ) ≤ x.val 0 := hf.le_iff_le.mp (hx.2 _ hb)
    have hupp : x.val 0 ≤ (y : ℝ) := by
      simpa [BudgetSet, Expenditure, UnitPrice] using hx.1
    apply Subtype.ext
    funext i
    fin_cases i
    exact le_antisymm hupp hlow
  · intro hx
    rcases hx with rfl
    refine ⟨hb, fun z hz => ?_⟩
    apply hf.monotone
    simpa [BudgetSet, Expenditure, UnitPrice, SingleQuantity] using hz

/-- **Problem 3.12:** every multiplier satisfying stationarity at the unique income-one
optimum is zero. The stationary derivative is proved separately above. -/
theorem stationaryCubic_multiplier_forced_zero (l : ℝ)
    (heq : ∀ j, 0 < (SingleQuantity 1).val j →
      MarginalUtility (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) j = l * UnitPrice.val j) : l = 0 := by
  have h := heq 0 (by norm_num [SingleQuantity])
  simpa [MarginalUtility, UnitPrice] using h.symm

/-- The utility is strictly increasing in the full one-good coordinate order. -/
theorem stationaryCubic_strictMono : StrictMono StationaryCubic := by
  intro x y hxy
  apply stationaryCubic_increasing
  by_contra h
  apply hxy.not_ge
  intro i
  fin_cases i
  exact le_of_not_gt h

/-- **Problem 3.11(b):** all regularity premises hold, but the exact calculus conditions
at one unit do not imply demand at income two. -/
theorem problem_3_11b :
    ContDiff ℝ 1 StationaryCubic ∧
    LocallyInsatiable (UtilityPref (fun x : NonnegativeOrthant 1 => StationaryCubic x.val)) ∧
    QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (fun x => StationaryCubic x.val) ∧
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val ∧
    OptimalityConditions UnitPrice 2 (SingleQuantity 1) 0 ∧
    SingleQuantity 1 ∉ MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 2 :=
  ⟨stationaryCubic_contDiff, stationaryCubic_locallyInsatiable, stationaryCubic_quasiConcave,
    stationaryCubic_derivative_one, stationaryCubic_conditions (by norm_num),
    stationaryCubic_nonoptimal⟩

/-- **Problem 3.12:** the strictly increasing, strictly convex preference witness has
unique demand at the stationary point, whose multiplier must vanish. -/
theorem problem_3_12 :
    StrictMono StationaryCubic ∧
    StrictlyConvexPreference (convex_Ici (𝕜 := ℝ) (0 : Fin 1 → ℝ))
      (UtilityPref (fun x => StationaryCubic x.val)) ∧
    MarshallianDemand (fun x => StationaryCubic x.val) UnitPrice 1 = {SingleQuantity 1} ∧
    HasFDerivAt StationaryCubic (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (SingleQuantity 1).val ∧
    OptimalityConditions UnitPrice 1 (SingleQuantity 1) 0 ∧
    ∀ l : ℝ, (∀ j, 0 < (SingleQuantity 1).val j →
      MarginalUtility (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) j = l * UnitPrice.val j) → l = 0 :=
  ⟨stationaryCubic_strictMono, stationaryCubic_strictlyConvex, stationaryCubic_demand 1,
    stationaryCubic_derivative_one, stationaryCubic_conditions le_rfl,
    stationaryCubic_multiplier_forced_zero⟩

end Kreps.ConsumerDemand

set_option linter.style.longLine false
#print axioms Kreps.ConsumerDemand.Complete
#print axioms Kreps.ConsumerDemand.TransitivePref
#print axioms Kreps.ConsumerDemand.Rational
#print axioms Kreps.ConsumerDemand.PrefChoice
#print axioms Kreps.ConsumerDemand.UtilityPref
#print axioms Kreps.ConsumerDemand.Represents
#print axioms Kreps.ConsumerDemand.Strict
#print axioms Kreps.ConsumerDemand.Indifferent
#print axioms Kreps.ConsumerDemand.utilityPref_rational
#print axioms Kreps.ConsumerDemand.NonnegativeOrthant
#print axioms Kreps.ConsumerDemand.LocallyInsatiable
#print axioms Kreps.ConsumerDemand.Mix
#print axioms Kreps.ConsumerDemand.ConvexMenu
#print axioms Kreps.ConsumerDemand.ConvexPreference
#print axioms Kreps.ConsumerDemand.StrictlyConvexPreference
#print axioms Kreps.ConsumerDemand.ConcaveUtility
#print axioms Kreps.ConsumerDemand.QuasiConcaveUtility
#print axioms Kreps.ConsumerDemand.StrictlyQuasiConcaveUtility
#print axioms Kreps.ConsumerDemand.PositivePrices
#print axioms Kreps.ConsumerDemand.ZeroBundle
#print axioms Kreps.ConsumerDemand.Expenditure
#print axioms Kreps.ConsumerDemand.BudgetSet
#print axioms Kreps.ConsumerDemand.expenditure_zero
#print axioms Kreps.ConsumerDemand.expenditure_nonneg
#print axioms Kreps.ConsumerDemand.budgetSet_nonempty
#print axioms Kreps.ConsumerDemand.commodity_expenditure_le
#print axioms Kreps.ConsumerDemand.budgetSet_coordinate_bound
#print axioms Kreps.ConsumerDemand.budgetSet_zero
#print axioms Kreps.ConsumerDemand.expenditure_continuous
#print axioms Kreps.ConsumerDemand.budgetSet_isClosed
#print axioms Kreps.ConsumerDemand.budgetSet_isCompact
#print axioms Kreps.ConsumerDemand.expenditure_mix
#print axioms Kreps.ConsumerDemand.budgetSet_convex
#print axioms Kreps.ConsumerDemand.ScalePrices
#print axioms Kreps.ConsumerDemand.expenditure_scalePrices
#print axioms Kreps.ConsumerDemand.budgetSet_scale
#print axioms Kreps.ConsumerDemand.MarshallianDemand
#print axioms Kreps.ConsumerDemand.mem_marshallianDemand_iff
#print axioms Kreps.ConsumerDemand.mem_marshallianDemand_iff_isMaxOn
#print axioms Kreps.ConsumerDemand.proposition_3_1a
#print axioms Kreps.ConsumerDemand.proposition_3_1b
#print axioms Kreps.ConsumerDemand.marshallianDemand_zero
#print axioms Kreps.ConsumerDemand.proposition_3_1c_convex
#print axioms Kreps.ConsumerDemand.marshallianDemand_subsingleton
#print axioms Kreps.ConsumerDemand.proposition_3_1c_unique
#print axioms Kreps.ConsumerDemand.preferenceChoice_exhausts_budget
#print axioms Kreps.ConsumerDemand.proposition_3_1d
#print axioms Kreps.ConsumerDemand.feasible_segment_derivative_nonpos
#print axioms Kreps.ConsumerDemand.convex_firstOrderNecessary
#print axioms Kreps.ConsumerDemand.linear_budget_multipliers
#print axioms Kreps.ConsumerDemand.concave_support_le
#print axioms Kreps.ConsumerDemand.concave_support_upper
#print axioms Kreps.ConsumerDemand.concave_firstOrderSufficient
#print axioms Kreps.ConsumerDemand.MarginalUtility
#print axioms Kreps.ConsumerDemand.CombinedOptimality
#print axioms Kreps.ConsumerDemand.OptimalityConditions
#print axioms Kreps.ConsumerDemand.BudgetVectors
#print axioms Kreps.ConsumerDemand.mem_budgetVectors_val
#print axioms Kreps.ConsumerDemand.budgetVectors_convex
#print axioms Kreps.ConsumerDemand.derivative_coordinate_expansion
#print axioms Kreps.ConsumerDemand.marginalUtility_right_derivative
#print axioms Kreps.ConsumerDemand.combinedOptimality_iff_complementarity
#print axioms Kreps.ConsumerDemand.combinedOptimality_iff_lagrangian
#print axioms Kreps.ConsumerDemand.proposition_3_5a
#print axioms Kreps.ConsumerDemand.optimalityConditions_firstOrder
#print axioms Kreps.ConsumerDemand.proposition_3_5b
#print axioms Kreps.ConsumerDemand.ShiftedLogUtility
#print axioms Kreps.ConsumerDemand.LogMarginals
#print axioms Kreps.ConsumerDemand.log_sub_log_le_tangent
#print axioms Kreps.ConsumerDemand.log_sub_log_lt_tangent
#print axioms Kreps.ConsumerDemand.shiftedLog_strict_support
#print axioms Kreps.ConsumerDemand.combinedOptimality_linear_bound
#print axioms Kreps.ConsumerDemand.shiftedLog_strict_optimality
#print axioms Kreps.ConsumerDemand.shiftedLog_demand_of_positive_shifts
#print axioms Kreps.ConsumerDemand.ShiftedCobbDouglas
#print axioms Kreps.ConsumerDemand.shiftedCobbDouglas_pos
#print axioms Kreps.ConsumerDemand.shiftedCobbDouglas_eq_zero
#print axioms Kreps.ConsumerDemand.log_shiftedCobbDouglas
#print axioms Kreps.ConsumerDemand.shiftedCobbDouglas_strict_optimality
#print axioms Kreps.ConsumerDemand.shiftedCobbDouglas_demand_of_optimality
#print axioms Kreps.ConsumerDemand.CobbDouglas
#print axioms Kreps.ConsumerDemand.cobbDouglas_continuous
#print axioms Kreps.ConsumerDemand.exponent_sum_pos
#print axioms Kreps.ConsumerDemand.CobbDouglasBundle
#print axioms Kreps.ConsumerDemand.cobbDouglasBundle_pos
#print axioms Kreps.ConsumerDemand.expenditure_cobbDouglasBundle
#print axioms Kreps.ConsumerDemand.cobbDouglasBundle_logMarginals
#print axioms Kreps.ConsumerDemand.cobbDouglasBundle_optimality
#print axioms Kreps.ConsumerDemand.cobbDouglas_demand_pos
#print axioms Kreps.ConsumerDemand.cobbDouglasBundle_zero
#print axioms Kreps.ConsumerDemand.cobbDouglas_demand
#print axioms Kreps.ConsumerDemand.cobbDouglas_demand_positive
#print axioms Kreps.ConsumerDemand.combinedOptimality_bangForBuck
#print axioms Kreps.ConsumerDemand.consumed_good_maximizes_bangForBuck
#print axioms Kreps.ConsumerDemand.consumed_goods_equal_bangForBuck
#print axioms Kreps.ConsumerDemand.consumed_goods_marginal_cross_product
#print axioms Kreps.ConsumerDemand.consumed_goods_marginal_ratio
#print axioms Kreps.ConsumerDemand.cobbDouglas_expenditure_share
#print axioms Kreps.ConsumerDemand.cobbDouglas_other_prices_irrelevant
#print axioms Kreps.ConsumerDemand.cobbDouglas_ten_percent
#print axioms Kreps.ConsumerDemand.SequentialUpper
#print axioms Kreps.ConsumerDemand.SequentialLower
#print axioms Kreps.ConsumerDemand.ParametricMaxima
#print axioms Kreps.ConsumerDemand.parametricMaxima_nonempty
#print axioms Kreps.ConsumerDemand.parametricMaxima_sequentialUpper
#print axioms Kreps.ConsumerDemand.sequentialUpper_upperHemicontinuousAt
#print axioms Kreps.ConsumerDemand.sequentialLower_of_continuous_selections
#print axioms Kreps.ConsumerDemand.LocalCompactBound
#print axioms Kreps.ConsumerDemand.ParametricValue
#print axioms Kreps.ConsumerDemand.parametricValue_eq_of_maximum
#print axioms Kreps.ConsumerDemand.parametricValue_continuous
#print axioms Kreps.ConsumerDemand.LocalCompactBound.mono
#print axioms Kreps.ConsumerDemand.SequentialUpper.isClosed
#print axioms Kreps.ConsumerDemand.SequentialUpper.isCompact
#print axioms Kreps.ConsumerDemand.continuous_of_singleton_correspondence
#print axioms Kreps.ConsumerDemand.SameObjectiveUpperBounds
#print axioms Kreps.ConsumerDemand.maximum_theorem_auxiliary
#print axioms Kreps.ConsumerDemand.maximum_theorem
#print axioms Kreps.ConsumerDemand.sameObjectiveUpperBounds_iff_value_eq
#print axioms Kreps.ConsumerDemand.PriceIncome
#print axioms Kreps.ConsumerDemand.ScaleBundle
#print axioms Kreps.ConsumerDemand.scaleBundle_zero
#print axioms Kreps.ConsumerDemand.scaleBundle_one
#print axioms Kreps.ConsumerDemand.expenditure_scaleBundle
#print axioms Kreps.ConsumerDemand.expenditure_pos
#print axioms Kreps.ConsumerDemand.expenditure_price_continuous
#print axioms Kreps.ConsumerDemand.expenditure_joint_continuous
#print axioms Kreps.ConsumerDemand.BudgetAdjustmentFactor
#print axioms Kreps.ConsumerDemand.BudgetAdjustment
#print axioms Kreps.ConsumerDemand.budgetAdjustment_self
#print axioms Kreps.ConsumerDemand.budgetAdjustment_feasible
#print axioms Kreps.ConsumerDemand.budgetAdjustment_continuous
#print axioms Kreps.ConsumerDemand.budgetSet_continuous_selection
#print axioms Kreps.ConsumerDemand.budgetSet_sequentialLower
#print axioms Kreps.ConsumerDemand.budgetSet_sequentialUpper
#print axioms Kreps.ConsumerDemand.budgetSet_localCompactBound
#print axioms Kreps.ConsumerDemand.SingleGoodBundle
#print axioms Kreps.ConsumerDemand.expenditure_singleGoodBundle
#print axioms Kreps.ConsumerDemand.singleGoodBundle_mem_budgetSet
#print axioms Kreps.ConsumerDemand.budgetSet_exists_positive
#print axioms Kreps.ConsumerDemand.BudgetTriangleVertices
#print axioms Kreps.ConsumerDemand.budgetTriangleVertices_subset
#print axioms Kreps.ConsumerDemand.budgetVectors_eq_triangle
#print axioms Kreps.ConsumerDemand.normalizedPower_unit_tangent_lt
#print axioms Kreps.ConsumerDemand.normalizedPower_tangent_lt
#print axioms Kreps.ConsumerDemand.normalizedPower_tangent_le
#print axioms Kreps.ConsumerDemand.CESPowerSum
#print axioms Kreps.ConsumerDemand.CESUtility
#print axioms Kreps.ConsumerDemand.CESWeight
#print axioms Kreps.ConsumerDemand.CESDenominator
#print axioms Kreps.ConsumerDemand.cesWeight_pos
#print axioms Kreps.ConsumerDemand.cesDenominator_pos
#print axioms Kreps.ConsumerDemand.CESBundle
#print axioms Kreps.ConsumerDemand.cesBundle_pos
#print axioms Kreps.ConsumerDemand.expenditure_cesBundle
#print axioms Kreps.ConsumerDemand.cesBundle_marginal_ratio
#print axioms Kreps.ConsumerDemand.cesPowerSum_strict_support
#print axioms Kreps.ConsumerDemand.cesPowerSum_nonneg
#print axioms Kreps.ConsumerDemand.cesPowerSum_pos
#print axioms Kreps.ConsumerDemand.cesUtility_of_positive
#print axioms Kreps.ConsumerDemand.cesUtility_pos
#print axioms Kreps.ConsumerDemand.cesPowerSum_strict_budget
#print axioms Kreps.ConsumerDemand.cesUtility_strict_budget
#print axioms Kreps.ConsumerDemand.ces_demand_pos
#print axioms Kreps.ConsumerDemand.cesBundle_zero
#print axioms Kreps.ConsumerDemand.problem_3_7
#print axioms Kreps.ConsumerDemand.cesUtility_nonneg
#print axioms Kreps.ConsumerDemand.cesUtility_zero_of_coordinate
#print axioms Kreps.ConsumerDemand.cesUtility_le_coordinate
#print axioms Kreps.ConsumerDemand.cesPowerSum_continuousAt_interior
#print axioms Kreps.ConsumerDemand.cesUtility_continuousAt_interior
#print axioms Kreps.ConsumerDemand.cesUtility_continuousAt_boundary
#print axioms Kreps.ConsumerDemand.cesUtility_continuous
#print axioms Kreps.ConsumerDemand.HomotheticPreference
#print axioms Kreps.ConsumerDemand.scaleBundle_zero_scalar
#print axioms Kreps.ConsumerDemand.scaleBundle_mul
#print axioms Kreps.ConsumerDemand.scaleBundle_inv
#print axioms Kreps.ConsumerDemand.homothetic_scale_iff
#print axioms Kreps.ConsumerDemand.mem_budgetSet_scale_bundle_iff
#print axioms Kreps.ConsumerDemand.homothetic_choice_scale_pos
#print axioms Kreps.ConsumerDemand.homothetic_choice_scale_iff
#print axioms Kreps.ConsumerDemand.homothetic_choice_set_scale
#print axioms Kreps.ConsumerDemand.problem_3_10b
#print axioms Kreps.ConsumerDemand.homothetic_of_homogeneous
#print axioms Kreps.ConsumerDemand.cesPowerSum_scale
#print axioms Kreps.ConsumerDemand.cesUtility_zero
#print axioms Kreps.ConsumerDemand.cesUtility_scale_pos
#print axioms Kreps.ConsumerDemand.cesUtility_scale
#print axioms Kreps.ConsumerDemand.cesUtility_homothetic
#print axioms Kreps.ConsumerDemand.LinearUtility
#print axioms Kreps.ConsumerDemand.linearUtility_continuous
#print axioms Kreps.ConsumerDemand.linearUtility_singleGoodBundle
#print axioms Kreps.ConsumerDemand.linearUtility_le_ratio_expenditure
#print axioms Kreps.ConsumerDemand.exists_maximal_utility_price_ratio
#print axioms Kreps.ConsumerDemand.singleGoodBundle_mem_linearDemand
#print axioms Kreps.ConsumerDemand.problem_3_6a
#print axioms Kreps.ConsumerDemand.cesUtility_one
#print axioms Kreps.ConsumerDemand.problem_3_7_one
#print axioms Kreps.ConsumerDemand.cesWeight_continuousAt_zero
#print axioms Kreps.ConsumerDemand.cesDenominator_zero
#print axioms Kreps.ConsumerDemand.cesDenominator_continuousAt_zero
#print axioms Kreps.ConsumerDemand.cesBundle_at_zero_exponent
#print axioms Kreps.ConsumerDemand.problem_3_7_zero_limit
#print axioms Kreps.ConsumerDemand.cesDemand_tendsto_cobbDouglas
#print axioms Kreps.ConsumerDemand.cappedAbs_eq_difference
#print axioms Kreps.ConsumerDemand.cappedAbs_one_sided
#print axioms Kreps.ConsumerDemand.TransferDirection
#print axioms Kreps.ConsumerDemand.transferDirection_cost
#print axioms Kreps.ConsumerDemand.transfer_nonnegative
#print axioms Kreps.ConsumerDemand.TransferBundle
#print axioms Kreps.ConsumerDemand.expenditure_transferBundle
#print axioms Kreps.ConsumerDemand.transferBundle_mem_budget
#print axioms Kreps.ConsumerDemand.derivative_transferDirection
#print axioms Kreps.ConsumerDemand.utility_transfer_derivative
#print axioms Kreps.ConsumerDemand.exists_improving_commodity_transfer
#print axioms Kreps.ConsumerDemand.StrictlyDecreasingPreference
#print axioms Kreps.ConsumerDemand.problem_3_1_demand
#print axioms Kreps.ConsumerDemand.problem_3_1_not_locallyInsatiable
#print axioms Kreps.ConsumerDemand.IllustrationPrices
#print axioms Kreps.ConsumerDemand.IllustrationFirst
#print axioms Kreps.ConsumerDemand.IllustrationSecond
#print axioms Kreps.ConsumerDemand.IllustrationSatiation
#print axioms Kreps.ConsumerDemand.SeparatedOptimaUtility
#print axioms Kreps.ConsumerDemand.SatiationUtility
#print axioms Kreps.ConsumerDemand.illustration_expenditure
#print axioms Kreps.ConsumerDemand.separatedOptimaUtility_le_one
#print axioms Kreps.ConsumerDemand.figure_3_2a_demand
#print axioms Kreps.ConsumerDemand.figure_3_2b_demand
#print axioms Kreps.ConsumerDemand.satiationUtility_le_zero
#print axioms Kreps.ConsumerDemand.figure_3_2c_demand
#print axioms Kreps.ConsumerDemand.figure_3_2c_slack
#print axioms Kreps.ConsumerDemand.illustration_vertices_ne
#print axioms Kreps.ConsumerDemand.separatedOptimaUtility_continuous
#print axioms Kreps.ConsumerDemand.figure_3_2a_not_convex
#print axioms Kreps.ConsumerDemand.figure_3_2b_convex
#print axioms Kreps.ConsumerDemand.figure_3_2b_not_strictlyConvex
#print axioms Kreps.ConsumerDemand.satiationUtility_continuous
#print axioms Kreps.ConsumerDemand.figure_3_2c_not_locallyInsatiable
#print axioms Kreps.ConsumerDemand.WaterfillCost
#print axioms Kreps.ConsumerDemand.waterfillCost_continuousOn
#print axioms Kreps.ConsumerDemand.waterfillCost_lower_bound
#print axioms Kreps.ConsumerDemand.waterfillCost_upper_bound
#print axioms Kreps.ConsumerDemand.exists_waterfill_multiplier
#print axioms Kreps.ConsumerDemand.WaterfillBundle
#print axioms Kreps.ConsumerDemand.waterfillBundle_commodity_cost
#print axioms Kreps.ConsumerDemand.expenditure_waterfillBundle
#print axioms Kreps.ConsumerDemand.waterfillBundle_shifted_pos
#print axioms Kreps.ConsumerDemand.waterfillBundle_marginal_le
#print axioms Kreps.ConsumerDemand.waterfillBundle_marginal_eq
#print axioms Kreps.ConsumerDemand.waterfillBundle_optimality
#print axioms Kreps.ConsumerDemand.shiftedProduct_demand_of_waterfill
#print axioms Kreps.ConsumerDemand.problem_3_5
#print axioms Kreps.ConsumerDemand.problem_3_5_zero
#print axioms Kreps.ConsumerDemand.WaterfillActiveSet
#print axioms Kreps.ConsumerDemand.ActiveSetMultiplier
#print axioms Kreps.ConsumerDemand.waterfillCost_eq_active_sum
#print axioms Kreps.ConsumerDemand.waterfillActiveSet_nonempty
#print axioms Kreps.ConsumerDemand.waterfill_multiplier_eq_active_candidate
#print axioms Kreps.ConsumerDemand.activeSetMultiplier_pos
#print axioms Kreps.ConsumerDemand.active_candidate_solves_expenditure
#print axioms Kreps.ConsumerDemand.problem_3_5_finite_candidates
#print axioms Kreps.ConsumerDemand.problem_3_5_finite_candidate_sound
#print axioms Kreps.ConsumerDemand.IndirectUtility
#print axioms Kreps.ConsumerDemand.indirectUtility_eq_of_mem
#print axioms Kreps.ConsumerDemand.indirectUtility_zero
#print axioms Kreps.ConsumerDemand.proposition_3_3a
#print axioms Kreps.ConsumerDemand.consumer_maximum_theorem
#print axioms Kreps.ConsumerDemand.proposition_3_3b
#print axioms Kreps.ConsumerDemand.marshallianDemand_localCompactBound
#print axioms Kreps.ConsumerDemand.marshallianDemand_isCompact
#print axioms Kreps.ConsumerDemand.marshallianDemand_upperHemicontinuous
#print axioms Kreps.ConsumerDemand.proposition_3_3c
#print axioms Kreps.ConsumerDemand.proposition_3_3b_unique
#print axioms Kreps.ConsumerDemand.IrrelevantOutside
#print axioms Kreps.ConsumerDemand.StrictlyConvexInGoods
#print axioms Kreps.ConsumerDemand.RemoveGood
#print axioms Kreps.ConsumerDemand.expenditure_removeGood
#print axioms Kreps.ConsumerDemand.irrelevant_good_zero_at_choice
#print axioms Kreps.ConsumerDemand.problem_3_2_subsingleton
#print axioms Kreps.ConsumerDemand.problem_3_2_unique
#print axioms Kreps.ConsumerDemand.LeontiefUtility
#print axioms Kreps.ConsumerDemand.leontiefUtility_le
#print axioms Kreps.ConsumerDemand.le_leontiefUtility
#print axioms Kreps.ConsumerDemand.LeontiefUnitCost
#print axioms Kreps.ConsumerDemand.leontiefUnitCost_pos
#print axioms Kreps.ConsumerDemand.LeontiefBundle
#print axioms Kreps.ConsumerDemand.leontiefBundle_effective_quantity
#print axioms Kreps.ConsumerDemand.expenditure_leontiefBundle
#print axioms Kreps.ConsumerDemand.leontiefUtility_leontiefBundle
#print axioms Kreps.ConsumerDemand.leontiefUtility_cost_bound
#print axioms Kreps.ConsumerDemand.leontiefBundle_mem_demand
#print axioms Kreps.ConsumerDemand.problem_3_6b
#print axioms Kreps.ConsumerDemand.linearUtility_scale
#print axioms Kreps.ConsumerDemand.linearUtility_homothetic
#print axioms Kreps.ConsumerDemand.leontiefUtility_scale
#print axioms Kreps.ConsumerDemand.leontiefUtility_homothetic
#print axioms Kreps.ConsumerDemand.SeparableMarginals
#print axioms Kreps.ConsumerDemand.SeparableMarginals.mk
#print axioms Kreps.ConsumerDemand.SeparableMarginals.utility
#print axioms Kreps.ConsumerDemand.SeparableMarginals.marginal
#print axioms Kreps.ConsumerDemand.SeparableMarginals.concave
#print axioms Kreps.ConsumerDemand.SeparableMarginals.increasing
#print axioms Kreps.ConsumerDemand.SeparableMarginals.hasDeriv
#print axioms Kreps.ConsumerDemand.SeparableMarginals.continuous_marginal
#print axioms Kreps.ConsumerDemand.SeparableMarginals.total
#print axioms Kreps.ConsumerDemand.SeparableMarginals.derivative
#print axioms Kreps.ConsumerDemand.SeparableMarginals.marginal_pos
#print axioms Kreps.ConsumerDemand.SeparableMarginals.marginal_strictAnti
#print axioms Kreps.ConsumerDemand.SeparableMarginals.marginal_antitone
#print axioms Kreps.ConsumerDemand.SeparableMarginals.hasFDeriv
#print axioms Kreps.ConsumerDemand.SeparableMarginals.marginalUtility
#print axioms Kreps.ConsumerDemand.SeparableMarginals.continuous_total
#print axioms Kreps.ConsumerDemand.SeparableMarginals.concave_total
#print axioms Kreps.ConsumerDemand.SeparableMarginals.strictConcave_total
#print axioms Kreps.ConsumerDemand.SeparableMarginals.strictQuasiConcave_total
#print axioms Kreps.ConsumerDemand.SeparableMarginals.unique_demand
#print axioms Kreps.ConsumerDemand.SeparableMarginals.perDollar
#print axioms Kreps.ConsumerDemand.MarginalGraph
#print axioms Kreps.ConsumerDemand.GraphicalAllocation
#print axioms Kreps.ConsumerDemand.SeparableMarginals.perDollar_continuous
#print axioms Kreps.ConsumerDemand.SeparableMarginals.perDollar_strictAnti
#print axioms Kreps.ConsumerDemand.marginalGraph_iff
#print axioms Kreps.ConsumerDemand.marginalGraph_unique
#print axioms Kreps.ConsumerDemand.graphicalAllocation_optimal
#print axioms Kreps.ConsumerDemand.optimal_graphicalAllocation
#print axioms Kreps.ConsumerDemand.demand_iff_graphicalAllocation
#print axioms Kreps.ConsumerDemand.exists_graphicalAllocation
#print axioms Kreps.ConsumerDemand.graphicalAllocation_height_unique
#print axioms Kreps.ConsumerDemand.problem_3_8
#print axioms Kreps.ConsumerDemand.SeparableMarginals.withNumeraire
#print axioms Kreps.ConsumerDemand.withNumeraire_total
#print axioms Kreps.ConsumerDemand.NonmoneyPrices
#print axioms Kreps.ConsumerDemand.NonmoneyBundle
#print axioms Kreps.ConsumerDemand.QuasiLinearAllocation
#print axioms Kreps.ConsumerDemand.quasiLinearAllocation_iff_graphical
#print axioms Kreps.ConsumerDemand.problem_3_9
#print axioms Kreps.ConsumerDemand.quasiLinearAllocation_optimal
#print axioms Kreps.ConsumerDemand.quasiLinear_height_strict_numeraire_zero
#print axioms Kreps.ConsumerDemand.quasiLinear_positive_numeraire_graph
#print axioms Kreps.ConsumerDemand.quasiLinear_nonmoney_independent
#print axioms Kreps.ConsumerDemand.strict_component_equal_at_maxima
#print axioms Kreps.ConsumerDemand.expenditure_nonmoney_split
#print axioms Kreps.ConsumerDemand.quasiLinear_demand_subsingleton
#print axioms Kreps.ConsumerDemand.quasiLinear_unique_demand
#print axioms Kreps.ConsumerDemand.NumeraireTarget
#print axioms Kreps.ConsumerDemand.NumeraireResidualBundle
#print axioms Kreps.ConsumerDemand.nonmoney_residualBundle
#print axioms Kreps.ConsumerDemand.residualBundle_expenditure
#print axioms Kreps.ConsumerDemand.numeraire_target_optimal
#print axioms Kreps.ConsumerDemand.numeraire_target_demand
#print axioms Kreps.ConsumerDemand.positive_numeraire_target
#print axioms Kreps.ConsumerDemand.numeraire_target_unique
#print axioms Kreps.ConsumerDemand.below_target_numeraire_zero
#print axioms Kreps.ConsumerDemand.no_target_numeraire_zero
#print axioms Kreps.ConsumerDemand.exists_marginalGraph_iff
#print axioms Kreps.ConsumerDemand.marginalGraph_zero_iff
#print axioms Kreps.ConsumerDemand.numeraireTarget_exists_iff
#print axioms Kreps.ConsumerDemand.right_derivative_nonpos
#print axioms Kreps.ConsumerDemand.left_derivative_nonneg
#print axioms Kreps.ConsumerDemand.coordinate_expenditure_continuous
#print axioms Kreps.ConsumerDemand.demand_coordinate_left_max
#print axioms Kreps.ConsumerDemand.demand_coordinate_right_max
#print axioms Kreps.ConsumerDemand.demand_feasible_path_derivative_nonpos
#print axioms Kreps.ConsumerDemand.problem_3_13
#print axioms Kreps.ConsumerDemand.KinkTransform
#print axioms Kreps.ConsumerDemand.kinkTransform_strictMono
#print axioms Kreps.ConsumerDemand.kinkTransform_continuous
#print axioms Kreps.ConsumerDemand.kinkTransform_not_differentiableAt
#print axioms Kreps.ConsumerDemand.kinkTransform_represents_linear
#print axioms Kreps.ConsumerDemand.kinkTransform_not_differentiableWithinAt
#print axioms Kreps.ConsumerDemand.PartialDerivativeUtility
#print axioms Kreps.ConsumerDemand.PartialDerivativePrices
#print axioms Kreps.ConsumerDemand.PartialDerivativeBundle
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_continuous
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_one_sided
#print axioms Kreps.ConsumerDemand.partialDerivativeBundle_values
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_budget_bound
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_demand
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_first_slice
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_second_slice
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_partials
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_no_common_multiplier
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_exchange
#print axioms Kreps.ConsumerDemand.partialDerivativeUtility_exchange_right
#print axioms Kreps.ConsumerDemand.problem_3_13_coordinate_multiplier_limitation
#print axioms Kreps.ConsumerDemand.PositiveBudgetSet
#print axioms Kreps.ConsumerDemand.LogarithmicDemand
#print axioms Kreps.ConsumerDemand.log_cobbDouglas
#print axioms Kreps.ConsumerDemand.problem_3_3a
#print axioms Kreps.ConsumerDemand.problem_3_3b
#print axioms Kreps.ConsumerDemand.logarithmicDemand_zero
#print axioms Kreps.ConsumerDemand.problem_3_3c
#print axioms Kreps.ConsumerDemand.Representation.FullMenus
#print axioms Kreps.ConsumerDemand.Representation.ChoiceRule
#print axioms Kreps.ConsumerDemand.Representation.FeasibleOn
#print axioms Kreps.ConsumerDemand.Representation.Feasible
#print axioms Kreps.ConsumerDemand.Representation.FiniteNonempty
#print axioms Kreps.ConsumerDemand.Representation.CoherentOn
#print axioms Kreps.ConsumerDemand.Representation.Coherent
#print axioms Kreps.ConsumerDemand.Representation.Complete
#print axioms Kreps.ConsumerDemand.Representation.TransitivePref
#print axioms Kreps.ConsumerDemand.Representation.Rational
#print axioms Kreps.ConsumerDemand.Representation.PrefChoice
#print axioms Kreps.ConsumerDemand.Representation.UtilityPref
#print axioms Kreps.ConsumerDemand.Representation.UtilityChoice
#print axioms Kreps.ConsumerDemand.Representation.Represents
#print axioms Kreps.ConsumerDemand.Representation.Revealed
#print axioms Kreps.ConsumerDemand.Representation.Strict
#print axioms Kreps.ConsumerDemand.Representation.Indifferent
#print axioms Kreps.ConsumerDemand.Representation.NoBetterThan
#print axioms Kreps.ConsumerDemand.Representation.complete_refl
#print axioms Kreps.ConsumerDemand.Representation.prefChoice_feasible
#print axioms Kreps.ConsumerDemand.Representation.feasible_empty
#print axioms Kreps.ConsumerDemand.Representation.represents_choice
#print axioms Kreps.ConsumerDemand.Representation.coherent_iff_on_full
#print axioms Kreps.ConsumerDemand.Representation.AsymmetricPref
#print axioms Kreps.ConsumerDemand.Representation.NegativelyTransitive
#print axioms Kreps.ConsumerDemand.Representation.WeakFromStrict
#print axioms Kreps.ConsumerDemand.Representation.IndifferenceFromStrict
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9a
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9b
#print axioms Kreps.ConsumerDemand.Representation.strict_weak_trans
#print axioms Kreps.ConsumerDemand.Representation.weak_strict_trans
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9c
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9d
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9e
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9f
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9g
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_9h
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_10
#print axioms Kreps.ConsumerDemand.Representation.problem_1_9
#print axioms Kreps.ConsumerDemand.Representation.OrderSeparating
#print axioms Kreps.ConsumerDemand.Representation.exists_positive_summable
#print axioms Kreps.ConsumerDemand.Representation.WeightedUtility
#print axioms Kreps.ConsumerDemand.Representation.weightedTerm_le
#print axioms Kreps.ConsumerDemand.Representation.weightedUtility_mono
#print axioms Kreps.ConsumerDemand.Representation.weightedUtility_strict
#print axioms Kreps.ConsumerDemand.Representation.weightedUtility_represents
#print axioms Kreps.ConsumerDemand.Representation.represents_of_countable_separating
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_11
#print axioms Kreps.ConsumerDemand.Representation.strict_iff_utility_lt
#print axioms Kreps.ConsumerDemand.Representation.countable_separating_of_represents
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_12
#print axioms Kreps.ConsumerDemand.Representation.NoWorseThan
#print axioms Kreps.ConsumerDemand.Representation.StrictlyBetterThan
#print axioms Kreps.ConsumerDemand.Representation.StrictlyWorseThan
#print axioms Kreps.ConsumerDemand.Representation.ContinuousPreference
#print axioms Kreps.ConsumerDemand.Representation.MetricContinuousPreference
#print axioms Kreps.ConsumerDemand.Representation.continuousPreference_iff_metric
#print axioms Kreps.ConsumerDemand.Representation.continuousPreference_of_continuous_utility
#print axioms Kreps.ConsumerDemand.Representation.ClosedContours
#print axioms Kreps.ConsumerDemand.Representation.OpenStrictContours
#print axioms Kreps.ConsumerDemand.Representation.continuousPreference_openStrictContours
#print axioms Kreps.ConsumerDemand.Representation.closedContours_iff_openStrictContours
#print axioms Kreps.ConsumerDemand.Representation.openStrictContours_continuousPreference
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_14c
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_14d
#print axioms Kreps.ConsumerDemand.Representation.SequenceWeakContinuity
#print axioms Kreps.ConsumerDemand.Representation.SequenceStrictContinuity
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_14a
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_14b
#print axioms Kreps.ConsumerDemand.Representation.problem_1_11
#print axioms Kreps.ConsumerDemand.Representation.exists_strict_between
#print axioms Kreps.ConsumerDemand.Representation.dense_orderSeparating
#print axioms Kreps.ConsumerDemand.Representation.represents_of_continuous_connected
#print axioms Kreps.ConsumerDemand.Representation.NonnegativeOrthant
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_15
#print axioms Kreps.ConsumerDemand.Representation.proposition_1_15_metric
#print axioms Kreps.ConsumerDemand.Representation.MonotonePreference
#print axioms Kreps.ConsumerDemand.Representation.StrictlyMonotonePreference
#print axioms Kreps.ConsumerDemand.Representation.StrictAllIncreasePreference
#print axioms Kreps.ConsumerDemand.Representation.GloballyInsatiable
#print axioms Kreps.ConsumerDemand.Representation.LocallyInsatiable
#print axioms Kreps.ConsumerDemand.Representation.proposition_2_2_monotone
#print axioms Kreps.ConsumerDemand.Representation.proposition_2_2_strict
#print axioms Kreps.ConsumerDemand.Representation.monotone_all_representations
#print axioms Kreps.ConsumerDemand.Representation.monotone_of_some_representation
#print axioms Kreps.ConsumerDemand.Representation.strict_all_representations
#print axioms Kreps.ConsumerDemand.Representation.strict_of_some_representation
#print axioms Kreps.ConsumerDemand.Representation.strictlyMonotone_monotone
#print axioms Kreps.ConsumerDemand.Representation.strictlyMonotone_strictAllIncrease
#print axioms Kreps.ConsumerDemand.Representation.locallyInsatiable_iff_open
#print axioms Kreps.ConsumerDemand.Representation.locallyInsatiable_global
#print axioms Kreps.ConsumerDemand.Representation.globallyInsatiable_iff_utility
#print axioms Kreps.ConsumerDemand.Representation.locallyInsatiable_iff_utility
#print axioms Kreps.ConsumerDemand.Representation.RaisedBundle
#print axioms Kreps.ConsumerDemand.Representation.raisedBundle_dist_le
#print axioms Kreps.ConsumerDemand.Representation.strictAllIncrease_locallyInsatiable
#print axioms Kreps.ConsumerDemand.Representation.monotone_locallyInsatiable_strictAllIncrease
#print axioms Kreps.ConsumerDemand.Representation.continuous_strictAllIncrease_monotone
#print axioms Kreps.ConsumerDemand.Representation.problem_2_6
#print axioms Kreps.ConsumerDemand.Representation.UnitSegment
#print axioms Kreps.ConsumerDemand.Representation.LexicographicPreference
#print axioms Kreps.ConsumerDemand.Representation.lexicographic_rational
#print axioms Kreps.ConsumerDemand.Representation.lexicographic_not_representable
#print axioms Kreps.ConsumerDemand.Representation.problem_1_10
#print axioms Kreps.ConsumerDemand.Representation.proposition_2_9_forward
#print axioms Kreps.ConsumerDemand.Representation.compact_choice_of_continuous_utility
#print axioms Kreps.ConsumerDemand.Representation.indifference_on_connected_image
#print axioms Kreps.ConsumerDemand.Representation.lemma_2_10
#print axioms Kreps.ConsumerDemand.Representation.monotone_path_crossing
#print axioms Kreps.ConsumerDemand.Representation.StrictRankSeparator
#print axioms Kreps.ConsumerDemand.Representation.dense_strictRankSeparator
#print axioms Kreps.ConsumerDemand.Representation.InteriorRankSet
#print axioms Kreps.ConsumerDemand.Representation.interiorRank_witness
#print axioms Kreps.ConsumerDemand.Representation.interiorRank_between
#print axioms Kreps.ConsumerDemand.Representation.interiorRankSet_countable
#print axioms Kreps.ConsumerDemand.Representation.RationalUnit
#print axioms Kreps.ConsumerDemand.Representation.interiorRanks_orderIso
#print axioms Kreps.ConsumerDemand.Representation.RationalRankValue
#print axioms Kreps.ConsumerDemand.Representation.rationalRankValue_bounds
#print axioms Kreps.ConsumerDemand.Representation.rationalRankValue_strictMono
#print axioms Kreps.ConsumerDemand.Representation.RankCutSet
#print axioms Kreps.ConsumerDemand.Representation.rankCutSet_nonempty
#print axioms Kreps.ConsumerDemand.Representation.rankCutSet_bddAbove
#print axioms Kreps.ConsumerDemand.Representation.RankCutUtility
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_nonneg
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_le_one
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_mono
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_upper
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_lower
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_at_rank
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_strict
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_represents
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_attains_rationals
#print axioms Kreps.ConsumerDemand.Representation.continuous_of_dense_rational_range
#print axioms Kreps.ConsumerDemand.Representation.rankCutUtility_continuous
#print axioms Kreps.ConsumerDemand.Representation.continuous_represents_of_continuous_connected
#print axioms Kreps.ConsumerDemand.Representation.proposition_2_9
#print axioms Kreps.ConsumerDemand.Representation.proposition_2_9_metric
#print axioms Kreps.ConsumerDemand.ContinuousPreference
#print axioms Kreps.ConsumerDemand.continuous_utility_of_primitive_preferences
#print axioms Kreps.ConsumerDemand.preferenceChoice_eq_demand
#print axioms Kreps.ConsumerDemand.primitive_consumer_choice_nonempty
#print axioms Kreps.ConsumerDemand.problem_3_2_primitive
#print axioms Kreps.ConsumerDemand.FirstGoods
#print axioms Kreps.ConsumerDemand.mem_firstGoods
#print axioms Kreps.ConsumerDemand.cobbDouglas_scale_pos
#print axioms Kreps.ConsumerDemand.cobbDouglas_homothetic
#print axioms Kreps.ConsumerDemand.weightedLog_scale_pos
#print axioms Kreps.ConsumerDemand.logarithmic_positive_scaling_iff
#print axioms Kreps.ConsumerDemand.quasiconcave_direction_nonneg
#print axioms Kreps.ConsumerDemand.exists_better_strictly_affordable
#print axioms Kreps.ConsumerDemand.problem_3_11a
#print axioms Kreps.ConsumerDemand.CrusoeFeasible
#print axioms Kreps.ConsumerDemand.CrusoeObjective
#print axioms Kreps.ConsumerDemand.CrusoeDemand
#print axioms Kreps.ConsumerDemand.CrusoeValue
#print axioms Kreps.ConsumerDemand.crusoeFeasible_nonempty
#print axioms Kreps.ConsumerDemand.crusoeFeasible_isCompact
#print axioms Kreps.ConsumerDemand.crusoeObjective_continuous
#print axioms Kreps.ConsumerDemand.crusoeFeasible_continuous_selection
#print axioms Kreps.ConsumerDemand.crusoeFeasible_sequentialLower
#print axioms Kreps.ConsumerDemand.crusoeFeasible_sequentialUpper
#print axioms Kreps.ConsumerDemand.crusoeFeasible_localCompactBound
#print axioms Kreps.ConsumerDemand.problem_3_14a
#print axioms Kreps.ConsumerDemand.problem_3_14d
#print axioms Kreps.ConsumerDemand.crusoeValue_eq_of_optimum
#print axioms Kreps.ConsumerDemand.crusoeDemand_isCompact
#print axioms Kreps.ConsumerDemand.crusoeDemand_zero
#print axioms Kreps.ConsumerDemand.crusoeDemand_continuous_of_unique
#print axioms Kreps.ConsumerDemand.MonotoneFutureUtility
#print axioms Kreps.ConsumerDemand.StrictlyMonotoneFutureUtility
#print axioms Kreps.ConsumerDemand.crusoe_production_nonneg
#print axioms Kreps.ConsumerDemand.crusoe_stream_nonneg
#print axioms Kreps.ConsumerDemand.crusoeObjective_concave
#print axioms Kreps.ConsumerDemand.crusoeObjective_strictConcave_utility
#print axioms Kreps.ConsumerDemand.crusoeObjective_strictConcave_production
#print axioms Kreps.ConsumerDemand.problem_3_14b
#print axioms Kreps.ConsumerDemand.crusoeDemand_subsingleton_of_strictConcave
#print axioms Kreps.ConsumerDemand.problem_3_14c_utility
#print axioms Kreps.ConsumerDemand.problem_3_14c_production
#print axioms Kreps.ConsumerDemand.problem_3_14d_lower_utility
#print axioms Kreps.ConsumerDemand.problem_3_14d_lower_production
#print axioms Kreps.ConsumerDemand.separable_not_homothetic
#print axioms Kreps.ConsumerDemand.problem_3_10a_separable
#print axioms Kreps.ConsumerDemand.problem_3_10a_quasiLinear
#print axioms Kreps.ConsumerDemand.SeparableMarginals.strictMono_total
#print axioms Kreps.ConsumerDemand.one_good_strictMono_homothetic
#print axioms Kreps.ConsumerDemand.problem_3_10a_separable_one_good
#print axioms Kreps.ConsumerDemand.problem_3_10a_numeraire_only
#print axioms Kreps.ConsumerDemand.Problem34Utility
#print axioms Kreps.ConsumerDemand.Problem34Prices
#print axioms Kreps.ConsumerDemand.Problem34BundleFive
#print axioms Kreps.ConsumerDemand.Problem34BundleSixteenPointFour
#print axioms Kreps.ConsumerDemand.Problem34BundleHundred
#print axioms Kreps.ConsumerDemand.problem34Utility_eq
#print axioms Kreps.ConsumerDemand.problem_3_4_five
#print axioms Kreps.ConsumerDemand.problem_3_4_sixteenPointFour
#print axioms Kreps.ConsumerDemand.problem_3_4_hundred
#print axioms Kreps.ConsumerDemand.shiftedProduct_not_homothetic
#print axioms Kreps.ConsumerDemand.shiftedProduct_homothetic_iff_zero_shifts
#print axioms Kreps.ConsumerDemand.shiftedProduct_one_good_homothetic
#print axioms Kreps.ConsumerDemand.problem_3_10a_shifted_log
#print axioms Kreps.ConsumerDemand.StationaryCubic
#print axioms Kreps.ConsumerDemand.SingleQuantity
#print axioms Kreps.ConsumerDemand.UnitPrice
#print axioms Kreps.ConsumerDemand.stationaryCubic_increasing
#print axioms Kreps.ConsumerDemand.stationaryCubic_contDiff
#print axioms Kreps.ConsumerDemand.stationaryCubic_locallyInsatiable
#print axioms Kreps.ConsumerDemand.stationaryCubic_derivative_one
#print axioms Kreps.ConsumerDemand.stationaryCubic_conditions
#print axioms Kreps.ConsumerDemand.stationaryCubic_nonoptimal
#print axioms Kreps.ConsumerDemand.stationaryCubic_strictlyConvex
#print axioms Kreps.ConsumerDemand.stationaryCubic_quasiConcave
#print axioms Kreps.ConsumerDemand.stationaryCubic_demand
#print axioms Kreps.ConsumerDemand.stationaryCubic_multiplier_forced_zero
#print axioms Kreps.ConsumerDemand.stationaryCubic_strictMono
#print axioms Kreps.ConsumerDemand.problem_3_11b
#print axioms Kreps.ConsumerDemand.problem_3_12
