/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.SeparableMarginals

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
