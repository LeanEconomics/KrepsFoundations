/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality
import Mathlib.Analysis.SpecificLimits.Basic

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
