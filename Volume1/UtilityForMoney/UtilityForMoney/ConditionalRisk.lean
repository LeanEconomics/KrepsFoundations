/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.SupermartingaleCoupling

/-!
# Conditional Jensen inequality for stochastic dominance

Kreps I, Proposition 6.15(b) and Problem 6.6(b), pp. 133, 142. Each positive
row mass normalizes its row to a conditional probability vector. Jensen's
inequality in that row and nonnegative monotonicity give the comparison, which
is then averaged using the two actual marginal laws.
-/

namespace Kreps.UtilityForMoney

/-- A row of nonpositive mean drift cannot increase conditional expected utility. -/
theorem FiniteCoupling.row_utility_le {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (hc : C.NonpositiveDrift) (U : ℝ → ℝ) (hi : Monotone U) (hu : ConcaveOn ℝ Set.univ U)
    (i : p.weights.support) :
    ∑ j : q.weights.support, C.mass i j * U j.val ≤ p.weights i.val * U i.val := by
  classical
  have hpos : 0 < p.weights i.val :=
    lt_of_le_of_ne (p.nonneg _) (Ne.symm (Finsupp.mem_support_iff.mp i.property))
  let w := fun j : q.weights.support => C.mass i j / p.weights i.val
  have hw (j) : 0 ≤ w j := div_nonneg (C.nonneg _ _) hpos.le
  have hsum : ∑ j, w j = 1 := by
    change (∑ j : q.weights.support, C.mass i j / p.weights i.val) = 1
    rw [← Finset.sum_div, C.row_sum, div_self hpos.ne']
  have hmean : ∑ j : q.weights.support, w j * j.val ≤ i.val := by
    have h := (C.nonpositiveDrift_iff.mp hc) i
    unfold FiniteCoupling.conditionalDrift at h
    change ∑ j : q.weights.support, w j * (j.val - i.val) ≤ 0 at h
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul,
      sub_nonpos] using h
  have hj := hu.le_map_sum (t := Finset.univ) (w := w) (p := fun j : q.weights.support => j.val)
    (fun j _ => hw j) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have he := mul_le_mul_of_nonneg_left (hj.trans (hi hmean)) hpos.le
  rw [Finset.mul_sum] at he
  have heq (j : q.weights.support) : p.weights i.val * (w j * U j.val) = C.mass i j * U j.val := by
    dsimp [w]
    field_simp
  simpa only [heq] using he

/-- **Problem 6.6(b):** a nonpositive conditional supplement implies second-order dominance. -/
theorem secondOrder_of_supermartingaleCoupling {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (hc : C.NonpositiveDrift) : SecondOrderDominates p q := by
  intro U hi hu
  rw [← sum_support_utility, ← sum_support_utility]
  calc
    ∑ j : q.weights.support, q.weights j.val * U j.val =
        ∑ j : q.weights.support, ∑ i : p.weights.support, C.mass i j * U j.val := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_mul, C.col_sum]
    _ = ∑ i : p.weights.support, ∑ j : q.weights.support, C.mass i j * U j.val :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => C.row_utility_le hc U hi hu i

/-- **Proposition 6.15(b):** second-order dominance iff a joint law has nonpositive conditional
supplement in every row of the first marginal. -/
theorem proposition_6_15b (p q : SimpleLottery ℝ) :
    SecondOrderDominates p q ↔ ∃ C : FiniteCoupling p q, C.NonpositiveDrift :=
  ⟨supermartingaleCoupling_of_dominance, fun ⟨C, h⟩ => secondOrder_of_supermartingaleCoupling C h⟩

end Kreps.UtilityForMoney
