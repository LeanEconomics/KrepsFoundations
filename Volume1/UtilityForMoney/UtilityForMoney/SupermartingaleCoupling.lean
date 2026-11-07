/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CouplingSeparation
import UtilityForMoney.DominanceFiniteMinimum
import UtilityForMoney.StochasticDominance

/-!
# Constructing a supermartingale coupling from second-order dominance

Kreps I, Proposition 6.15(b), pp. 133–134. If the marginal and conditional-mean
constraints had no solution, finite separation would give a dual certificate.
The minimum of its affine rows is an increasing concave prize utility strictly
favoring the second lottery, contrary to dominance. The resulting joint law
allows arbitrary finite supports and arbitrary real probabilities.
-/

namespace Kreps.UtilityForMoney

open DominanceTools

/-- The lower envelope of affine rows with nonnegative slopes is nondecreasing and concave. -/
theorem increasing_concave_envelope {I : Type*} [Fintype I] [Nonempty I]
    (x a c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    let U := FiniteMinimum (fun i z => a i + c i * (z - x i))
    Monotone U ∧ ConcaveOn ℝ Set.univ U := by
  constructor
  · intro s t hst
    obtain ⟨i, hi⟩ := finiteMinimum_attained (fun i z => a i + c i * (z - x i)) t
    apply (finiteMinimum_le _ s i).trans
    change _ ≤ FiniteMinimum _ t
    rw [hi]
    gcongr
    exact hc i
  · apply finiteMinimum_concaveOn
    intro i
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ l h _ _ hs
    simp only [smul_eq_mul]
    apply le_of_eq
    calc
      _ = (l + h) * a i + c i * ((l * s + h * t) - (l + h) * x i) := by ring
      _ = _ := by rw [hs]; ring

/-- Summing over support subtypes gives the book's expected utility without any zero-mass rows. -/
theorem sum_support_utility (p : SimpleLottery ℝ) (U : ℝ → ℝ) :
    ∑ i : p.weights.support, p.weights i.val * U i.val = ExpectedUtility U p := by
  exact Finset.sum_coe_sort p.weights.support (fun x => p.weights x * U x)

/-- Proposition 6.15(b), existence direction. Every second-order ranking has a joint law
whose second prize has nonpositive expected increment conditional on the first prize. -/
theorem supermartingaleCoupling_of_dominance {p q : SimpleLottery ℝ}
    (hdom : SecondOrderDominates p q) : ∃ C : FiniteCoupling p q, C.NonpositiveDrift := by
  classical
  let I := ↥p.weights.support
  let J := ↥q.weights.support
  let : Nonempty I := lottery_support_nonempty p
  let : Nonempty J := lottery_support_nonempty q
  let wp (i : I) := p.weights i.val
  let wq (j : J) := q.weights j.val
  obtain h | h := coupling_or_separation wp wq (fun i : I => i.val) (fun j : J => j.val)
  · obtain ⟨w, hrow, hcol, hmean⟩ := h
    exact ⟨⟨fun i j => w.weights (i, j), fun i j => w.nonneg (i, j), hrow, hcol⟩, hmean⟩
  · obtain ⟨a, b, c, hc, hsep⟩ := h
    let L (i : I) (z : ℝ) := a i + c i * (z - i.val)
    let U := FiniteMinimum L
    have hreg : Monotone U ∧ ConcaveOn ℝ Set.univ U :=
      increasing_concave_envelope (fun i : I => i.val) a c hc
    let A := ∑ i, wp i * a i
    let B := ∑ j, wq j * b j
    have hcol (j : J) : A + B - b j < U j.val := by
      obtain ⟨i, hi⟩ := finiteMinimum_attained L j.val
      change _ < FiniteMinimum L j.val
      rw [hi]
      have hj : A + B < a i + b j + c i * (j.val - i.val) := hsep i j
      dsimp only [L]
      linarith
    have hrow (i : I) : U i.val ≤ a i := by
      simpa only [L, sub_self, mul_zero, add_zero] using finiteMinimum_le L i.val i
    have hq : (∑ j, wq j * (A + B - b j)) < ∑ j : J, wq j * U j.val := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro j _
      exact mul_lt_mul_of_pos_left (hcol j)
        (lt_of_le_of_ne (q.nonneg j.val) (Ne.symm (Finsupp.mem_support_iff.mp j.property)))
    have hre : ∑ j, wq j * (A + B - b j) = A := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, wq]
      rw [support_mass_sum, one_mul]
      dsimp [B, wq]
      ring
    rw [hre, show ∑ j : J, wq j * U j.val = ExpectedUtility U q from sum_support_utility q U] at hq
    have hp : ExpectedUtility U p ≤ A := by
      rw [← sum_support_utility]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (p.nonneg i.val)
    exact (hq.not_ge ((hdom U hreg.1 hreg.2).trans hp)).elim

end Kreps.UtilityForMoney
