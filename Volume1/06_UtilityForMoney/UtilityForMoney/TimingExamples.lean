/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Committing to a consumption quantity before learning income

Kreps I, Problem 6.7, pp. 142–143. Both prices equal one. Write `w = 1 + x₁`
and `Nᵢ = yᵢ + 2`. Spending the remaining income in state `i` gives
`1 + x₂ = Nᵢ - w`. A single choice of `w` must be feasible in every state.
The logarithmic support inequalities adapt Chapter 3's `LogarithmicSupport`
at commit `f9c357ada1d9965dabd9eec694720ba585faf575`.
-/

namespace Kreps.UtilityForMoney

/-- Feasible precommitments in the shifted variable, including both consumption boundaries. -/
def TimingMenu {n : ℕ} (N : Fin n → ℝ) : Set ℝ :=
  {w | 1 ≤ w ∧ ∀ i, w ≤ N i - 1}

/-- Mean indirect utility at one common first-good commitment in equiprobable states. -/
noncomputable def TimingValue {n : ℕ} (N : Fin n → ℝ) (w : ℝ) : ℝ :=
  ((n : ℝ) * Real.log w + ∑ i, Real.log (N i - w)) / n

/-- Sum of the marginal utilities of precommitting more first-good consumption. -/
noncomputable def TimingMarginal {n : ℕ} (N : Fin n → ℝ) (w : ℝ) : ℝ :=
  (n : ℝ) / w - ∑ i, 1 / (N i - w)

/-- For fixed first consumption, greater second consumption strictly increases bundle utility. -/
theorem spending_remainder_optimal {y x z : ℝ} (hz : 0 ≤ z) (hslack : x + z < y) :
    Real.log (x + 1) + Real.log (z + 1) < Real.log (x + 1) + Real.log (y - x + 1) := by
  have hg := Real.log_lt_log (by linarith : 0 < z + 1) (by linarith : z + 1 < y - x + 1)
  linarith

/-- Log utility lies below its tangent at every positive consumption. -/
theorem timing_log_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log z - Real.log x ≤ (z - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz hx)
  rw [Real.log_div hz.ne' hx.ne'] at h
  convert h using 1
  field_simp

/-- The tangent bound is strict for a different positive consumption. -/
theorem timing_log_tangent_strict {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (hn : z ≠ x) :
    Real.log z - Real.log x < (z - x) / x := by
  have h := Real.log_lt_sub_one_of_pos (div_pos hz hx)
    (fun h => hn ((div_eq_one_iff_eq hx.ne').mp h))
  rw [Real.log_div hz.ne' hx.ne'] at h
  convert h using 1
  field_simp

/-- A feasible zero marginal is the unique global optimum among common commitments. -/
theorem timing_unique_of_marginal {n : ℕ} (hn : 0 < n) (N : Fin n → ℝ) {w : ℝ}
    (hw : w ∈ TimingMenu N) (hopt : TimingMarginal N w = 0) {z : ℝ}
    (hz : z ∈ TimingMenu N) (hne : z ≠ w) : TimingValue N z < TimingValue N w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfst := timing_log_tangent_strict (zero_lt_one.trans_le hw.1)
    (zero_lt_one.trans_le hz.1) hne
  have hsnd : ∑ i, (Real.log (N i - z) - Real.log (N i - w)) ≤
      (w - z) * ∑ i, 1 / (N i - w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hp := timing_log_tangent (by linarith [hw.2 i] : 0 < N i - w)
      (by linarith [hz.2 i] : 0 < N i - z)
    convert hp using 1
    ring
  have he : ∑ i, 1 / (N i - w) = (n : ℝ) / w := (sub_eq_zero.mp hopt).symm
  rw [Finset.sum_sub_distrib, he] at hsnd
  have heq : (n : ℝ) * ((z - w) / w) + (w - z) * (n / w) = 0 := by ring
  unfold TimingValue
  apply (div_lt_div_iff_of_pos_right hn').mpr
  linarith only [hsnd, mul_lt_mul_of_pos_left hfst hn', heq]

/-- The two shifted incomes for the source's equal lottery over 98 and 178. -/
def TimingTwo : Fin 2 → ℝ := ![100, 180]

/-- The sure income is the printed finite decimal, interpreted exactly. -/
def TimingSure : Fin 1 → ℝ := fun _ => 128.948391819

/-- The three shifted incomes, with equal probabilities. -/
def TimingThree : Fin 3 → ℝ := ![100, 180, 128.948391819]

/-- The common commitment in the binary lottery is exactly 59 units of the first good. -/
theorem timing_two_optimum :
    (60 : ℝ) ∈ TimingMenu TimingTwo ∧
      ∀ z ∈ TimingMenu TimingTwo, z ≠ 60 → TimingValue TimingTwo z < TimingValue TimingTwo 60 := by
  have h : (60 : ℝ) ∈ TimingMenu TimingTwo :=
    ⟨by norm_num, fun i => by fin_cases i <;> norm_num [TimingTwo]⟩
  exact ⟨h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h
    (by norm_num [TimingMarginal, TimingTwo, Fin.sum_univ_two]) hz hn⟩

/-- The certain-income commitment is 63.4741959095 units of the first good. -/
theorem timing_sure_optimum :
    (64.4741959095 : ℝ) ∈ TimingMenu TimingSure ∧ ∀ z ∈ TimingMenu TimingSure,
      z ≠ 64.4741959095 → TimingValue TimingSure z < TimingValue TimingSure 64.4741959095 := by
  have h : (64.4741959095 : ℝ) ∈ TimingMenu TimingSure :=
    ⟨by norm_num, fun _ => by norm_num [TimingSure]⟩
  exact ⟨h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h
    (by norm_num [TimingMarginal, TimingSure, Fin.sum_univ_one]) hz hn⟩

/-- The three-state first-order condition has a root inside the certified decimal bracket. -/
theorem timing_three_root : ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610,
    TimingMarginal TimingThree w = 0 := by
  have hc : ContinuousOn (TimingMarginal TimingThree) (Set.Icc 61.2389938609 61.2389938610) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div continuousOn_id fun x hx => by linarith [hx.1]
    · apply continuousOn_finsetSum
      intro i _
      apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      intro x hx
      fin_cases i <;> norm_num [TimingThree] <;> linarith [hx.2]
  apply intermediate_value_Icc' (by norm_num) hc
  constructor <;> norm_num [TimingMarginal, TimingThree, Fin.sum_univ_succ]

/-- Every distinct feasible precommitment is worse than the three-state root. -/
theorem timing_three_optimum : ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610,
    w ∈ TimingMenu TimingThree ∧ ∀ z ∈ TimingMenu TimingThree,
      z ≠ w → TimingValue TimingThree z < TimingValue TimingThree w := by
  obtain ⟨w, hbounds, hw⟩ := timing_three_root
  have h : w ∈ TimingMenu TimingThree := by
    refine ⟨by linarith [hbounds.1], fun i => ?_⟩
    fin_cases i <;> norm_num [TimingThree] <;> linarith [hbounds.2]
  exact ⟨w, hbounds, h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h hw hz hn⟩

end Kreps.UtilityForMoney
