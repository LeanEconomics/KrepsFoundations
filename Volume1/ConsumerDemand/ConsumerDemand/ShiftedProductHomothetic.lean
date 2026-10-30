/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.ShiftedDemandProcedure
import ConsumerDemand.ProductHomogeneity
import ConsumerDemand.SeparableNonhomothetic
import ConsumerDemand.ShiftedLogExample

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
