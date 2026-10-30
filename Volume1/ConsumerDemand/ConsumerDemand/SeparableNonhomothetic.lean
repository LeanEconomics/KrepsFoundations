/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.SeparableDemand
import ConsumerDemand.QuasiLinearDemand
import ConsumerDemand.HomotheticDemand

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
