/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.LinearDemand

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
