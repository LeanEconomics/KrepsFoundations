/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.AfriatTheorem
import RevealedPreference.ComparativeStatics

/-!
# A two-good Giffen example with unique choices

Kreps I, Problem 4.3, p. 78, asks for an indifference-curve diagram showing a
Giffen good. The formula and numbers below are a constructed witness, not an
example specified by Kreps. Utility is the minimum of two increasing affine
functions on the full nonnegative orthant. At income ten, raising only the first
price from one to two changes unique demand from `(1,9)` to `(2,6)`.

The reproducible diagram `docs/assets/giffen-example.svg` plots these exact budget
lines and utility levels; `scripts/plot_giffen_example.py` generates it. All
feasibility, global optimality and uniqueness claims are proved here independently
of plotting or numerical optimization.
-/

namespace Kreps.RevealedPreference

/-- A constructed concave utility, defined on all real two-good vectors. -/
def GiffenUtility (x : Fin 2 → ℝ) : ℝ :=
  min (x 0 + 2 * x 1) (13 * x 0 + 6 * x 1 - 48)

/-- The preference used by the example, on the entire nonnegative consumption domain. -/
def GiffenPreference : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop :=
  UtilityPref (fun x => GiffenUtility x.val)

/-- Both goods initially have unit prices. -/
def GiffenOldPrices : Fin 2 → ℝ := ![1, 1]

/-- Only the price of the first good rises, from one to two. -/
def GiffenNewPrices : Fin 2 → ℝ := ![2, 1]

/-- The unique original consumption bundle in the constructed example. -/
def GiffenOldBundle : NonnegativeOrthant 2 :=
  ⟨![1, 9], by intro j; fin_cases j <;> norm_num⟩

/-- The unique new bundle buys more of the now more expensive first good. -/
def GiffenNewBundle : NonnegativeOrthant 2 :=
  ⟨![2, 6], by intro j; fin_cases j <;> norm_num⟩

/-- The constructed utility is continuous everywhere, including on the orthant boundary. -/
theorem giffenUtility_continuous : Continuous GiffenUtility := by
  unfold GiffenUtility
  fun_prop

/-- Both affine pieces are concave, so their minimum is concave on the full vector space. -/
theorem giffenUtility_concaveOn : ConcaveOn ℝ Set.univ GiffenUtility := by
  have hfirst : ConcaveOn ℝ Set.univ (fun x : Fin 2 → ℝ => x 0 + 2 * x 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hsecond : ConcaveOn ℝ Set.univ
      (fun x : Fin 2 → ℝ => 13 * x 0 + 6 * x 1 - 48) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  exact hfirst.inf hsecond

/-- Increasing some coordinate and decreasing none strictly increases the constructed utility. -/
theorem giffenUtility_strictMono : StrictMono GiffenUtility := by
  intro x y hxy
  have hfirst := affineExpenditure_strictMono
    (p := (![1, 2] : Fin 2 → ℝ)) (by intro j; fin_cases j <;> norm_num) hxy
  have hsecond := affineExpenditure_strictMono
    (p := (![13, 6] : Fin 2 → ℝ)) (by intro j; fin_cases j <;> norm_num) hxy
  simp only [AffineExpenditure, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Fin.sum_univ_zero, add_zero, one_mul] at hfirst hsecond
  exact lt_min ((min_le_left _ _).trans_lt hfirst)
    ((min_le_right _ _).trans_lt (sub_lt_sub_right hsecond 48))

/-- The full-domain constructed preference has all the regularity properties in Afriat's theorem. -/
theorem giffenPreference_regular :
    Rational GiffenPreference ∧ ContinuousPreference GiffenPreference ∧
      StrictlyMonotonePreference GiffenPreference ∧ LocallyInsatiable GiffenPreference ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) GiffenPreference := by
  have hm : StrictlyMonotonePreference GiffenPreference :=
    strictlyMonotonePreference_of_strictMono (fun _ _ h => giffenUtility_strictMono h)
  exact ⟨utilityPref_rational _,
    continuousPreference_of_continuous_utility
      (giffenUtility_continuous.comp continuous_subtype_val), hm,
    strictlyMonotone_locallyInsatiable (by norm_num) hm,
    convexPreference_of_concaveOn giffenUtility_concaveOn⟩

/-- Every price is strictly positive in each of the two observations. -/
theorem giffenPrices_positive (j : Fin 2) :
    0 < GiffenOldPrices j ∧ 0 < GiffenNewPrices j := by
  fin_cases j <;> norm_num [GiffenOldPrices, GiffenNewPrices]

/-- The price change is exactly an increase of the first commodity's price. -/
theorem giffenPrices_ownPriceIncrease : OwnPriceIncrease GiffenOldPrices GiffenNewPrices 0 := by
  constructor
  · norm_num [GiffenOldPrices, GiffenNewPrices]
  · intro j hj
    fin_cases j <;> simp_all [GiffenOldPrices, GiffenNewPrices]

/-- The original bundle is affordable at income ten. -/
theorem giffen_old_feasible : GiffenOldBundle ∈ Budget GiffenOldPrices 10 := by
  norm_num [Budget, Expenditure, GiffenOldPrices, GiffenOldBundle, Fin.sum_univ_succ]

/-- The new bundle is affordable at income ten after the first price increases. -/
theorem giffen_new_feasible : GiffenNewBundle ∈ Budget GiffenNewPrices 10 := by
  norm_num [Budget, Expenditure, GiffenNewPrices, GiffenNewBundle, Fin.sum_univ_succ]

/-- Each selected bundle uses exactly the same income, ten, at its corresponding prices. -/
theorem giffen_budget_exhaustion :
    Expenditure GiffenOldPrices GiffenOldBundle.val = 10 ∧
      Expenditure GiffenNewPrices GiffenNewBundle.val = 10 := by
  norm_num [Expenditure, GiffenOldPrices, GiffenNewPrices, GiffenOldBundle,
    GiffenNewBundle, Fin.sum_univ_succ]

/-- The original optimum lies on the indifference curve of utility nineteen. -/
theorem giffen_old_value : GiffenUtility GiffenOldBundle.val = 19 := by
  norm_num [GiffenUtility, GiffenOldBundle]

/-- The new optimum lies on the indifference curve of utility fourteen. -/
theorem giffen_new_value : GiffenUtility GiffenNewBundle.val = 14 := by
  norm_num [GiffenUtility, GiffenNewBundle]

/-- Every originally affordable bundle gives utility at most nineteen. -/
theorem giffen_old_maximum {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenOldPrices 10) : GiffenUtility x.val ≤ 19 := by
  have hb : x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenOldPrices, Fin.sum_univ_succ] using hx
  by_cases hfirst : x.val 0 ≤ 1
  · exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-- Equality in the old budget bound forces exactly the original bundle. -/
theorem giffen_old_unique {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenOldPrices 10) (hu : 19 ≤ GiffenUtility x.val) :
    x = GiffenOldBundle := by
  have hb : x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenOldPrices, Fin.sum_univ_succ] using hx
  obtain ⟨hfirst, hsecond⟩ := le_min_iff.mp hu
  have hzero : x.val 0 = 1 := by linarith
  have hone : x.val 1 = 9 := by linarith
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hzero
  · exact hone

/-- Every bundle affordable after the price rise gives utility at most fourteen. -/
theorem giffen_new_maximum {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenNewPrices 10) : GiffenUtility x.val ≤ 14 := by
  have hb : 2 * x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenNewPrices, Fin.sum_univ_succ] using hx
  by_cases hfirst : x.val 0 ≤ 2
  · exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-- Equality in the new budget bound forces exactly the new bundle. -/
theorem giffen_new_unique {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenNewPrices 10) (hu : 14 ≤ GiffenUtility x.val) :
    x = GiffenNewBundle := by
  have hb : 2 * x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenNewPrices, Fin.sum_univ_succ] using hx
  obtain ⟨hfirst, hsecond⟩ := le_min_iff.mp hu
  have hzero : x.val 0 = 2 := by linarith
  have hone : x.val 1 = 6 := by linarith
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hzero
  · exact hone

/-- The entire original choice set consists of the single bundle `(1,9)`. -/
theorem giffen_old_choice :
    PrefChoice GiffenPreference (Budget GiffenOldPrices 10) = {GiffenOldBundle} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply giffen_old_unique hx.1
    have h := hx.2 GiffenOldBundle giffen_old_feasible
    change GiffenUtility GiffenOldBundle.val ≤ GiffenUtility x.val at h
    rwa [giffen_old_value] at h
  · rintro rfl
    refine ⟨giffen_old_feasible, ?_⟩
    intro z hz
    change GiffenUtility z.val ≤ GiffenUtility GiffenOldBundle.val
    rw [giffen_old_value]
    exact giffen_old_maximum hz

/-- The entire new choice set consists of the single bundle `(2,6)`. -/
theorem giffen_new_choice :
    PrefChoice GiffenPreference (Budget GiffenNewPrices 10) = {GiffenNewBundle} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply giffen_new_unique hx.1
    have h := hx.2 GiffenNewBundle giffen_new_feasible
    change GiffenUtility GiffenNewBundle.val ≤ GiffenUtility x.val at h
    rwa [giffen_new_value] at h
  · rintro rfl
    refine ⟨giffen_new_feasible, ?_⟩
    intro z hz
    change GiffenUtility z.val ≤ GiffenUtility GiffenNewBundle.val
    rw [giffen_new_value]
    exact giffen_new_maximum hz

/-- **Problem 4.3:** the same regular preference has unique demand rising with its own price. -/
theorem problem_4_3 :
    Rational GiffenPreference ∧ ContinuousPreference GiffenPreference ∧
      StrictlyMonotonePreference GiffenPreference ∧ LocallyInsatiable GiffenPreference ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) GiffenPreference ∧
      OwnPriceIncrease GiffenOldPrices GiffenNewPrices 0 ∧
      PrefChoice GiffenPreference (Budget GiffenOldPrices 10) = {GiffenOldBundle} ∧
      PrefChoice GiffenPreference (Budget GiffenNewPrices 10) = {GiffenNewBundle} ∧
      GiffenOldBundle.val 0 < GiffenNewBundle.val 0 := by
  obtain ⟨hr, hc, hm, hl, hv⟩ := giffenPreference_regular
  exact ⟨hr, hc, hm, hl, hv, giffenPrices_ownPriceIncrease, giffen_old_choice,
    giffen_new_choice, by norm_num [GiffenOldBundle, GiffenNewBundle]⟩

end Kreps.RevealedPreference
