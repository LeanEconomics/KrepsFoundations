/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.AfriatTheorem
import Mathlib.Basic.NNReal.Basic

/-!
# Direct rankings, unique choices, and income effects

Kreps I, pp. 71 and 73-75. Afriat's regularity conclusion concerns finite market
data; directly elicited rankings can contradict convexity or monotonicity.
The stronger boundary comparison called WARP in the source requires unique
maximizers. Strict convexity suffices for uniqueness. Zero income forces zero
consumption, so globally nonincreasing nonnegative demand must vanish.

`StrictlyConvexPreference` is an attributed local copy from Chapter 2,
`ConvexPreference.lean`, originating at commit `7d496c5`.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A nontrivial mixture of distinct bundles is strictly above the worse endpoint. -/
def StrictlyConvexPreference {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- A strict preference for a coordinatewise dominated bundle rejects monotonicity. -/
theorem dominated_strict_ranking_not_monotone {x y : NonnegativeOrthant k}
    (hxy : x ≤ y) (hp : Strict r x y) : ¬(∀ a b, b ≤ a → r a b) :=
  fun hm => hp.2 (hm y x hxy)

/-- Strictly preferring both endpoints to their midpoint rejects convex preference. -/
theorem midpoint_strict_rankings_not_convex (hr : Rational r)
    (x y : NonnegativeOrthant k)
    (hx : Strict r x (Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num)))
    (hy : Strict r y (Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num))) :
    ¬ConvexPreference (convex_Ici (0 : Fin k → ℝ)) r := by
  intro hc
  rcases hr.1 x y with hxy | hyx
  · exact hy.2 (hc x y hxy (1 / 2) (by norm_num))
  · have he : Mix (convex_Ici (0 : Fin k → ℝ)) y x (1 / 2) (by norm_num) =
        Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num) := by
      apply Subtype.ext
      ext j
      simp only [Mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact hx.2 (he ▸ hc y x hyx (1 / 2) (by norm_num))

/-- Convex mixtures of affordable nonnegative bundles remain affordable. -/
theorem budget_mix {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ Budget p y) (hz : z ∈ Budget p y) {a : ℝ} (ha : a ∈ Set.Icc 0 1) :
    Mix (convex_Ici (0 : Fin k → ℝ)) x z a ha ∈ Budget p y := by
  change Expenditure p (a • x.val + (1 - a) • z.val) ≤ y
  have he := affineExpenditure_mix p x.val z.val a (1 - a)
  change Expenditure p (a • x.val + (1 - a) • z.val) =
    a * Expenditure p x.val + (1 - a) * Expenditure p z.val at he
  rw [he]
  change Expenditure p x.val ≤ y at hx
  change Expenditure p z.val ≤ y at hz
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx),
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hz)]

/-- Strict convexity makes the budget maximizer unique whenever it exists. -/
theorem strictlyConvex_budget_choice_unique
    (hc : StrictlyConvexPreference (convex_Ici (0 : Fin k → ℝ)) r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : z ∈ PrefChoice r (Budget p y)) : x = z := by
  by_contra hne
  have hs := hc x z hne (hx.2 z hz.1) (1 / 2) (by norm_num)
  exact hs.2 (hz.2 _ (budget_mix hx.1 hz.1 (by norm_num)))

/-- The source's WARP boundary comparison follows from uniqueness, not insatiability alone. -/
theorem unique_choice_strict (hr : Rational r) {A : Set (NonnegativeOrthant k)}
    {x z : NonnegativeOrthant k} (hx : x ∈ PrefChoice r A)
    (hu : ∀ w ∈ PrefChoice r A, w = x) (hz : z ∈ A) (hne : z ≠ x) : Strict r x z := by
  refine ⟨hx.2 z hz, ?_⟩
  intro hzx
  exact hne (hu z ⟨hz, fun w hw => hr.2 _ _ _ hzx (hx.2 w hw)⟩)

/-- Strictly convex preferences give the strict boundary comparison for every other bundle. -/
theorem strictlyConvex_choice_strict (hr : Rational r)
    (hc : StrictlyConvexPreference (convex_Ici (0 : Fin k → ℝ)) r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : z ∈ Budget p y) (hne : z ≠ x) :
    Strict r x z :=
  unique_choice_strict hr hx (fun _ hw => strictlyConvex_budget_choice_unique hc hw hx) hz hne

/-- Positive prices and zero income leave only the zero commodity vector affordable. -/
theorem zero_income_bundle_zero {p : Fin k → ℝ} (hp : ∀ i, 0 < p i)
    {x : NonnegativeOrthant k} (hx : x ∈ Budget p 0) : x.val = 0 := by
  ext i
  have hterm : p i * x.val i ≤ Expenditure p x.val :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hp j).le (x.property j)) (Finset.mem_univ i)
  have hnonpos : x.val i ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge (hterm.trans hx)) (mul_pos (hp i) hpos)
  exact le_antisymm hnonpos (x.property i)

/-- A nonnegative demand coordinate falling at every income must never be consumed. -/
theorem globally_inferior_demand_zero {p : Fin k → ℝ} (hp : ∀ i, 0 < p i)
    (d : NNReal → NonnegativeOrthant k) (hd : ∀ y : NNReal, d y ∈ Budget p (y : ℝ))
    (i : Fin k)
    (hfall : Antitone (fun y => (d y).val i)) : ∀ y, (d y).val i = 0 := by
  intro y
  have hz : (d 0).val i = 0 := congrFun (zero_income_bundle_zero hp (hd 0)) i
  have hle : (d y).val i ≤ (d 0).val i := hfall (show (0 : NNReal) ≤ y from zero_le)
  rw [hz] at hle
  exact le_antisymm hle ((d y).property i)

end Kreps.RevealedPreference
