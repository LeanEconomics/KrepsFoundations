/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConvexityExamples
import PreferenceProperties.Monotonicity

/-!
# The open and unbounded menu examples

Kreps I, introductory examples in Problem 2.2, p. 46. Strictly monotone preference
on the nonnegative half-line has no best point on `(1,5)` or `(3,∞)`, although both
menus are nonempty and convex. The compact-menu counterexample is proved separately
in `ConvexityExamples`.
-/

namespace Kreps.PreferenceProperties

/-- A relatively open bounded interval in the one-good consumption domain. -/
def OpenIntervalMenu (a b : ℝ) : Set OneGood := {x | a < x.val ∧ x.val < b}

/-- An open upper ray in the one-good consumption domain. -/
def UpperRayMenu (a : ℝ) : Set OneGood := {x | a < x.val}

/-- The bounded interval menu is convex, including when it is empty. -/
theorem openIntervalMenu_convex (a b : ℝ) :
    ConvexMenu (convex_Ici (0 : ℝ)) (OpenIntervalMenu a b) := by
  intro x hx y hy t ht
  exact (convex_Ioo a b) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)

/-- The upper-ray menu is convex. -/
theorem upperRayMenu_convex (a : ℝ) :
    ConvexMenu (convex_Ici (0 : ℝ)) (UpperRayMenu a) := by
  intro x hx y hy t ht
  exact (convex_Ioi a) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)

/-- Moving halfway toward the excluded upper endpoint beats every point of an open interval. -/
theorem strictlyMonotone_openInterval_empty {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) (a b : ℝ) : PrefChoice r (OpenIntervalMenu a b) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxb : x.val < b := hx.1.2
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨(x.val + b) / 2, show 0 ≤ (x.val + b) / 2 from by linarith⟩
  have hyx : x < y := by change x.val < (x.val + b) / 2; linarith
  have hy : y ∈ OpenIntervalMenu a b := by
    change a < (x.val + b) / 2 ∧ (x.val + b) / 2 < b
    have hax : a < x.val := hx.1.1
    constructor <;> linarith
  exact (hm y x hyx.le (ne_of_gt hyx)).2 (hx.2 y hy)

/-- Adding one unit beats every point of the unbounded upper-ray menu. -/
theorem strictlyMonotone_upperRay_empty {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) (a : ℝ) : PrefChoice r (UpperRayMenu a) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx0 : 0 ≤ x.val := x.property
  let y : OneGood := ⟨x.val + 1, show 0 ≤ x.val + 1 from by linarith⟩
  have hyx : x < y := by change x.val < x.val + 1; linarith
  have hy : y ∈ UpperRayMenu a := by
    change a < x.val + 1
    have hax : a < x.val := hx.1
    linarith
  exact (hm y x hyx.le (ne_of_gt hyx)).2 (hx.2 y hy)

/-- **Problem 2.2**, introductory examples: both nonempty convex menus have empty best sets. -/
theorem problem_2_2_intervals {r : OneGood → OneGood → Prop}
    (hm : StrictlyMonotonePreference r) :
    (OpenIntervalMenu 1 5).Nonempty ∧ ConvexMenu (convex_Ici (0 : ℝ)) (OpenIntervalMenu 1 5) ∧
      PrefChoice r (OpenIntervalMenu 1 5) = ∅ ∧ (UpperRayMenu 3).Nonempty ∧
      ConvexMenu (convex_Ici (0 : ℝ)) (UpperRayMenu 3) ∧ PrefChoice r (UpperRayMenu 3) = ∅ := by
  refine ⟨⟨⟨3, by norm_num⟩, by norm_num [OpenIntervalMenu]⟩,
    openIntervalMenu_convex 1 5, strictlyMonotone_openInterval_empty hm 1 5,
    ⟨⟨4, by norm_num⟩, by norm_num [UpperRayMenu]⟩,
    upperRayMenu_convex 3, strictlyMonotone_upperRay_empty hm 3⟩

end Kreps.PreferenceProperties
