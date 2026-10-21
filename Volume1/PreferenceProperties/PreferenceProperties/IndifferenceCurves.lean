/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousUtility
import PreferenceProperties.ConvexPreference

/-!
# The mathematical assertions in indifference-curve diagrams

Kreps I, Section 2.4, pp. 38-39. Local insatiability excludes a ball inside
an indifference class; strict monotonicity makes two-good curves decreasing;
strict convexity makes interior mixtures of distinct indifferent bundles better.
The path-crossing assertion is `monotone_path_crossing` in `ContinuousUtility`.
No smoothness assertion follows from these assumptions.
-/

namespace Kreps.PreferenceProperties

/-- The indifference class denoted I(x) in the chapter. -/
def IndifferenceClass {X : Type*} (r : X → X → Prop) (x : X) : Set X :=
  {y | Indifferent r y x}

/-- Local insatiability prevents any positive-radius ball from lying in one class. -/
theorem indifferenceClass_no_ball {X : Type*} [PseudoMetricSpace X] {r : X → X → Prop}
    (hr : Rational r) (hl : LocallyInsatiable r) (x z : X) {ε : ℝ} (hε : 0 < ε) :
    ¬Metric.ball z ε ⊆ IndifferenceClass r x := by
  intro hsub
  have hz : Indifferent r z x := hsub (by simpa using hε)
  obtain ⟨y, hy, hbetter⟩ := locallyInsatiable_iff_open.mp hl z ε hε
  have hyx : Indifferent r y x := hsub hy
  exact hbetter.2 (hr.2 z x y hz.1 hyx.2)

/-- Thus every indifference class has empty relative interior. -/
theorem indifferenceClass_interior_empty {X : Type*} [PseudoMetricSpace X]
    {r : X → X → Prop} (hr : Rational r) (hl : LocallyInsatiable r) (x : X) :
    interior (IndifferenceClass r x) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  exact indifferenceClass_no_ball hr hl x z hε (fun _ h => interior_subset (hb h))

/-- For two goods, strictly more of the first requires less of the second along a class. -/
theorem indifferenceCurve_decreasing
    {r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop}
    (hs : StrictlyMonotonePreference r) {x y : NonnegativeOrthant 2}
    (hi : Indifferent r y x) (hfirst : x.val 0 < y.val 0) : y.val 1 < x.val 1 := by
  by_contra hnot
  have hxy : x ≤ y := by
    intro j
    fin_cases j
    · exact hfirst.le
    · exact le_of_not_gt hnot
  have hne : y ≠ x := by
    intro he
    have h := congrArg (fun z : NonnegativeOrthant 2 => z.val 0) he
    linarith
  exact (hs y x hxy hne).2 hi.2

/-- Distinct indifferent endpoints have strictly better interior mixtures under strict convexity. -/
theorem indifference_mixture_strict {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {hS : Convex ℝ S} {r : S → S → Prop}
    (hs : StrictlyConvexPreference hS r) {x y : S} (hne : x ≠ y)
    (hi : Indifferent r x y) (a : ℝ) (ha : a ∈ Set.Ioo 0 1) :
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y :=
  hs x y hne hi.1 a ha

end Kreps.PreferenceProperties
