/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.PolygonalCurve
import PreferenceProperties.NumericalRankBrackets
import PreferenceProperties.RepresentationExtension

/-!
# A reference curve meeting every indifference class

Kreps I, Problem 2.14(a)-(b), p. 48. From any numerical representation, choose
a countable sequence bracketing all ranks and join the points by affine segments.
When best and worst ranks are both attained, a single segment suffices. Otherwise
the countable construction handles each of the remaining three extrema cases.
The connected-image crossing lemma then makes the curve meet every class.

The final theorem assembles parts (a)-(g): construct the curve, run the exact
recursive scale on an augmented dense subset of its image, and extend by indifference.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- A countable sequence of weak rank bounds gives a continuous bracketing polygonal curve. -/
theorem exists_bracketing_polygonal_curve [Nonempty S] (hS : Convex ℝ S)
    {r : S → S → Prop} {v : S → ℝ} (hv : Represents v r) :
    ∃ q : ℕ → S, Continuous (SequenceCurve hS q) ∧
      ∀ x, ∃ a b : ℝ, r (SequenceCurve hS q a) x ∧ r x (SequenceCurve hS q b) := by
  obtain ⟨q, hq⟩ := exists_preference_bracketing_sequence hv
  refine ⟨q, sequenceCurve_continuous hS q, fun x => ?_⟩
  obtain ⟨i, j, hi, hj⟩ := hq x
  refine ⟨i, j, ?_⟩
  simpa only [sequenceCurve_nat] using And.intro hi hj

/-- The single segment from a best point to a worst point. -/
def ExtremeReferenceSegment (hS : Convex ℝ S) (best worst : S) (t : UnitSegment) : S :=
  Mix hS worst best t.val t.property

/-- The segment starts at the best point. -/
theorem extremeReferenceSegment_zero (hS : Convex ℝ S) (best worst : S) :
    ExtremeReferenceSegment hS best worst ⟨0, by norm_num⟩ = best :=
  mix_zero hS worst best _

/-- The segment ends at the worst point. -/
theorem extremeReferenceSegment_one (hS : Convex ℝ S) (best worst : S) :
    ExtremeReferenceSegment hS best worst ⟨1, by norm_num⟩ = worst :=
  mix_one hS worst best _

/-- The one-segment construction is continuous. -/
theorem extremeReferenceSegment_continuous (hS : Convex ℝ S) (best worst : S) :
    Continuous (ExtremeReferenceSegment hS best worst) := by
  have h : Continuous (fun t : UnitSegment =>
      t.val • worst.val + (1 - t.val) • best.val) := by fun_prop
  exact h.subtype_mk _

/-- The both-extrema-attained case in **Problem 2.14(a)** uses only one line segment. -/
theorem problem_2_14a_both_extrema (hS : Convex ℝ S) {r : S → S → Prop}
    (best worst : S) (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) :
    Continuous (ExtremeReferenceSegment hS best worst) ∧
      ∀ x, r (ExtremeReferenceSegment hS best worst ⟨0, by norm_num⟩) x ∧
        r x (ExtremeReferenceSegment hS best worst ⟨1, by norm_num⟩) := by
  refine ⟨extremeReferenceSegment_continuous hS best worst, fun x => ?_⟩
  rw [extremeReferenceSegment_zero, extremeReferenceSegment_one]
  exact ⟨hbest x, hworst x⟩

/-- In the both-extrema case the single segment crosses every indifference class. -/
theorem extremeReferenceSegment_covers (hS : Convex ℝ S) {r : S → S → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) (best worst : S)
    (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) (x : S) :
    ∃ t, Indifferent r (ExtremeReferenceSegment hS best worst t) x := by
  have h := problem_2_14a_both_extrema hS best worst hbest hworst
  exact lemma_2_10 hr hc _ h.1 x (h.2 x).1 (h.2 x).2

/-- A two-point list continued constantly has just one nonconstant affine segment. -/
def ExtremeReferenceSequence (best worst : S) (n : ℕ) : S := if n = 0 then best else worst

/-- The two-point sequence starts at its best point. -/
theorem extremeReferenceSequence_curve_zero (hS : Convex ℝ S) (best worst : S) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) 0 = best := by
  simpa only [Nat.cast_zero, ExtremeReferenceSequence, ite_true] using
    sequenceCurve_nat hS (ExtremeReferenceSequence best worst) 0

/-- Its first affine segment ends at its worst point. -/
theorem extremeReferenceSequence_curve_one (hS : Convex ℝ S) (best worst : S) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) 1 = worst := by
  simpa only [Nat.cast_one, ExtremeReferenceSequence, one_ne_zero, ite_false] using
    sequenceCurve_nat hS (ExtremeReferenceSequence best worst) 1

/-- On the unit interval the two-point polygonal curve is exactly the single segment. -/
theorem extremeReferenceSequence_on_unit (hS : Convex ℝ S) (best worst : S)
    (t : UnitSegment) :
    SequenceCurve hS (ExtremeReferenceSequence best worst) t.val =
      ExtremeReferenceSegment hS best worst t := by
  apply Subtype.ext
  have h := polygonalCurve_formula hS
    (fun n : ℤ => ExtremeReferenceSequence best worst n.toNat) 0 (t := t.val)
    (by simpa only [Int.cast_zero, zero_add] using t.property)
  simpa only [SequenceCurve, ExtremeReferenceSequence, zero_add, Int.toNat_zero,
    Int.toNat_one, ite_true, one_ne_zero, ite_false, Int.cast_zero, sub_zero,
    ExtremeReferenceSegment, Mix] using h

/-- The two-point polygonal curve has precisely the image of the one line segment. -/
theorem extremeReferenceSequence_range (hS : Convex ℝ S) (best worst : S) :
    Set.range (SequenceCurve hS (ExtremeReferenceSequence best worst)) =
      Set.range (ExtremeReferenceSegment hS best worst) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    let a := Int.fract t
    have ha : a ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    by_cases hA : (⌊t⌋ + 1).toNat = 0
    · by_cases hB : (⌊t⌋).toNat = 0
      · refine ⟨⟨0, by norm_num⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, extremeReferenceSegment_zero]
        exact (mix_self hS best (Int.fract t) _).symm
      · refine ⟨⟨1 - a, sub_nonneg.mpr ha.2, by linarith [ha.1]⟩, ?_⟩
        change Mix hS worst best (1 - a) _ = _
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, ite_false]
        exact (mix_swap hS best worst a ha).symm
    · by_cases hB : (⌊t⌋).toNat = 0
      · refine ⟨⟨a, ha⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_true, ite_false, ExtremeReferenceSegment]
        rfl
      · refine ⟨⟨1, by norm_num⟩, ?_⟩
        simp only [SequenceCurve, PolygonalCurve, ExtremeReferenceSequence,
          hA, hB, ite_false, extremeReferenceSegment_one]
        exact (mix_self hS worst (Int.fract t) _).symm
  · rintro x ⟨t, rfl⟩
    exact ⟨t.val, extremeReferenceSequence_on_unit hS best worst t⟩

/-- With both extrema attained, the real-parameter curve brackets all points using one segment. -/
theorem extremeReferenceSequence_brackets (hS : Convex ℝ S) {r : S → S → Prop}
    (best worst : S) (hbest : ∀ x, r best x) (hworst : ∀ x, r x worst) :
    Continuous (SequenceCurve hS (ExtremeReferenceSequence best worst)) ∧
      ∀ x, ∃ a b : ℝ, r (SequenceCurve hS (ExtremeReferenceSequence best worst) a) x ∧
        r x (SequenceCurve hS (ExtremeReferenceSequence best worst) b) := by
  refine ⟨sequenceCurve_continuous hS _, fun x => ⟨0, 1, ?_, ?_⟩⟩
  · rw [extremeReferenceSequence_curve_zero]
    exact hbest x
  · rw [extremeReferenceSequence_curve_one]
    exact hworst x

/-- **Problem 2.14(a):** a continuous countable connect-the-dots curve brackets all preferences. -/
theorem problem_2_14a {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ q : ℕ → NonnegativeOrthant k,
      Continuous (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q) ∧
        ∀ x, ∃ a b : ℝ,
          r (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q a) x ∧
          r x (SequenceCurve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) q b) := by
  classical
  let : Nonempty (NonnegativeOrthant k) := ⟨⟨0, le_rfl⟩⟩
  by_cases he : (∃ best, ∀ x, r best x) ∧ ∃ worst, ∀ x, r x worst
  · obtain ⟨⟨best, hbest⟩, ⟨worst, hworst⟩⟩ := he
    exact ⟨ExtremeReferenceSequence best worst, extremeReferenceSequence_brackets
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) best worst hbest hworst⟩
  · obtain ⟨v, hv⟩ := proposition_1_15 k hr hc
    exact exists_bracketing_polygonal_curve (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) hv

/-- **Problem 2.14(b):** every bracketed class meets the connected curve. -/
theorem problem_2_14b {X : Type*} [TopologicalSpace X] {r : X → X → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) (f : ℝ → X) (hf : Continuous f)
    (hb : ∀ x, ∃ a b : ℝ, r (f a) x ∧ r x (f b)) :
    ∀ x, ∃ t, Indifferent r (f t) x := by
  intro x
  obtain ⟨a, b, ha, hb⟩ := hb x
  exact indifference_on_connected_image hr hc f hf x ha hb

/-- Parts (a)-(b) produce a connected curve image meeting every indifference class. -/
theorem problem_2_14ab {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ f : ℝ → NonnegativeOrthant k, Continuous f ∧
      IsPreconnected (Set.range f) ∧ ∀ x, ∃ t, Indifferent r (f t) x := by
  obtain ⟨q, hq, hb⟩ := problem_2_14a hr hc
  exact ⟨_, hq, isPreconnected_range hq, problem_2_14b hr hc _ hq hb⟩

/-- **Problem 2.14:** the complete curve, recursive-scale, and indifference-extension proof. -/
theorem problem_2_14 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u := by
  obtain ⟨f, hf, hZ, hcover⟩ := problem_2_14ab hr hc
  let Z := Set.range f
  let : Nonempty Z := ⟨⟨f 0, Set.mem_range_self 0⟩⟩
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp hZ
  let rz : Z → Z → Prop := fun x y => r x.val y.val
  have hrz : Rational rz := ⟨fun x y => hr.1 x.val y.val,
    fun x y z => hr.2 x.val y.val z.val⟩
  have hcz : ContinuousPreference rz :=
    hc.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  obtain ⟨q, hq, he⟩ := exists_dense_sample_with_extremes rz
  have hcomplete := problem_2_14_recursive_completion hrz hcz q hq he
  let v := SampledWeightedUtility rz q DyadicWeight
  have hu : Represents (RecursiveUtility v q) rz := hcomplete.2.1
  have huc : Continuous (RecursiveUtility v q) := hcomplete.2.2.1
  have hclasses : ∀ x, ∃ z : Z, Indifferent r z.val x := by
    intro x
    obtain ⟨t, ht⟩ := hcover x
    exact ⟨⟨f t, Set.mem_range_self t⟩, ht⟩
  obtain ⟨u, hrep, hcont, _⟩ := problem_2_14c hr hc Z hZ (RecursiveUtility v q) hu huc hclasses
  exact ⟨u, hrep, hcont⟩

end Kreps.PreferenceProperties
