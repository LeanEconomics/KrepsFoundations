/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.Lexicographic
import ChoicePreferenceUtility.ContinuousPreference
import ChoicePreferenceUtility.Rationalization

/-!
# The discontinuous utility produced by rational weights

Kreps I, Problem 1.12, p. 26. Rational points separate the usual order on [0,1].
The resulting utility is the sum of the positive weights at rational points at or
below its argument. At every positive rational point, the utility has a jump of at
least that point's weight and is discontinuous. These conclusions hold for every
positive summable weight assignment, including geometric weights from any injective
enumeration of the rationals, hence also the enumeration displayed in the problem.
Identity is an explicit continuous representation of the same preference.
-/

namespace Kreps.ChoicePreferenceUtility

/-- The rational points of the closed unit interval. -/
def RationalUnitPoints : Set UnitSegment := {x | ∃ q : ℚ, (q : ℝ) = x.val}

/-- The separating subset is countable. -/
theorem rationalUnitPoints_countable : RationalUnitPoints.Countable :=
  (Set.countable_range (fun q : ℚ => (q : ℝ))).preimage Subtype.val_injective

/-- The separating condition requested in **Problem 1.12**. -/
theorem problem_1_12_separating :
    OrderSeparating (UtilityPref (fun x : UnitSegment => x.val)) RationalUnitPoints := by
  intro x y hxy
  have hyx : y.val < x.val := lt_of_le_not_ge hxy.1 hxy.2
  obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
  let z : UnitSegment := ⟨q, y.property.1.trans hyq.le, hqx.le.trans x.property.2⟩
  exact ⟨z, ⟨q, rfl⟩, hqx.le, hyq.le, not_le_of_gt hyq⟩

/-- The weights for a chosen injective indexing; the first weight is one half. -/
noncomputable def GeometricRationalWeights
    (e : RationalUnitPoints ↪ ℕ) (q : RationalUnitPoints) : ℝ :=
  (1 / 2 : ℝ) ^ (e q + 1)

/-- Geometric indexing satisfies exactly the positivity and summability hypotheses used below. -/
theorem geometricRationalWeights_valid (e : RationalUnitPoints ↪ ℕ) :
    (∀ q, 0 < GeometricRationalWeights e q) ∧ Summable (GeometricRationalWeights e) := by
  refine ⟨fun q => pow_pos (by norm_num) _, ?_⟩
  change Summable (fun q => (1 / 2 : ℝ) ^ (e q + 1))
  exact summable_geometric_two.comp_injective (Nat.succ_injective.comp e.injective)

/-- The utility constructed by summing the weights of the rational lower contour. -/
noncomputable def RationalUtility (w : RationalUnitPoints → ℝ) (x : UnitSegment) : ℝ :=
  WeightedUtility (UtilityPref (fun x : UnitSegment => x.val)) RationalUnitPoints w x

/-- An explicit formula describing the graph requested in **Problem 1.12**. -/
theorem rationalUtility_formula (w : RationalUnitPoints → ℝ) (x : UnitSegment) :
    RationalUtility w x = ∑' q : RationalUnitPoints, if q.val.val ≤ x.val then w q else 0 := by
  classical
  rfl

/-- The constructed function represents the usual weak order. -/
theorem problem_1_12_represents {w : RationalUnitPoints → ℝ}
    (hw : ∀ q, 0 < w q) (hs : Summable w) :
    Represents (RationalUtility w) (UtilityPref (fun x : UnitSegment => x.val)) :=
  weightedUtility_represents hw hs (proposition_1_3a _) problem_1_12_separating

/-- Approaching a rational point from below misses at least that point's entire weight. -/
theorem rationalUtility_jump {w : RationalUnitPoints → ℝ} (hw : ∀ q, 0 < w q)
    (hs : Summable w) (q : RationalUnitPoints) {x : UnitSegment} (hx : x.val < q.val.val) :
    RationalUtility w x + w q ≤ RationalUtility w q.val := by
  classical
  let f : RationalUnitPoints → ℝ := fun z => if z.val.val ≤ x.val then w z else 0
  let g : RationalUnitPoints → ℝ := fun z => if z.val.val ≤ q.val.val then w z else 0
  let a : RationalUnitPoints → ℝ := fun z => if z = q then w q else 0
  have hf : Summable f := hs.indicator {z | z.val.val ≤ x.val}
  have hg : Summable g := hs.indicator {z | z.val.val ≤ q.val.val}
  have ha : HasSum a (w q) := hasSum_ite_eq q (w q)
  have hterm (z : RationalUnitPoints) : f z + a z ≤ g z := by
    by_cases hz : z = q
    · subst z
      simp only [f, g, a, ite_eq_right (not_le.mpr hx), ite_eq_left rfl,
        ite_eq_left le_rfl, zero_add, le_refl]
    · dsimp [a]
      simp only [hz, ite_false, add_zero]
      by_cases hzx : z.val.val ≤ x.val
      · have hzq := hzx.trans hx.le
        simp only [f, g, ite_eq_left hzx, ite_eq_left hzq, le_refl]
      · dsimp [f, g]
        simp only [hzx, ite_false]
        split_ifs
        · exact (hw z).le
        · exact le_rfl
  have hsum := Summable.tsum_le_tsum hterm (hf.add ha.summable) hg
  rw [hf.tsum_add ha.summable, ha.tsum_eq] at hsum
  exact hsum

/-- Every positive rational point is a discontinuity, including the endpoint one. -/
theorem problem_1_12_discontinuous {w : RationalUnitPoints → ℝ} (hw : ∀ q, 0 < w q)
    (hs : Summable w) (q : RationalUnitPoints) (hq : 0 < q.val.val) :
    ¬ContinuousAt (RationalUtility w) q.val := by
  intro hc
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (w q / 2) (half_pos (hw q))
  let ε : ℝ := min (δ / 2) (q.val.val / 2)
  have hepos : 0 < ε := lt_min (half_pos hδ) (half_pos hq)
  have heδ : ε ≤ δ / 2 := min_le_left _ _
  have heq : ε ≤ q.val.val / 2 := min_le_right _ _
  let x : UnitSegment := ⟨q.val.val - ε, by constructor <;>
    have hq1 := q.val.property.2 <;> linarith⟩
  have hxq : x.val < q.val.val := by dsimp [x]; linarith
  have hdist : dist x q.val < δ := by
    change dist x.val q.val.val < δ
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hxq)]
    dsimp [x]
    linarith
  have hgap := rationalUtility_jump hw hs q hxq
  have hsmall := hclose hdist
  rw [Real.dist_eq] at hsmall
  have habs := neg_le_abs (RationalUtility w x - RationalUtility w q.val)
  linarith [hw q]

/-- The usual preference has a continuous utility despite the discontinuous construction. -/
theorem problem_1_12_continuous_representation :
    Continuous (fun x : UnitSegment => x.val) ∧
      Represents (fun x : UnitSegment => x.val) (UtilityPref (fun x : UnitSegment => x.val)) :=
  ⟨continuous_subtype_val, fun _ _ => Iff.rfl⟩

/-- The preference in the example is itself continuous. -/
theorem problem_1_12_continuous_preference :
    ContinuousPreference (UtilityPref (fun x : UnitSegment => x.val)) :=
  continuousPreference_of_continuous_utility continuous_subtype_val

end Kreps.ChoicePreferenceUtility
