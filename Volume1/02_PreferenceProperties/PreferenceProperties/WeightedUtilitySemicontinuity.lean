/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.UpperSemicontinuousSeries
import PreferenceProperties.OrthantRepresentation

/-!
# Upper semicontinuity of weighted lower-contour utility

Kreps I, Problem 2.10, p. 47. Nonnegative summable weights give an upper
semicontinuous utility sum for any sequence of reference points. Strictly
positive weights represent preference when the references separate strict ranks.
The dyadic weights are exactly `1 / 2^(n+1)`, with zero-based enumeration of the
book's points `q¹,q²,...`. Density of their range suffices for representation.
-/

namespace Kreps.PreferenceProperties

variable {X I : Type*} {r : X → X → Prop}

/-- Sum the weights of enumerated reference points no better than the given alternative. -/
noncomputable def SampledWeightedUtility (r : X → X → Prop) (q : I → X)
    (w : I → ℝ) (x : X) : ℝ := ∑' i, {j | r x (q j)}.indicator w i

/-- Closed weak upper contours make each nonnegative weighted indicator upper semicontinuous. -/
theorem sampledWeightedTerm_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) (q : I → X) {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i : I) :
    UpperSemicontinuous (fun x => {j | r x (q j)}.indicator w i) := by
  change UpperSemicontinuous ((NoWorseThan r (q i)).indicator (fun _ => w i))
  exact (((proposition_1_14c hr).mp hc) (q i)).2.upperSemicontinuous_indicator (hw i)

/-- Summability supplies a uniform tail bound, preserving upper semicontinuity of the series. -/
theorem sampledWeightedUtility_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) (q : I → X) {w : I → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) :
    UpperSemicontinuous (SampledWeightedUtility r q w) := by
  apply upperSemicontinuous_tsum_of_norm_le hs (sampledWeightedTerm_upperSemicontinuous hr hc q hw)
  intro i x
  classical
  change ‖if r x (q i) then w i else 0‖ ≤ w i
  split_ifs
  · simp only [Real.norm_eq_abs, abs_of_nonneg (hw i), le_refl]
  · simpa only [norm_zero] using hw i

/-- The set-indexed weighted utility from Chapter 1 satisfies the same conclusion. -/
theorem weightedUtility_upperSemicontinuous [TopologicalSpace X]
    (hr : Rational r) (hc : ContinuousPreference r) {D : Set X} {w : D → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hs : Summable w) : UpperSemicontinuous (WeightedUtility r D w) :=
  sampledWeightedUtility_upperSemicontinuous hr hc Subtype.val hw hs

/-- Weak preference increases every sampled weighted term. -/
theorem sampledWeightedTerm_mono (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (ht : TransitivePref r) {x y : X} (hxy : r x y) (i : I) :
    {j | r y (q j)}.indicator w i ≤ {j | r x (q j)}.indicator w i := by
  classical
  change (if r y (q i) then w i else 0) ≤ if r x (q i) then w i else 0
  by_cases hy : r y (q i)
  · simp [hy, ht x y (q i) hxy hy]
  · simp only [hy, ite_false]
    split_ifs
    · exact hw i
    · exact le_rfl

/-- Weak preference increases the sampled weighted sum. -/
theorem sampledWeightedUtility_mono (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : TransitivePref r) {x y : X} (hxy : r x y) :
    SampledWeightedUtility r q w y ≤ SampledWeightedUtility r q w x :=
  Summable.tsum_le_tsum (sampledWeightedTerm_mono q hw ht hxy)
    (hs.indicator _) (hs.indicator _)

/-- A sampled separating point contributes a strictly positive increase. -/
theorem sampledWeightedUtility_strict (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (hs : Summable w) (ht : TransitivePref r) (hq : OrderSeparating r (Set.range q))
    {x y : X} (hxy : Strict r x y) :
    SampledWeightedUtility r q w y < SampledWeightedUtility r q w x := by
  classical
  obtain ⟨z, ⟨i, rfl⟩, hxz, hzy⟩ := hq x y hxy
  have hi : {j | r y (q j)}.indicator w i < {j | r x (q j)}.indicator w i := by
    change (if r y (q i) then w i else 0) < if r x (q i) then w i else 0
    simpa only [hzy.2, hxz, ite_false, ite_true] using hw i
  exact Summable.tsum_lt_tsum (sampledWeightedTerm_mono q (fun j => (hw j).le) ht hxy.1)
    hi (hs.indicator _) (hs.indicator _)

/-- Positive summable weights on any separating enumeration represent preference. -/
theorem sampledWeightedUtility_represents (q : I → X) {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (hs : Summable w) (hr : Rational r) (hq : OrderSeparating r (Set.range q)) :
    Represents (SampledWeightedUtility r q w) r := by
  intro x y
  constructor
  · exact sampledWeightedUtility_mono q (fun i => (hw i).le) hs hr.2
  · intro h
    by_contra hxy
    have hyx : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact not_lt_of_ge h (sampledWeightedUtility_strict q hw hs hr.2 hq hyx)

/-- The book's geometric weights, with the first enumerated point indexed by zero. -/
noncomputable def DyadicWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- These are exactly the displayed reciprocal powers of two. -/
theorem dyadicWeight_formula (n : ℕ) : DyadicWeight n = 1 / (2 : ℝ) ^ (n + 1) := by
  simp [DyadicWeight]

/-- Every enumerated point has strictly positive weight. -/
theorem dyadicWeight_pos (n : ℕ) : 0 < DyadicWeight n := pow_pos (by norm_num) _

/-- The geometric sequence is summable. -/
theorem dyadicWeight_summable : Summable DyadicWeight := by
  have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  simp only [pow_succ]
  exact hs.mul_right (1 / 2)

/-- The sampled dyadic sum is the formula displayed in Problem 2.10. -/
theorem sampledDyadicUtility_formula [DecidableRel r] (q : ℕ → X) (x : X) :
    SampledWeightedUtility r q DyadicWeight x =
      ∑' n, if r x (q n) then 1 / (2 : ℝ) ^ (n + 1) else 0 := by
  apply tsum_congr
  intro n
  classical
  by_cases h : r x (q n)
  · simp [h, dyadicWeight_formula]
  · simp [h]

/-- **Problem 2.10:** the displayed utility is upper semicontinuous for any enumeration. -/
theorem problem_2_10 {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (q : ℕ → NonnegativeOrthant k) :
    UpperSemicontinuous (SampledWeightedUtility r q DyadicWeight) :=
  sampledWeightedUtility_upperSemicontinuous hr hc q (fun n => (dyadicWeight_pos n).le)
    dyadicWeight_summable

/-- For an enumeration with dense range, the same formula also represents preference. -/
theorem problem_2_10_representation {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (q : ℕ → NonnegativeOrthant k) (hq : Dense (Set.range q)) :
    Represents (SampledWeightedUtility r q DyadicWeight) r := by
  let : PreconnectedSpace (NonnegativeOrthant k) :=
    isPreconnected_iff_preconnectedSpace.mp
      (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
  exact sampledWeightedUtility_represents q dyadicWeight_pos dyadicWeight_summable hr
    (dense_orderSeparating hr hc hq)

end Kreps.PreferenceProperties
