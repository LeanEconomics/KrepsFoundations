/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Homotheticity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Preference along rays, without commodity monotonicity

Ingredients for the full Proposition 2.19 and Problem 2.12. Continuity and
homotheticity make a ray strictly increasing above the origin's rank and strictly
decreasing below it. Positive and negative reference rays bracket every relevant
indifference class. No commodity-monotonicity hypothesis is used.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A preferred scalar multiple can be iterated to give a chain above the original bundle. -/
theorem homothetic_iterate_above (hr : Rational r) (hh : HomotheticPreference r)
    {t : ℝ≥0} {x : NonnegativeOrthant k} (h : r (ScaleBundle t x) x) :
    ∀ m : ℕ, r (ScaleBundle (t ^ m) x) x := by
  intro m
  induction m with
  | zero => simpa only [pow_zero, scaleBundle_one] using complete_refl hr.1 x
  | succ m ih =>
    rw [pow_succ, scaleBundle_mul]
    exact hr.2 _ _ x (hh _ _ (t ^ m) h) ih

/-- A worse scalar multiple can be iterated to give a chain below the original bundle. -/
theorem homothetic_iterate_below (hr : Rational r) (hh : HomotheticPreference r)
    {t : ℝ≥0} {x : NonnegativeOrthant k} (h : r x (ScaleBundle t x)) :
    ∀ m : ℕ, r x (ScaleBundle (t ^ m) x) := by
  intro m
  induction m with
  | zero => simpa only [pow_zero, scaleBundle_one] using complete_refl hr.1 x
  | succ m ih =>
    rw [pow_succ, scaleBundle_mul]
    exact hr.2 x _ _ ih (hh _ _ (t ^ m) h)

/-- Contracting a bundle strictly above the origin strictly reduces its rank. -/
theorem homothetic_contract_positive (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {t : ℝ≥0} (ht : t < 1)
    {x : NonnegativeOrthant k} (hx : Strict r x (OrthantZero k)) :
    Strict r x (ScaleBundle t x) := by
  apply (proposition_1_9a hr.1 x _).mpr
  intro h
  have hseq := homothetic_iterate_above hr hh h
  have hclosed := ((proposition_1_14c hr).mp hc x).2
  exact hx.2 (hclosed.mem_of_tendsto (scaleBundle_pow_tendsto_zero ht x)
    (Filter.Eventually.of_forall hseq))

/-- Contracting a bundle strictly below the origin strictly raises its rank. -/
theorem homothetic_contract_negative (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {t : ℝ≥0} (ht : t < 1)
    {x : NonnegativeOrthant k} (hx : Strict r (OrthantZero k) x) :
    Strict r (ScaleBundle t x) x := by
  apply (proposition_1_9a hr.1 _ x).mpr
  intro h
  have hseq := homothetic_iterate_below hr hh h
  have hclosed := ((proposition_1_14c hr).mp hc x).1
  exact hx.2 (hclosed.mem_of_tendsto (scaleBundle_pow_tendsto_zero ht x)
    (Filter.Eventually.of_forall hseq))

/-- Scaling preserves the origin's indifference class, even at scalar zero. -/
theorem homothetic_origin_indifferent (hh : HomotheticPreference r)
    {x : NonnegativeOrthant k} (hx : Indifferent r x (OrthantZero k)) (t : ℝ≥0) :
    Indifferent r (ScaleBundle t x) (OrthantZero k) := by
  have h : Indifferent r (ScaleBundle t x) (ScaleBundle t (OrthantZero k)) :=
    ⟨hh _ _ t hx.1, hh _ _ t hx.2⟩
  simpa only [scaleBundle_origin] using h

/-- Larger multiples of a positive-rank bundle are strictly preferred. -/
theorem homothetic_positive_ray (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) {t s : ℝ≥0} (hts : t < s) :
    Strict r (ScaleBundle s p) (ScaleBundle t p) := by
  have hs : 0 < s := (show 0 ≤ t from zero_le).trans_lt hts
  have hts' : t / s < 1 := (div_lt_one hs).mpr hts
  have h := (homothetic_scale_strict_iff hh hs p (ScaleBundle (t / s) p)).mpr
    (homothetic_contract_positive hr hc hh hts' hp)
  have he : s * (t / s) = t := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  rwa [← scaleBundle_mul, he] at h

/-- Larger multiples of a negative-rank bundle are strictly worse. -/
theorem homothetic_negative_ray (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r (OrthantZero k) p) {t s : ℝ≥0} (hts : t < s) :
    Strict r (ScaleBundle t p) (ScaleBundle s p) := by
  have hs : 0 < s := (show 0 ≤ t from zero_le).trans_lt hts
  have hts' : t / s < 1 := (div_lt_one hs).mpr hts
  have h := (homothetic_scale_strict_iff hh hs (ScaleBundle (t / s) p) p).mpr
    (homothetic_contract_negative hr hc hh hts' hp)
  have he : s * (t / s) = t := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  rwa [← scaleBundle_mul, he] at h

/-- A numerical representation is strictly increasing along a positive reference ray. -/
theorem positive_ray_strictMono (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {u : NonnegativeOrthant k → ℝ} (hu : Represents u r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k)) :
    StrictMono (fun t : ℝ≥0 => u (ScaleBundle t p)) := by
  intro t s hts
  exact (strict_iff_utility_lt hu _ _).mp (homothetic_positive_ray hr hc hh hp hts)

/-- A numerical representation is strictly decreasing along a negative reference ray. -/
theorem negative_ray_strictAnti (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {u : NonnegativeOrthant k → ℝ} (hu : Represents u r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p) :
    StrictAnti (fun t : ℝ≥0 => u (ScaleBundle t p)) := by
  intro t s hts
  exact (strict_iff_utility_lt hu _ _).mp (homothetic_negative_ray hr hc hh hp hts)

/-- Every bundle is strictly dominated by some positive multiple of a positive reference. -/
theorem positive_ray_cofinal (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k)) (x : NonnegativeOrthant k) :
    ∃ t : ℝ≥0, 0 < t ∧ Strict r (ScaleBundle t p) x := by
  have hlim := scaleBundle_pow_tendsto_zero (show (1 / 2 : ℝ≥0) < 1 by norm_num) x
  have hevent := hlim.eventually ((continuousPreference_openStrictContours hc p).2.mem_nhds hp)
  obtain ⟨m, hm⟩ := hevent.exists
  have ha : (0 : ℝ≥0) < (1 / 2) ^ m := pow_pos (by norm_num) _
  have hinv : (0 : ℝ≥0) < ((1 / 2) ^ m)⁻¹ := inv_pos.mpr ha
  refine ⟨((1 / 2) ^ m)⁻¹, hinv, ?_⟩
  have h := (homothetic_scale_strict_iff hh hinv p
    (ScaleBundle ((1 / 2) ^ m) x)).mpr hm
  simpa only [scaleBundle_inv (ne_of_gt ha)] using h

/-- Every bundle strictly dominates some positive multiple of a negative reference. -/
theorem negative_ray_coinitial (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p : NonnegativeOrthant k} (hp : Strict r (OrthantZero k) p) (x : NonnegativeOrthant k) :
    ∃ t : ℝ≥0, 0 < t ∧ Strict r x (ScaleBundle t p) := by
  have hlim := scaleBundle_pow_tendsto_zero (show (1 / 2 : ℝ≥0) < 1 by norm_num) x
  have hevent := hlim.eventually ((continuousPreference_openStrictContours hc p).1.mem_nhds hp)
  obtain ⟨m, hm⟩ := hevent.exists
  have ha : (0 : ℝ≥0) < (1 / 2) ^ m := pow_pos (by norm_num) _
  have hinv : (0 : ℝ≥0) < ((1 / 2) ^ m)⁻¹ := inv_pos.mpr ha
  refine ⟨((1 / 2) ^ m)⁻¹, hinv, ?_⟩
  have h := (homothetic_scale_strict_iff hh hinv
    (ScaleBundle ((1 / 2) ^ m) x) p).mpr hm
  simpa only [scaleBundle_inv (ne_of_gt ha)] using h

/-- Every rank weakly above the origin occurs on any positive reference ray. -/
theorem positive_ray_indifference (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) {x : NonnegativeOrthant k}
    (hx : r x (OrthantZero k)) : ∃ t : ℝ≥0, Indifferent r (ScaleBundle t p) x := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  obtain ⟨T, _, hT⟩ := positive_ray_cofinal hc hh hp x
  have hf := huc.comp (scaleBundle_ray_continuous p)
  have h0 : u (ScaleBundle 0 p) ≤ u x := by
    simpa only [scaleBundle_zero] using (hu x (OrthantZero k)).mp hx
  have h1 : u x ≤ u (ScaleBundle T p) := (hu _ _).mp hT.1
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show 0 ≤ T from zero_le) hf.continuousOn ⟨h0, h1⟩
  exact ⟨t, (hu _ _).mpr ht.ge, (hu _ _).mpr ht.le⟩

/-- Every rank weakly below the origin occurs on any negative reference ray. -/
theorem negative_ray_indifference (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p : NonnegativeOrthant k}
    (hp : Strict r (OrthantZero k) p) {x : NonnegativeOrthant k}
    (hx : r (OrthantZero k) x) : ∃ t : ℝ≥0, Indifferent r (ScaleBundle t p) x := by
  obtain ⟨u, hu, huc⟩ := (proposition_2_9 k hr).mp hc
  obtain ⟨T, _, hT⟩ := negative_ray_coinitial hc hh hp x
  have hf := huc.comp (scaleBundle_ray_continuous p)
  have h0 : u x ≤ u (ScaleBundle 0 p) := by
    simpa only [scaleBundle_zero] using (hu (OrthantZero k) x).mp hx
  have h1 : u (ScaleBundle T p) ≤ u x := (hu _ _).mp hT.1
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (show 0 ≤ T from zero_le) hf.continuousOn ⟨h1, h0⟩
  exact ⟨t, (hu _ _).mpr ht.ge, (hu _ _).mpr ht.le⟩

end Kreps.PreferenceProperties
