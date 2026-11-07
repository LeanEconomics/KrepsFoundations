/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.HomogeneousExtension

/-!
# A signed homogeneous representation

Kreps I, Proposition 2.19 and Problem 2.12. Join a positive reference ray to a
negative reference ray at the origin, parameterize their ranks by the real line,
and extend by indifference. Together with the one-sided and constant cases, this
proves the full theorem without imposing monotonicity in commodities.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A positive ray for positive parameters and a negative ray for negative parameters. -/
def SignedRay (p n : NonnegativeOrthant k) (a : ℝ) : NonnegativeOrthant k :=
  ⟨fun j => max a 0 * p.val j + max (-a) 0 * n.val j,
    fun j => add_nonneg (mul_nonneg (le_max_right _ _) (p.property j))
      (mul_nonneg (le_max_right _ _) (n.property j))⟩

/-- On the nonnegative half-line the signed curve is the positive reference ray. -/
theorem signedRay_nonneg (p n : NonnegativeOrthant k) {a : ℝ} (ha : 0 ≤ a) :
    SignedRay p n a = ScaleBundle (.mk a ha) p := by
  apply Subtype.ext
  funext j
  simp [SignedRay, ScaleBundle, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]

/-- On the nonpositive half-line the signed curve is the negative reference ray. -/
theorem signedRay_nonpos (p n : NonnegativeOrthant k) {a : ℝ} (ha : a ≤ 0) :
    SignedRay p n a = ScaleBundle (.mk (-a) (neg_nonneg.mpr ha)) n := by
  apply Subtype.ext
  funext j
  simp [SignedRay, ScaleBundle, max_eq_right ha, max_eq_left (neg_nonneg.mpr ha)]

/-- The two reference rays meet at the origin. -/
theorem signedRay_zero (p n : NonnegativeOrthant k) : SignedRay p n 0 = OrthantZero k := by
  rw [signedRay_nonneg p n le_rfl]
  exact scaleBundle_zero p

/-- Joining the two rays gives a continuous curve, including at their meeting point. -/
theorem signedRay_continuous (p n : NonnegativeOrthant k) : Continuous (SignedRay p n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_id.max continuous_const).mul continuous_const).add
    ((continuous_id.neg.max continuous_const).mul continuous_const)

/-- Scalar multiplication of bundles multiplies the signed parameter by the same scalar. -/
theorem signedRay_scale (p n : NonnegativeOrthant k) (t : ℝ≥0) (a : ℝ) :
    ScaleBundle t (SignedRay p n a) = SignedRay p n ((t : ℝ) * a) := by
  apply Subtype.ext
  funext j
  change (t : ℝ) * (max a 0 * p.val j + max (-a) 0 * n.val j) =
    max ((t : ℝ) * a) 0 * p.val j + max (-((t : ℝ) * a)) 0 * n.val j
  have hp : max ((t : ℝ) * a) 0 = (t : ℝ) * max a 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg (a := (t : ℝ)) a 0 t.property).symm
  have hn : max (-((t : ℝ) * a)) 0 = (t : ℝ) * max (-a) 0 := by
    simpa only [mul_zero, mul_neg] using
      (mul_max_of_nonneg (a := (t : ℝ)) (-a) 0 t.property).symm
  rw [hp, hn]
  ring

/-- Increasing the signed parameter strictly raises preference rank. -/
theorem homothetic_signedRay_strict (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n)
    {a b : ℝ} (hab : a < b) : Strict r (SignedRay p n b) (SignedRay p n a) := by
  by_cases hb : b ≤ 0
  · rw [signedRay_nonpos p n hb, signedRay_nonpos p n (hab.le.trans hb)]
    apply homothetic_negative_ray hr hc hh hn
    exact NNReal.coe_lt_coe.mp (neg_lt_neg hab)
  · have hb' : 0 < b := lt_of_not_ge hb
    by_cases ha : 0 ≤ a
    · rw [signedRay_nonneg p n hb'.le, signedRay_nonneg p n ha]
      apply homothetic_positive_ray hr hc hh hp
      exact NNReal.coe_lt_coe.mp hab
    · have ha' : a < 0 := lt_of_not_ge ha
      rw [signedRay_nonneg p n hb'.le, signedRay_nonpos p n ha'.le]
      have hpos : Strict r (ScaleBundle (.mk b hb'.le) p) (OrthantZero k) := by
        simpa only [scaleBundle_zero] using homothetic_positive_ray hr hc hh hp
          (show (0 : ℝ≥0) < .mk b hb'.le from NNReal.coe_lt_coe.mp hb')
      have hneg : Strict r (OrthantZero k)
          (ScaleBundle (.mk (-a) (neg_nonneg.mpr ha'.le)) n) := by
        simpa only [scaleBundle_zero] using homothetic_negative_ray hr hc hh hn
          (show (0 : ℝ≥0) < .mk (-a) (neg_nonneg.mpr ha'.le) from
            NNReal.coe_lt_coe.mp (neg_pos.mpr ha'))
      exact strict_weak_trans hr.2 hpos hneg.1

/-- The real parameter represents preference on the joined reference rays. -/
theorem homothetic_signedRay_represents (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n) :
    Represents (fun a : ℝ => a) (fun a b => r (SignedRay p n a) (SignedRay p n b)) := by
  obtain ⟨u, hu⟩ := proposition_1_15 k hr hc
  have hs : StrictMono (fun a : ℝ => u (SignedRay p n a)) := by
    intro a b hab
    exact (strict_iff_utility_lt hu _ _).mp (homothetic_signedRay_strict hr hc hh hp hn hab)
  exact fun a b => (hu _ _).trans hs.le_iff_le

/-- The joined rays meet every indifference class. -/
theorem homothetic_signedRay_covers (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) {p n : NonnegativeOrthant k}
    (hp : Strict r p (OrthantZero k)) (hn : Strict r (OrthantZero k) n)
    (x : NonnegativeOrthant k) : ∃ a : ℝ, Indifferent r (SignedRay p n a) x := by
  rcases hr.1 x (OrthantZero k) with hx | hx
  · obtain ⟨t, ht⟩ := positive_ray_indifference hr hc hh hp hx
    refine ⟨(t : ℝ), ?_⟩
    rw [signedRay_nonneg p n (a := (t : ℝ)) t.property]
    exact ht
  · obtain ⟨t, ht⟩ := negative_ray_indifference hr hc hh hn hx
    refine ⟨-(t : ℝ), ?_⟩
    rw [signedRay_nonpos p n (a := -(t : ℝ)) (neg_nonpos.mpr t.property)]
    have he : NNReal.mk (- -(t : ℝ)) (neg_nonneg.mpr (neg_nonpos.mpr t.property)) = t := by
      apply NNReal.coe_injective
      exact neg_neg (t : ℝ)
    rw [he]
    exact ht

/-- Positive and negative references give a continuous homogeneous representation of all ranks. -/
theorem homogeneous_representation_both_sides (hr : Rational r)
    (hc : ContinuousPreference r) (hh : HomotheticPreference r)
    {p n : NonnegativeOrthant k} (hp : Strict r p (OrthantZero k))
    (hn : Strict r (OrthantZero k) n) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  have hcover := homothetic_signedRay_covers hr hc hh hp hn
  have hv := homothetic_signedRay_represents hr hc hh hp hn
  refine ⟨LiftedUtility (SignedRay p n) id hcover,
    liftedUtility_represents hr (SignedRay p n) id hcover hv,
    liftedUtility_continuous hr hc (SignedRay p n) id hcover hv continuous_id, ?_⟩
  exact liftedUtility_homogeneous hr hh (SignedRay p n) id hcover hv
    (fun t a => (t : ℝ) * a) (signedRay_scale p n) (fun _ _ => rfl)

/-- **Proposition 2.19:** continuity and homotheticity are equivalent to a continuous
degree-one homogeneous representation, with no commodity-monotonicity assumption. -/
theorem proposition_2_19 (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ∧ HomotheticPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u := by
  constructor
  · rintro ⟨hc, hh⟩
    by_cases hpos : ∃ p, Strict r p (OrthantZero k)
    · obtain ⟨p, hp⟩ := hpos
      by_cases hneg : ∃ n, Strict r (OrthantZero k) n
      · obtain ⟨n, hn⟩ := hneg
        exact homogeneous_representation_both_sides hr hc hh hp hn
      · apply homogeneous_representation_above_origin hr hc hh hp
        intro x
        by_contra hx
        exact hneg ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
    · by_cases hneg : ∃ n, Strict r (OrthantZero k) n
      · obtain ⟨n, hn⟩ := hneg
        apply homogeneous_representation_below_origin hr hc hh hn
        intro x
        by_contra hx
        exact hpos ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
      · apply homogeneous_representation_indifferent hr
        intro x
        constructor
        · by_contra hx
          exact hneg ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
        · by_contra hx
          exact hpos ⟨x, (proposition_1_9a hr.1 _ _).mpr hx⟩
  · rintro ⟨u, hu, huc, huh⟩
    exact proposition_2_19_forward hu huc huh

/-- **Problem 2.12:** the full homogeneous representation, without the optional extra assumption. -/
theorem problem_2_12 (hr : Rational r) (hc : ContinuousPreference r)
    (hh : HomotheticPreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u ∧ HomogeneousUtility u :=
  (proposition_2_19 k hr).mp ⟨hc, hh⟩

end Kreps.PreferenceProperties
