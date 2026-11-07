/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.AfriatRankInduction
import RevealedPreference.FiniteAffineEnvelope
import RevealedPreference.GarpNecessity

/-!
# Afriat's theorem on the full consumption domain

Kreps I, Proposition 4.3, pp. 70-73. Primitive feasible market data satisfy GARP
exactly when rational, locally insatiable preferences rationalize them. The
sufficiency construction supplies a continuous, strictly increasing, concave
utility on all real commodity vectors, then restricts it to the entire nonnegative
orthant. Empty observation families are included. The preference equivalence
requires a positive number of commodities, as local insatiability is impossible
on the singleton zero-dimensional orthant.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- Positive multipliers in the Afriat inequalities rule out every revealed strict cycle. -/
theorem matrixGARP_of_afriat {C : I → I → ℝ} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hineq : ∀ i j, v i ≤ v j + lam j * C j i) :
    MatrixGARP C := by
  apply matrixGARP_of_scores v
  · intro i j hij
    exact (hineq j i).trans (add_le_of_nonpos_right
      (mul_nonpos_of_nonneg_of_nonpos (hlam i).le hij))
  · intro i j hij
    exact (hineq j i).trans_lt (add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (hlam i) hij))

/-- GARP is equivalent to solvability of the finite Afriat inequalities. -/
theorem matrixGARP_iff_afriat [Finite I] (C : I → I → ℝ) :
    MatrixGARP C ↔ ∃ v lam : I → ℝ, (∀ i, 0 < lam i) ∧
      ∀ i j, v i ≤ v j + lam j * C j i :=
  ⟨lemma_4_5, fun ⟨_, _, hl, hv⟩ => matrixGARP_of_afriat hl hv⟩

/-- Concavity of a full-domain utility gives convex preference on the nonnegative orthant. -/
theorem convexPreference_of_concaveOn {u : (Fin k → ℝ) → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) :
    ConvexPreference (convex_Ici (0 : Fin k → ℝ))
      (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) := by
  intro x y hxy a ha
  have h := hu.2 (Set.mem_univ x.val) (Set.mem_univ y.val)
    ha.1 (sub_nonneg.mpr ha.2) (by ring : a + (1 - a) = 1)
  change u y.val ≤ u x.val at hxy
  change u y.val ≤ u (a • x.val + (1 - a) • y.val)
  simp only [smul_eq_mul] at h
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hxy)]

/-- The constructive direction supplies a regular utility over the entire commodity space. -/
theorem garp_exists_concave_utility [Finite I] {D : MarketData I k} (hG : GARP D) :
    ∃ u : (Fin k → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧
      ConcaveOn ℝ Set.univ u ∧
      Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) := by
  classical
  let := Fintype.ofFinite I
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let u := FiniteAffineTerm (fun _ : Unit => fun _ : Fin k => (1 : ℝ))
      (fun _ : Unit => (0 : Fin k → ℝ)) (fun _ => 0) (fun _ => 1) ()
    refine ⟨u, finiteAffineTerm_continuous _ _ _ _ _,
      finiteAffineTerm_strictMono _ zero_lt_one (fun _ => zero_lt_one),
      finiteAffineTerm_concaveOn _ _ _ _ _, ?_⟩
    exact fun i => isEmptyElim i
  | inr hI =>
    obtain ⟨v, lam, hlam, hineq⟩ := lemma_4_5 hG
    have hv : ∀ i j, v i ≤ v j + lam j *
        (AffineExpenditure (D.price j) (D.bundle i).val -
          AffineExpenditure (D.price j) (D.bundle j).val) := by
      intro i j
      simpa only [garp_cost_eq_difference hG, Expenditure, AffineExpenditure] using hineq i j
    let u := FiniteAffineEnvelope D.price (fun i => (D.bundle i).val) v lam
    refine ⟨u, finiteAffineEnvelope_continuous _ _ _ _,
      finiteAffineEnvelope_strictMono hlam D.price_pos,
      finiteAffineEnvelope_concaveOn _ _ _ _, ?_⟩
    intro i
    refine ⟨D.feasible i, fun x hx => ?_⟩
    apply finiteAffineEnvelope_maximizes hv i (hlam i).le
    change Expenditure (D.price i) x.val ≤ Expenditure (D.price i) (D.bundle i).val
    rw [garp_budget_exhaustion hG]
    exact hx

/-- **Proposition 4.3:** GARP is equivalent to primitive rational, insatiable rationalization. -/
theorem proposition_4_3 [Finite I] (hk : 0 < k) (D : MarketData I k) :
    GARP D ↔ ∃ r, Rational r ∧ LocallyInsatiable r ∧ Rationalizes D r := by
  constructor
  · intro hG
    obtain ⟨u, _, hm, _, hR⟩ := garp_exists_concave_utility hG
    refine ⟨UtilityPref (fun x : NonnegativeOrthant k => u x.val),
      utilityPref_rational _, ?_, hR⟩
    exact strictlyMonotone_locallyInsatiable hk
      (strictlyMonotonePreference_of_strictMono (fun _ _ h => hm h))
  · rintro ⟨r, hr, hl, hR⟩
    exact rationalizes_garp hr hl hR

/-- Afriat's stronger regularity conclusion imposes no further restriction on finite data. -/
theorem garp_iff_regular_rationalizable [Finite I] (hk : 0 < k) (D : MarketData I k) :
    GARP D ↔ ∃ r, Rational r ∧ ContinuousPreference r ∧
      StrictlyMonotonePreference r ∧
      ConvexPreference (convex_Ici (0 : Fin k → ℝ)) r ∧ Rationalizes D r := by
  constructor
  · intro hG
    obtain ⟨u, hc, hm, hconc, hR⟩ := garp_exists_concave_utility hG
    exact ⟨UtilityPref (fun x : NonnegativeOrthant k => u x.val),
      utilityPref_rational _,
      continuousPreference_of_continuous_utility (hc.comp continuous_subtype_val),
      strictlyMonotonePreference_of_strictMono (fun _ _ h => hm h),
      convexPreference_of_concaveOn hconc, hR⟩
  · rintro ⟨r, hr, _, hm, _, hR⟩
    exact rationalizes_garp hr (strictlyMonotone_locallyInsatiable hk hm) hR

end Kreps.RevealedPreference
