/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.ThresholdChains

/-!
# A complete fixed-threshold representation criterion

Kreps I, Problem 1.17f, p. 29. The additional bounded-chain condition is necessary
and sufficient on every finite domain satisfying the four proposed conditions.
For sufficiency, greatest reachable integer scores give a potential with a gap
between strict and non-strict comparisons. A small injective code of the finitely
many positive-indifference classes separates unequal classes without closing that
gap. Rescaling then gives exactly the threshold one and exactly the prescribed
positive indifference. No utility representation is assumed in the chain condition.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*} {s i : X → X → Prop}

/-- Positive indifference gives an equivalence relation under the proposed conditions. -/
def positiveIndifferenceSetoid (ha : PartialPreferenceAxioms s i) : Setoid X where
  r := i
  iseqv := ⟨ha.indiff_refl, fun h => ha.indiff_symm _ _ h,
    fun hxy hyz => ha.indiff_trans _ _ _ hxy hyz⟩

/-- Finitely many positive-indifference classes admit distinct codes in the unit interval. -/
theorem exists_bounded_indifference_code [Finite X] (ha : PartialPreferenceAxioms s i) :
    ∃ ρ : X → ℝ, (∀ x, 0 ≤ ρ x ∧ ρ x < 1) ∧ (∀ x y, ρ x = ρ y ↔ i x y) := by
  classical
  let Q := Quotient (positiveIndifferenceSetoid ha)
  let : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let f : X → Fin (Fintype.card Q) := fun x => e (Quotient.mk _ x)
  let d : ℝ := (Fintype.card Q : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨fun x => (f x).val / d, ?_, ?_⟩
  · intro x
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hd.le
    · apply (div_lt_one hd).mpr
      have hn : ((f x).val : ℝ) < (Fintype.card Q : ℝ) := by exact_mod_cast (f x).isLt
      dsimp [d]
      linarith
  · intro x y
    constructor
    · intro h
      have hr : ((f x).val : ℝ) = ((f y).val : ℝ) := (div_left_inj' hd.ne').mp h
      have hn : (f x).val = (f y).val := by exact_mod_cast hr
      have he : f x = f y := Fin.ext hn
      exact Quotient.exact (e.injective he)
    · intro h
      have hq : Quotient.mk (positiveIndifferenceSetoid ha) x =
          Quotient.mk (positiveIndifferenceSetoid ha) y := Quotient.sound h
      have he : f x = f y := congrArg e hq
      change ((f x).val : ℝ) / d = ((f y).val : ℝ) / d
      rw [he]

/-- Integer potentials and bounded class codes give the exact threshold representation. -/
theorem threshold_representation_of_bounded [Finite X] (ha : PartialPreferenceAxioms s i)
    (hb : BoundedThresholdChains s i) :
    ∃ u : X → ℝ, (∀ x y, i x y ↔ EqualUtility u x y) ∧
      (∀ x y, s x y ↔ ThresholdPreference u x y) := by
  obtain ⟨m, _, B, hB⟩ := hb
  obtain ⟨ρ, hρ, hρeq⟩ := exists_bounded_indifference_code ha
  let P := ThresholdPotential s i m
  let v : X → ℝ := fun x => (P x : ℝ) + ρ x / 4
  let d : ℝ := (m : ℝ) + 1 / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let u : X → ℝ := fun x => v x / d
  refine ⟨u, ?_, ?_⟩
  · intro x y
    constructor
    · intro hxy
      have hP : P x = P y := thresholdPotential_indifferent ha hB hxy
      have hρxy := (hρeq x y).mpr hxy
      change v x / d = v y / d
      simp only [v, hP, hρxy]
    · intro hxy
      have hv : v x = v y := (div_left_inj' hd.ne').mp hxy
      have hP : P x = P y := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hgap : P x + 1 ≤ P y := by omega
          have hgap' : (P x : ℝ) + 1 ≤ (P y : ℝ) := by exact_mod_cast hgap
          dsimp [v] at hv
          linarith [(hρ x).1, (hρ x).2, (hρ y).1, (hρ y).2]
        · have hgap : P y + 1 ≤ P x := by omega
          have hgap' : (P y : ℝ) + 1 ≤ (P x : ℝ) := by exact_mod_cast hgap
          dsimp [v] at hv
          linarith [(hρ x).1, (hρ x).2, (hρ y).1, (hρ y).2]
      apply (hρeq x y).mp
      dsimp [v] at hv
      rw [hP] at hv
      linarith
  · intro x y
    constructor
    · intro hxy
      have hP : P y + (m : ℤ) + 1 ≤ P x := thresholdPotential_strict hB hxy
      have hP' : (P y : ℝ) + (m : ℝ) + 1 ≤ (P x : ℝ) := by exact_mod_cast hP
      have hv : v y + d < v x := by
        dsimp [v, d]
        linarith [(hρ y).2, (hρ x).1]
      have hdiv := div_lt_div_of_pos_right hv hd
      change v y / d + 1 < v x / d
      simpa only [add_div, div_self hd.ne'] using hdiv
    · intro hxy
      by_contra hnot
      have hP : P x - (m : ℤ) ≤ P y := thresholdPotential_not_strict hB hnot
      have hP' : (P x : ℝ) - (m : ℝ) ≤ (P y : ℝ) := by exact_mod_cast hP
      have hv : v x ≤ v y + d := by
        dsimp [v, d]
        linarith [(hρ x).2, (hρ y).1]
      have hdiv := div_le_div_of_nonneg_right hv hd.le
      have hu : u x ≤ u y + 1 := by
        simpa only [u, add_div, div_self hd.ne'] using hdiv
      exact (not_lt_of_ge hu) hxy

/-- **Problem 1.17f**: a precise additional comparison-chain criterion, in both directions. -/
theorem problem_1_17f [Finite X] (ha : PartialPreferenceAxioms s i) :
    BoundedThresholdChains s i ↔
      ∃ u : X → ℝ, (∀ x y, i x y ↔ EqualUtility u x y) ∧
        (∀ x y, s x y ↔ ThresholdPreference u x y) :=
  ⟨threshold_representation_of_bounded ha,
    fun ⟨_, hi, hs⟩ => boundedThresholdChains_of_representation hs hi⟩

end Kreps.ChoicePreferenceUtility
