/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.Independence

/-!
# Preferences on probability grids

Kreps I, proof of Lemma 5.7, pp. 91–92. Background substitution makes all
adjacent intervals of a grid comparable in the same direction. A chain of
those intervals transfers comparisons between endpoints to every rational grid
weight. Equal-step grids include the dyadic ones in the printed proof.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Probability at the specified grid point with a positive denominator. -/
noncomputable def GridWeight (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) : Weight :=
  ⟨(j : ℝ) / n, by positivity, (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hj)⟩

/-- At the last grid point the full first alternative is selected. -/
theorem gridWeight_last (n : ℕ) (hn : 0 < n) : GridWeight n n hn le_rfl = 1 := by
  apply Subtype.ext
  change (n : ℝ) / n = 1
  exact div_self (by positivity)

/-- At the first grid point the second alternative is selected. -/
theorem gridWeight_zero (n : ℕ) (hn : 0 < n) : GridWeight n 0 hn (Nat.zero_le _) = 0 := by
  apply Subtype.ext
  simp [GridWeight]

/-- Each step of the grid has probability increment one over the denominator. -/
theorem gridWeight_step {n i : ℕ} (hi : i < n) :
    (GridWeight n (i + 1) (by omega) hi).val =
      (GridWeight n i (by omega) hi.le).val + (GridWeight n 1 (by omega) (by omega)).val := by
  simp [GridWeight, add_div]

/-- Chaining a common comparison from the first grid interval to any positive grid point. -/
theorem grid_chain {P : Z → Z → Prop} (ht : TransitivePref P) (x y : Z) {n : ℕ} (hn : 0 < n)
    (h : ∀ i (hi : i < n), P (Mix (GridWeight n (i + 1) hn hi) x y)
      (Mix (GridWeight n i hn hi.le) x y)) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    P (Mix (GridWeight n m hn hmn) x y) y := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hi : m < n := by omega
    by_cases hz : m = 0
    · subst m
      simpa only [gridWeight_zero, mix_zero] using h 0 hi
    · exact ht _ _ _ (h m hi) (ih (by omega) hi.le)

/-- Weak upward grid comparisons all agree with the endpoint comparison. -/
theorem grid_weak (hr : Rational r) (hi : BackgroundIndependent r) {x y : Z} (hxy : r x y)
    {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) :
    r (Mix (GridWeight n m (by omega) hmn) x y) y := by
  have hd : (GridWeight n 1 (by omega) (by omega)).val < 1 := by
    simp only [GridWeight, Nat.cast_one]
    exact (div_lt_one (by positivity)).mpr (by exact_mod_cast hn)
  have hs (i : ℕ) (h : i < n) := segment_step_weak hr hi x y hd (gridWeight_step h)
  have hu : r (Mix (GridWeight n 1 (by omega) (by omega)) x y) y := by
    by_contra h
    have hrev := grid_chain (P := fun a b => Strict r b a)
      (fun a b c hab hbc => proposition_1_9h hr.2 c b a hbc hab) x y (by omega : 0 < n)
      (fun i hni => (proposition_1_9a hr.1 _ _).mpr (fun hc => h ((hs i hni).mp hc)))
      (m := n) (by omega) le_rfl
    rw [gridWeight_last, mix_one] at hrev
    exact hrev.2 hxy
  exact grid_chain hr.2 x y (by omega) (fun i h => (hs i h).mpr hu) hm hmn

/-- Strict upward grid comparisons all agree with the strict endpoint comparison. -/
theorem grid_strict (hr : Rational r) (hi : BackgroundIndependent r) {x y : Z}
    (hxy : Strict r x y) {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) :
    Strict r (Mix (GridWeight n m (by omega) hmn) x y) y := by
  have hd : (GridWeight n 1 (by omega) (by omega)).val < 1 := by
    simp only [GridWeight, Nat.cast_one]
    exact (div_lt_one (by positivity)).mpr (by exact_mod_cast hn)
  have hs (i : ℕ) (h : i < n) := segment_step_strict hi x y hd (gridWeight_step h)
  have hu : Strict r (Mix (GridWeight n 1 (by omega) (by omega)) x y) y := by
    by_contra h
    have hrev := grid_chain (P := fun a b => r b a)
      (fun a b c hab hbc => hr.2 c b a hbc hab) x y (by omega : 0 < n)
      (fun i hni => not_not.mp (fun hc => h ((hs i hni).mp
        ((proposition_1_9a hr.1 _ _).mpr hc)))) (m := n) (by omega) le_rfl
    rw [gridWeight_last, mix_one] at hrev
    exact hxy.2 hrev
  exact grid_chain (proposition_1_9h hr.2) x y (by omega) (fun i h => (hs i h).mpr hu) hm hmn

/-- Every nonempty open subinterval of probabilities contains a positive grid point. -/
theorem exists_gridWeight_between {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (n m : ℕ) (hn : 1 < n) (_hm : 0 < m) (hmn : m ≤ n),
      a < (GridWeight n m (by omega) hmn).val ∧ (GridWeight n m (by omega) hmn).val < b := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (b - a)⁻¹)
  have hn' : 1 < n := by exact_mod_cast (le_max_left _ _).trans_lt hn
  obtain ⟨z, hz, hz'⟩ := exists_div_btwn hab ((le_max_right _ _).trans_lt hn)
  have hnpos : (0 : ℝ) < n := by positivity
  have hzpos : (0 : ℝ) < z := (div_pos_iff_of_pos_right hnpos).mp (ha.trans_lt hz)
  have hzi : 0 ≤ z := by exact_mod_cast hzpos.le
  lift z to ℕ using hzi
  have hm : 0 < z := by exact_mod_cast hzpos
  have hmn : z ≤ n := by exact_mod_cast (div_le_one hnpos).mp (hz'.le.trans hb)
  exact ⟨n, z, hn', hm, hmn, by simpa [GridWeight] using hz, by simpa [GridWeight] using hz'⟩

end Kreps.ChoiceUnderUncertainty
