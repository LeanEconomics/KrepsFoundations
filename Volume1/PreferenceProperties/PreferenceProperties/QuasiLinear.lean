/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.StrictPreference
import Mathlib.Basic.NNReal.Basic

/-!
# Quasi-linear utility and compensating money

Kreps I, Definition 2.15 and Proposition 2.16, pp. 43-44, and Problem 2.11,
p. 48. The non-money bundle has any nonempty type X; taking X to be the
nonnegative orthant gives the book's domain. Money is nonnegative throughout.
The construction follows the hint: calibrate each bundle against a fixed x₀,
then assign the difference between the two compensating money amounts.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*}

/-- **Definition 2.15:** subutility plus the amount of money left over. -/
def QuasiLinearUtility (u : X → ℝ) (p : X × ℝ≥0) : ℝ := u p.1 + p.2

/-- A preference admits a utility representation with money coefficient one. -/
def QuasiLinear (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∃ u : X → ℝ, Represents (QuasiLinearUtility u) r

/-- **Proposition 2.16a:** for fixed non-money goods, money orders the bundles. -/
def OwnMoneyOrder (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x m n, r (x, m) (x, n) ↔ n ≤ m

/-- **Proposition 2.16b:** each common nonnegative money addition preserves comparisons. -/
def MoneyTranslation (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x y m n t, r (x, m) (y, n) ↔ r (x, m + t) (y, n + t)

/-- **Proposition 2.16c:** money can make any two non-money bundles indifferent. -/
def MoneyCompensable (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) : Prop :=
  ∀ x y, ∃ m n, Indifferent r (x, m) (y, n)

/-- Indifferent substitutions leave every weak comparison unchanged. -/
theorem indifferent_compare_iff {Y : Type*} {r : Y → Y → Prop}
    (ht : TransitivePref r) {x x' y y' : Y}
    (hx : Indifferent r x x') (hy : Indifferent r y y') : r x y ↔ r x' y' := by
  constructor
  · intro h
    exact ht x' y y' (ht x' x y hx.2 h) hy.1
  · intro h
    exact ht x y' y (ht x x' y' hx.1 h) hy.2

/-- Translation invariance also preserves indifference in both directions. -/
theorem moneyTranslation_indifferent {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (ht : MoneyTranslation r) (x y : X) (m n t : ℝ≥0) :
    Indifferent r (x, m) (y, n) ↔ Indifferent r (x, m + t) (y, n + t) := by
  exact and_congr (ht x y m n t) (ht y x n m t)

/-- A quasi-linear representation has the fixed-goods money order. -/
theorem quasiLinear_ownMoneyOrder {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : OwnMoneyOrder r := by
  intro x m n
  rw [hu]
  change (u x + (n : ℝ) ≤ u x + (m : ℝ)) ↔ n ≤ m
  rw [add_le_add_iff_left, NNReal.coe_le_coe]

/-- Common additions cancel from comparisons of quasi-linear utilities. -/
theorem quasiLinear_moneyTranslation {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : MoneyTranslation r := by
  intro x y m n t
  rw [hu, hu]
  simp only [QuasiLinearUtility, NNReal.coe_add]
  constructor <;> intro h <;> linarith

/-- Positive and negative parts of the utility difference give feasible compensations. -/
theorem quasiLinear_moneyCompensable {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) : MoneyCompensable r := by
  intro x y
  let m : ℝ≥0 := .mk (max 0 (u y - u x)) (le_max_left _ _)
  let n : ℝ≥0 := .mk (max 0 (u x - u y)) (le_max_left _ _)
  have he : QuasiLinearUtility u (x, m) = QuasiLinearUtility u (y, n) := by
    change u x + max 0 (u y - u x) = u y + max 0 (u x - u y)
    rcases le_total (u x) (u y) with h | h
    · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
      ring
  exact ⟨m, n, (hu _ _).mpr he.ge, (hu _ _).mpr he.le⟩

/-- The compensating-money construction in the hint to **Problem 2.11**. -/
theorem quasiLinear_of_money_properties {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) (hm : OwnMoneyOrder r) (ht : MoneyTranslation r)
    (hc : MoneyCompensable r) (x₀ : X) : QuasiLinear r := by
  classical
  choose m n h using fun x => hc x x₀
  let u : X → ℝ := fun x => (n x : ℝ) - (m x : ℝ)
  refine ⟨u, ?_⟩
  rintro ⟨x, a⟩ ⟨y, b⟩
  change r (x, a) (y, b) ↔ u y + (b : ℝ) ≤ u x + (a : ℝ)
  let T := m x + m y
  have hx : Indifferent r (x, a + T) (x₀, n x + a + m y) := by
    simpa [T, add_assoc, add_left_comm, add_comm] using
      (moneyTranslation_indifferent ht x x₀ (m x) (n x) (a + m y)).mp (h x)
  have hy : Indifferent r (y, b + T) (x₀, n y + b + m x) := by
    simpa [T, add_assoc, add_left_comm, add_comm] using
      (moneyTranslation_indifferent ht y x₀ (m y) (n y) (b + m x)).mp (h y)
  calc
    r (x, a) (y, b) ↔ r (x, a + T) (y, b + T) := ht x y a b T
    _ ↔ r (x₀, n x + a + m y) (x₀, n y + b + m x) :=
      indifferent_compare_iff hr.2 hx hy
    _ ↔ n y + b + m x ≤ n x + a + m y := hm x₀ _ _
    _ ↔ u y + (b : ℝ) ≤ u x + (a : ℝ) := by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      dsimp [u]
      constructor <;> intro hle <;> linarith

/-- **Proposition 2.16:** all three money properties characterize quasi-linearity. -/
theorem proposition_2_16 [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    QuasiLinear r ↔ OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨quasiLinear_ownMoneyOrder hu, quasiLinear_moneyTranslation hu,
      quasiLinear_moneyCompensable hu⟩
  · rintro ⟨hm, ht, hc⟩
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact quasiLinear_of_money_properties hr hm ht hc x₀

/-- **Problem 2.11:** the characterization, with a nonnegative money domain. -/
theorem problem_2_11 [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    QuasiLinear r ↔ OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r :=
  proposition_2_16 hr

/-- The money-unit utility difference in the compensation discussion on p. 44. -/
def QuasiLinearDifference (u : X → ℝ) (p q : X × ℝ≥0) : ℝ :=
  QuasiLinearUtility u p - QuasiLinearUtility u q

/-- The corrected bundle keeps q's goods and adds the utility difference to q's money. -/
theorem quasiLinear_compensation {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) (p q : X × ℝ≥0)
    (hf : 0 ≤ (q.2 : ℝ) + QuasiLinearDifference u p q) :
    Indifferent r p (q.1, .mk ((q.2 : ℝ) + QuasiLinearDifference u p q) hf) := by
  have he : QuasiLinearUtility u
      (q.1, .mk ((q.2 : ℝ) + QuasiLinearDifference u p q) hf) =
      QuasiLinearUtility u p := by
    change u q.1 + ((q.2 : ℝ) + (u p.1 + p.2 - (u q.1 + q.2))) = u p.1 + p.2
    ring
  exact ⟨(hu _ _).mpr he.le, (hu _ _).mpr he.ge⟩

/-- A weakly preferred starting bundle guarantees that the compensation stays feasible. -/
theorem quasiLinear_compensation_of_preferred {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r) {p q : X × ℝ≥0}
    (hpq : r p q) : ∃ n : ℝ≥0, (n : ℝ) = q.2 + QuasiLinearDifference u p q ∧
      Indifferent r p (q.1, n) := by
  have hd : 0 ≤ QuasiLinearDifference u p q := sub_nonneg.mpr ((hu p q).mp hpq)
  have hf := add_nonneg q.2.property hd
  exact ⟨.mk _ hf, rfl, quasiLinear_compensation hu p q hf⟩

/-- Reusing the original goods, as in the printed final formula, fails even for linear utility. -/
theorem printed_compensation_bundle_counterexample :
    ¬Indifferent (UtilityPref (QuasiLinearUtility (fun x : ℝ≥0 => (x : ℝ))))
      (1, 0) (1, 1) := by
  norm_num [Indifferent, UtilityPref, QuasiLinearUtility]

end Kreps.PreferenceProperties
