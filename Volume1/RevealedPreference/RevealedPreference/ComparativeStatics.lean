/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.GarpNecessity

/-!
# Slutsky compensation and the Giffen implication

Kreps I, Propositions 4.6-4.8, pp. 76-77, and Problem 4.4, p. 78. The proofs
use primitive rational, locally insatiable preferences and actual maximizers.
They require neither differentiability nor uniqueness. Proposition 4.7 takes the
lower-income maximizer conditionally, as the source explicitly permits when
continuity is not maintained.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A price increase changes exactly one coordinate. -/
def OwnPriceIncrease (p q : Fin k → ℝ) (i : Fin k) : Prop :=
  p i < q i ∧ ∀ j, j ≠ i → q j = p j

/-- Expenditure changes by the own-price increment times the purchased quantity. -/
theorem expenditure_own_price {p q : Fin k → ℝ} {i : Fin k}
    (h : ∀ j, j ≠ i → q j = p j) (x : Fin k → ℝ) :
    Expenditure q x = Expenditure p x + (q i - p i) * x i := by
  classical
  have he : ∀ j, q j * x j = p j * x j +
      if j = i then (q i - p i) * x i else 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [ite_eq_left]
      ring
    · simp [hj, h j hj]
  simp only [Expenditure, he, Finset.sum_add_distrib]
  simp

/-- Slutsky compensation makes the new choice no cheaper at the old prices. -/
theorem compensated_old_expenditure (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) :
    Expenditure p x.val ≤ Expenditure p z.val := by
  rw [optimal_budget_exhaustion hr hl hx]
  apply le_of_not_gt
  intro hs
  exact (lemma_4_1 hr hl hx hs).2 (hz.2 x (by simp [Budget]))

/-- **Proposition 4.6:** the compensated own-price effect is nonpositive. -/
theorem proposition_4_6 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) : z.val i ≤ x.val i := by
  have hcost := compensated_old_expenditure hr hl hx hz
  have hnew := optimal_budget_exhaustion hr hl hz
  rw [expenditure_own_price hp.2 z.val, expenditure_own_price hp.2 x.val] at hnew
  have hmul : (q i - p i) * z.val i ≤ (q i - p i) * x.val i := by linarith
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hp.1)).mp hmul

/-- The price-change dot product expands into the difference of the two cost changes. -/
theorem expenditure_price_quantity_difference (p q x z : Fin k → ℝ) :
    Expenditure (q - p) (z - x) =
      (Expenditure q z - Expenditure q x) -
        (Expenditure p z - Expenditure p x) := by
  unfold Expenditure
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Proposition 4.8 / Problem 4.4:** the compensated price-quantity dot product is nonpositive. -/
theorem proposition_4_8 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) :
    Expenditure (q - p) (z.val - x.val) ≤ 0 := by
  rw [expenditure_price_quantity_difference, optimal_budget_exhaustion hr hl hz]
  have h := compensated_old_expenditure hr hl hx hz
  linarith

/-- A Giffen response is strictly cheaper at the original prices and hence lowers income. -/
theorem giffen_lower_income (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hz : z ∈ PrefChoice r (Budget q y))
    (hg : x.val i < z.val i) : Expenditure p z.val < y := by
  have hnew := optimal_budget_exhaustion hr hl hz
  rw [expenditure_own_price hp.2 z.val] at hnew
  have hzpos : 0 < z.val i := (x.property i).trans_lt hg
  have hprod := mul_pos (sub_pos.mpr hp.1) hzpos
  linarith

/-- A lower-income choice in the Giffen argument consumes at least the new own quantity. -/
theorem giffen_lower_income_quantity (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {z w : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hz : z ∈ PrefChoice r (Budget q y))
    (hw : w ∈ PrefChoice r (Budget p (Expenditure p z.val))) : z.val i ≤ w.val i := by
  apply le_of_not_gt
  intro hlt
  have hwcost := optimal_budget_exhaustion hr hl hw
  have hzq := optimal_budget_exhaustion hr hl hz
  have hprod := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hp.1)
  have hwq : Expenditure q w.val < y := by
    rw [expenditure_own_price hp.2 w.val, hwcost]
    rw [expenditure_own_price hp.2 z.val] at hzq
    linarith
  exact (lemma_4_1 hr hl hz hwq).2 (hw.2 z (by simp [Budget]))

/-- **Proposition 4.7:** Giffen behavior implies a strict inferior-good comparison. -/
theorem proposition_4_7 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z w : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q y))
    (hg : x.val i < z.val i)
    (hw : w ∈ PrefChoice r (Budget p (Expenditure p z.val))) :
    Expenditure p z.val < y ∧ x.val i < w.val i := by
  have hy := optimal_budget_exhaustion hr hl hx
  have hlow : Expenditure p z.val < Expenditure p x.val := by
    rw [hy]
    exact giffen_lower_income hr hl hp hz hg
  exact ⟨hy ▸ hlow, hg.trans_le (giffen_lower_income_quantity hr hl hp hz hw)⟩

end Kreps.RevealedPreference
