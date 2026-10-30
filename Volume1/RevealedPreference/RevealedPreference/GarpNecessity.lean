/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.MarketData

/-!
# Local insatiability implies GARP

Kreps I, Lemma 4.1, p. 68, and the necessity direction of Proposition 4.3,
pp. 70-71. Local improvements inside a strict budget establish strict preference
over every strictly cheaper alternative. Rationality propagates these comparisons
along all finite revealed chains. No numerical representation is assumed.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- **Lemma 4.1:** an optimal bundle strictly dominates every strictly affordable bundle. -/
theorem lemma_4_1 (hr : Rational r) (hl : LocallyInsatiable r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : Expenditure p z.val < y) : Strict r x z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (strictBudget_isOpen p y) z hz
  obtain ⟨w, hw, hwp⟩ := locallyInsatiable_iff_open.mp hl z ε hε
  have hwstrict : Expenditure p w.val < y := hball (Metric.mem_ball.mpr hw)
  have hwb : w ∈ Budget p y := hwstrict.le
  exact weak_strict_trans hr.2 (hx.2 w hwb) hwp

/-- A locally insatiable maximum exhausts its budget. -/
theorem optimal_budget_exhaustion (hr : Rational r) (hl : LocallyInsatiable r)
    {p : Fin k → ℝ} {y : ℝ} {x : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) : Expenditure p x.val = y := by
  apply le_antisymm hx.1
  apply le_of_not_gt
  intro hs
  have h := lemma_4_1 hr hl hx hs
  exact h.2 h.1

/-- Rationalization transports every weak revealed chain to a weak preference comparison. -/
theorem rationalizes_revealedWeak {D : MarketData I k} (hr : Rational r)
    (hR : Rationalizes D r) {i j : I} (hij : RevealedWeak D.cost i j) :
    r (D.bundle i) (D.bundle j) := by
  induction hij with
  | refl => exact complete_refl hr.1 _
  | @tail j l _ hjl ih =>
    exact hr.2 _ _ _ ih ((hR j).2 _ (sub_nonpos.mp hjl))

/-- A strict edge in a revealed chain yields strict preference under local insatiability. -/
theorem rationalizes_revealedStrict {D : MarketData I k} (hr : Rational r)
    (hl : LocallyInsatiable r) (hR : Rationalizes D r) {i j : I}
    (hij : RevealedStrict D.cost i j) : Strict r (D.bundle i) (D.bundle j) := by
  obtain ⟨a, b, hia, hab, hbj⟩ := hij
  exact strict_weak_trans hr.2
    (weak_strict_trans hr.2 (rationalizes_revealedWeak hr hR hia)
      (lemma_4_1 hr hl (hR a) (sub_lt_zero.mp hab)))
    (rationalizes_revealedWeak hr hR hbj)

/-- **Proposition 4.3, necessity:** rational, locally insatiable rationalization implies GARP. -/
theorem rationalizes_garp {D : MarketData I k} (hr : Rational r)
    (hl : LocallyInsatiable r) (hR : Rationalizes D r) : GARP D := by
  intro i hi
  have h := rationalizes_revealedStrict hr hl hR hi
  exact h.2 h.1

end Kreps.RevealedPreference
