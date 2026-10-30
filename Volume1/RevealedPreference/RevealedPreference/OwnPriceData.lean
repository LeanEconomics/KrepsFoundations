/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.AfriatTheorem
import RevealedPreference.ComparativeStatics

/-!
# Own-price observations and a boundary correction

Kreps I, p. 75. The two-observation argument assumes positive consumption of the
changing-price commodity in the original observation. The later finite-sequence
claim omits this condition and is false at the boundary. We prove the corrected
finite-data assertion and an exact two-observation counterexample to the printed
unrestricted claim. See `docs/corrections.md`.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- At common income with other prices fixed, cross-cost is the own-price difference. -/
theorem ownPriceData_cost {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l) (i j : I) :
    D.cost i j = (D.price i g - D.price j g) * (D.bundle j).val g := by
  unfold MarketData.cost
  rw [expenditure_own_price (fun l hl => hp i j l hl), he j, hy j i]
  ring

/-- Positive own-good quantities validate the finite own-price consistency claim. -/
theorem garp_of_own_price_data {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l)
    (hx : ∀ i, 0 < (D.bundle i).val g) : GARP D := by
  apply matrixGARP_of_scores (fun i => -D.price i g)
  · intro i j hij
    change D.cost i j ≤ 0 at hij
    rw [ownPriceData_cost he hy hp i j] at hij
    have h : D.price i g - D.price j g ≤ 0 :=
      le_of_not_gt (fun hh => (not_lt_of_ge hij) (mul_pos hh (hx j)))
    linarith
  · intro i j hij
    change D.cost i j < 0 at hij
    rw [ownPriceData_cost he hy hp i j] at hij
    have h : D.price i g - D.price j g < 0 :=
      lt_of_not_ge (fun hh => (not_le_of_gt hij) (mul_nonneg hh (hx j).le))
    linarith

/-- The corrected finite own-price assertion supplies a full-domain regular rationalizer. -/
theorem own_price_data_rationalizable [Finite I] {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l)
    (hx : ∀ i, 0 < (D.bundle i).val g) :
    ∃ u : (Fin k → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧
      ConcaveOn ℝ Set.univ u ∧
      Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) :=
  garp_exists_concave_utility (garp_of_own_price_data he hy hp hx)

/-- The source's two-observation claim needs positive own consumption only in the old bundle. -/
theorem garp_two_own_price_observations {D : MarketData (Fin 2) k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : D.income 0 = D.income 1) (hp : OwnPriceIncrease (D.price 0) (D.price 1) g)
    (hx : 0 < (D.bundle 0).val g) : GARP D := by
  have hdiag (i : Fin 2) : D.cost i i = 0 := by simp [MarketData.cost, he]
  have h10 : 0 < D.cost 1 0 := by
    unfold MarketData.cost
    rw [expenditure_own_price hp.2, he 0, hy]
    simpa using mul_pos (sub_pos.mpr hp.1) hx
  apply matrixGARP_of_scores ![1, 0]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [DirectWeak, hdiag] at *
    exact (not_le_of_gt h10 hij).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [DirectStrict, hdiag] at *
    exact (not_lt_of_ge h10.le hij).elim

/-- Two feasible exhausted observations at increasing own prices, with zero old own demand. -/
noncomputable def BoundaryOwnPriceData : MarketData (Fin 2) 2 where
  price := ![![1, 1], ![2, 1]]
  income := fun _ => 1
  bundle := fun i => ⟨![![0, 1], ![1 / 4, 1 / 2]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, Fin.sum_univ_two]

/-- Both counterexample observations exhaust the same income. -/
theorem boundaryOwnPriceData_exhausts (i : Fin 2) :
    Expenditure (BoundaryOwnPriceData.price i) (BoundaryOwnPriceData.bundle i).val = 1 := by
  fin_cases i <;> norm_num [BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]

/-- The second observation raises only the first price, from one to two. -/
theorem boundaryOwnPriceData_price_increase :
    OwnPriceIncrease (BoundaryOwnPriceData.price 0) (BoundaryOwnPriceData.price 1) 0 := by
  constructor
  · norm_num [BoundaryOwnPriceData]
  · intro j hj
    fin_cases j <;> norm_num [BoundaryOwnPriceData] at *

/-- The omitted positive-consumption condition permits a strict two-observation cycle. -/
theorem boundaryOwnPriceData_not_garp : ¬GARP BoundaryOwnPriceData := by
  intro hG
  apply hG 0
  apply revealedStrict_weak_trans
    (directStrict_revealedStrict (j := 1) ?_) (directWeak_revealedWeak ?_)
  · norm_num [DirectStrict, MarketData.cost, BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]
  · norm_num [DirectWeak, MarketData.cost, BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]

end Kreps.RevealedPreference
