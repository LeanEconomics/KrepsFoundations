/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.MarketExamples

/-!
# Why the maintained restrictions matter

Kreps I, p. 68, permits indifference throughout the region where every good is
below 1000, without requiring indifference everywhere. A nonconstant utility
with exactly this plateau rationalizes the otherwise inconsistent original data.
The p. 73 distinction between strict interior and boundary comparisons is also
witnessed by a strictly increasing linear utility with tied budget maximizers.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}

/-- A nonconstant utility flat on the box below the source's threshold 1000. -/
noncomputable def ThousandPlateauUtility (x : Fin k → ℝ) : ℝ :=
  ∑ i, max 0 (x i - 1000)

/-- Every bundle whose coordinates are at most 1000 has zero plateau utility. -/
theorem thousandPlateauUtility_zero {x : Fin k → ℝ} (hx : ∀ i, x i ≤ 1000) :
    ThousandPlateauUtility x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact max_eq_left (sub_nonpos.mpr (hx i))

/-- All bundles in the book's open box are indifferent to one another. -/
theorem thousandPlateauUtility_indifferent {x z : NonnegativeOrthant k}
    (hx : ∀ i, x.val i < 1000) (hz : ∀ i, z.val i < 1000) :
    Indifferent (UtilityPref
      (fun w : NonnegativeOrthant k => ThousandPlateauUtility w.val)) x z := by
  change ThousandPlateauUtility z.val ≤ ThousandPlateauUtility x.val ∧
    ThousandPlateauUtility x.val ≤ ThousandPlateauUtility z.val
  rw [thousandPlateauUtility_zero (fun i => (hx i).le),
    thousandPlateauUtility_zero (fun i => (hz i).le)]
  exact ⟨le_rfl, le_rfl⟩

/-- Prices of at least one bound each affordable quantity by income. -/
theorem affordable_coordinate_le_income {p : Fin k → ℝ} (hp : ∀ i, 1 ≤ p i)
    {y : ℝ} {x : NonnegativeOrthant k} (hx : x ∈ Budget p y) (i : Fin k) : x.val i ≤ y := by
  calc
    x.val i ≤ p i * x.val i := le_mul_of_one_le_left (x.property i) (hp i)
    _ ≤ Expenditure p x.val := Finset.single_le_sum
      (fun j _ => mul_nonneg (zero_le_one.trans (hp j)) (x.property j)) (Finset.mem_univ i)
    _ ≤ y := hx

/-- The nonconstant plateau utility rationalizes every budget in the original inconsistent data. -/
theorem thousandPlateauUtility_rationalizes :
    Rationalizes InitialData
      (UtilityPref (fun x : NonnegativeOrthant 3 => ThousandPlateauUtility x.val)) := by
  intro i
  have hp : ∀ j, 1 ≤ InitialData.price i j := by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [InitialData]
  have hy : InitialData.income i ≤ 1000 := by fin_cases i <;> norm_num [InitialData]
  have hz (x : NonnegativeOrthant 3) (hx : x ∈ Budget (InitialData.price i)
      (InitialData.income i)) : ThousandPlateauUtility x.val = 0 :=
    thousandPlateauUtility_zero (fun j => (affordable_coordinate_le_income hp hx j).trans hy)
  refine ⟨InitialData.feasible i, fun x hx => ?_⟩
  change ThousandPlateauUtility x.val ≤ ThousandPlateauUtility (InitialData.bundle i).val
  rw [hz x hx, hz _ (InitialData.feasible i)]

/-- The plateau utility is not the constant indifference representation. -/
theorem thousandPlateauUtility_nonconstant :
    ThousandPlateauUtility (![0, 0, 0] : Fin 3 → ℝ) = 0 ∧
      ThousandPlateauUtility (![1001, 0, 0] : Fin 3 → ℝ) = 1 := by
  norm_num [ThousandPlateauUtility, Fin.sum_univ_succ]

/-- Linear utility leaves distinct bundles on the same budget boundary indifferent. -/
theorem linear_boundary_tie :
    ∃ r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop,
      Rational r ∧ LocallyInsatiable r ∧
      ∃ x z : NonnegativeOrthant 2,
        x ≠ z ∧ x ∈ PrefChoice r (Budget ![1, 1] 1) ∧
        z ∈ PrefChoice r (Budget ![1, 1] 1) ∧ ¬Strict r x z := by
  let u : NonnegativeOrthant 2 → ℝ := fun x => Expenditure ![1, 1] x.val
  let x : NonnegativeOrthant 2 := ⟨![1, 0], by intro i; fin_cases i <;> norm_num⟩
  let z : NonnegativeOrthant 2 := ⟨![0, 1], by intro i; fin_cases i <;> norm_num⟩
  have hu : StrictMono u := by
    intro a b hab
    exact affineExpenditure_strictMono (by intro i; fin_cases i <;> norm_num) hab
  have hxu : u x = 1 := by norm_num [u, x, Expenditure, Fin.sum_univ_two]
  have hzu : u z = 1 := by norm_num [u, z, Expenditure, Fin.sum_univ_two]
  refine ⟨UtilityPref u, utilityPref_rational u,
    strictlyMonotone_locallyInsatiable (by norm_num)
      (strictlyMonotonePreference_of_strictMono hu), x, z, ?_, ?_, ?_, ?_⟩
  · intro he
    have h := congrArg (fun w : NonnegativeOrthant 2 => w.val 0) he
    norm_num [x, z] at h
  · refine ⟨hxu.le, fun w hw => ?_⟩
    change u w ≤ u x
    rw [hxu]
    exact hw
  · refine ⟨hzu.le, fun w hw => ?_⟩
    change u w ≤ u z
    rw [hzu]
    exact hw
  · intro hs
    apply hs.2
    change u x ≤ u z
    rw [hxu, hzu]

end Kreps.RevealedPreference
