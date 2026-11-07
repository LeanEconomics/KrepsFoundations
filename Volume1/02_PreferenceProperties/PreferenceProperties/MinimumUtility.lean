/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Homotheticity
import PreferenceProperties.Monotonicity
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Minimum utility and the two forms of strict monotonicity

Kreps I, p. 32. A finite minimum of strictly increasing component utilities
strictly increases when every commodity increases. With at least two goods it
is never strictly monotone in the stronger, coordinatewise product-order sense.
The component utilities have the book's nonnegative one-good domain.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {k : ℕ} [NeZero k]

/-- The minimum of the component utilities in the p. 32 example. -/
noncomputable def MinimumUtility (u : Fin k → ℝ≥0 → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => u j (.mk (x.val j) (x.property j)))

/-- Minimum utility is bounded by each component utility. -/
theorem minimumUtility_le_component (u : Fin k → ℝ≥0 → ℝ)
    (x : NonnegativeOrthant k) (j : Fin k) :
    MinimumUtility u x ≤ u j (.mk (x.val j) (x.property j)) :=
  Finset.inf'_le _ (Finset.mem_univ j)

/-- A component attains the finite minimum. -/
theorem minimumUtility_exists_index (u : Fin k → ℝ≥0 → ℝ) (x : NonnegativeOrthant k) :
    ∃ j, MinimumUtility u x = u j (.mk (x.val j) (x.property j)) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun j => u j (.mk (x.val j) (x.property j)))
  exact ⟨j, hj⟩

/-- Nondecreasing components give nondecreasing minimum utility. -/
theorem minimumUtility_monotone {u : Fin k → ℝ≥0 → ℝ} (hu : ∀ j, Monotone (u j)) :
    Monotone (MinimumUtility u) := by
  intro x y hxy
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u y
  rw [hj]
  exact (minimumUtility_le_component u x j).trans (hu j (hxy j))

/-- Strictly increasing components give strict preference improvement when all goods increase. -/
theorem minimumPreference_strictAllIncrease {u : Fin k → ℝ≥0 → ℝ}
    (hu : ∀ j, StrictMono (u j)) :
    StrictAllIncreasePreference (UtilityPref (MinimumUtility u)) := by
  intro x y hxy
  have hr : Represents (MinimumUtility u) (UtilityPref (MinimumUtility u)) := fun _ _ => Iff.rfl
  apply (strict_iff_utility_lt hr _ _).mpr
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u x
  exact (minimumUtility_le_component u y j).trans_lt ((hu j (hxy j)).trans_eq hj.symm)

/-- Increasing a coordinate other than a minimizing one cannot strictly raise the minimum. -/
theorem minimumPreference_not_strictlyMonotone (hk : 2 ≤ k) (u : Fin k → ℝ≥0 → ℝ) :
    ¬StrictlyMonotonePreference (UtilityPref (MinimumUtility u)) := by
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hj⟩ := minimumUtility_exists_index u (OrthantZero k)
  obtain ⟨i, hij⟩ := exists_ne j
  let y : NonnegativeOrthant k :=
    ⟨Function.update (0 : Fin k → ℝ) i 1, fun a => by
      simp only [Function.update_apply]
      split_ifs <;> norm_num⟩
  have hne : y ≠ OrthantZero k := by
    intro h
    have he := congrArg (fun z : NonnegativeOrthant k => z.val i) h
    simp [y, OrthantZero] at he
  have hyj : (NNReal.mk (y.val j) (y.property j) : ℝ≥0) = 0 := by
    apply NNReal.coe_injective
    change (Function.update (0 : Fin k → ℝ) i 1) j = 0
    simp [Function.update_of_ne hij.symm]
  have hj0 : MinimumUtility u (OrthantZero k) = u j 0 := hj
  have hle : MinimumUtility u y ≤ MinimumUtility u (OrthantZero k) := by
    calc
      MinimumUtility u y ≤ u j (.mk (y.val j) (y.property j)) :=
        minimumUtility_le_component u y j
      _ = u j 0 := congrArg (u j) hyj
      _ = MinimumUtility u (OrthantZero k) := hj0.symm
  intro h
  exact (h y (OrthantZero k) y.property hne).2 hle

/-- The p. 32 example separates all-coordinate increase from strict monotonicity. -/
theorem minimumUtility_example (hk : 2 ≤ k) {u : Fin k → ℝ≥0 → ℝ}
    (hu : ∀ j, StrictMono (u j)) :
    MonotonePreference (UtilityPref (MinimumUtility u)) ∧
      StrictAllIncreasePreference (UtilityPref (MinimumUtility u)) ∧
      LocallyInsatiable (UtilityPref (MinimumUtility u)) ∧
      ¬StrictlyMonotonePreference (UtilityPref (MinimumUtility u)) := by
  have hr : Represents (MinimumUtility u) (UtilityPref (MinimumUtility u)) := fun _ _ => Iff.rfl
  have hs := minimumPreference_strictAllIncrease hu
  exact ⟨(proposition_2_2_monotone hr).mpr (minimumUtility_monotone (fun j => (hu j).monotone)),
    hs, strictAllIncrease_locallyInsatiable hs, minimumPreference_not_strictlyMonotone hk u⟩

end Kreps.PreferenceProperties
