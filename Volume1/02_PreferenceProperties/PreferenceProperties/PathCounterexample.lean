/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousUtility
import PreferenceProperties.MonotonicityExamples
import PreferenceProperties.Rationalization

/-!
# Continuity and local insatiability do not imply coordinatewise path crossing

Kreps I, Problem 2.7, p. 46. The utility x₁ - x₂ is continuous and locally
insatiable. The diagonal path from (4,4) to (1,1) passes from strictly above
to strictly below (3,2) in both coordinates, but has constant utility zero
and therefore never meets that bundle's indifference class of utility one.
-/

namespace Kreps.PreferenceProperties

/-- The first good helps while the second hurts. -/
def NetUtility (x : NonnegativeOrthant 2) : ℝ := x.val 0 - x.val 1

/-- This utility is continuous on the whole orthant. -/
theorem netUtility_continuous : Continuous NetUtility :=
  ((continuous_apply 0).comp continuous_subtype_val).sub
    ((continuous_apply 1).comp continuous_subtype_val)

/-- Increasing just the first good gives an arbitrarily nearby strict improvement. -/
theorem netPreference_locallyInsatiable : LocallyInsatiable (UtilityPref NetUtility) := by
  intro x ε hε
  let y := PairBundle (x.val 0 + ε) (x.val 1)
    (add_nonneg (x.property 0) hε.le) (x.property 1)
  have hd : dist y x ≤ ε := by
    change dist (fun j : Fin 2 => if j = 0 then x.val 0 + ε else x.val 1) x.val ≤ ε
    apply (dist_pi_le_iff hε.le).mpr
    intro j
    fin_cases j
    · simp [abs_of_pos hε]
    · simpa using hε.le
  have hlt : NetUtility x < NetUtility y := by
    change x.val 0 - x.val 1 < (x.val 0 + ε) - x.val 1
    linarith
  exact ⟨y, hd, hlt.le, not_le_of_gt hlt⟩

/-- A continuous diagonal path whose endpoints lie on opposite coordinate sides of the target. -/
def AvoidingPath (t : UnitSegment) : NonnegativeOrthant 2 :=
  ⟨fun _ => 4 - 3 * t.val, fun _ => by
    change 0 ≤ 4 - 3 * t.val
    have ht : t.val ≤ 1 := t.property.2
    linarith⟩

/-- The path has no jumps. -/
theorem avoidingPath_continuous : Continuous AvoidingPath :=
  (continuous_pi fun _ =>
    continuous_const.sub (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The coordinatewise intermediate bundle has utility one. -/
def PathMiddle : NonnegativeOrthant 2 := PairBundle 3 2 (by norm_num) (by norm_num)

/-- Every commodity falls past its target level along the path. -/
theorem avoidingPath_coordinate_bounds :
    (∀ j, PathMiddle.val j < (AvoidingPath ⟨0, by norm_num⟩).val j) ∧
    (∀ j, (AvoidingPath ⟨1, by norm_num⟩).val j < PathMiddle.val j) := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [PathMiddle, PairBundle, AvoidingPath]

/-- Yet no path point is indifferent to the target. -/
theorem avoidingPath_no_indifference :
    ¬∃ t, Indifferent (UtilityPref NetUtility) (AvoidingPath t) PathMiddle := by
  rintro ⟨t, ht⟩
  norm_num [Indifferent, UtilityPref, NetUtility, AvoidingPath, PathMiddle, PairBundle] at ht

/-- **Problem 2.7:** the counterexample also satisfies local insatiability. -/
theorem problem_2_7 :
    Rational (UtilityPref NetUtility) ∧ ContinuousPreference (UtilityPref NetUtility) ∧
    LocallyInsatiable (UtilityPref NetUtility) ∧ Continuous AvoidingPath ∧
    (∀ j, PathMiddle.val j < (AvoidingPath ⟨0, by norm_num⟩).val j) ∧
    (∀ j, (AvoidingPath ⟨1, by norm_num⟩).val j < PathMiddle.val j) ∧
    ¬∃ t, Indifferent (UtilityPref NetUtility) (AvoidingPath t) PathMiddle :=
  ⟨proposition_1_3a _, continuousPreference_of_continuous_utility netUtility_continuous,
    netPreference_locallyInsatiable, avoidingPath_continuous, avoidingPath_coordinate_bounds.1,
    avoidingPath_coordinate_bounds.2, avoidingPath_no_indifference⟩

/-- The failed hypothesis is monotonicity, as the path-crossing theorem also shows. -/
theorem netPreference_not_monotone : ¬MonotonePreference (UtilityPref NetUtility) := by
  intro hm
  apply avoidingPath_no_indifference
  exact monotone_path_crossing (proposition_1_3a _)
    (continuousPreference_of_continuous_utility netUtility_continuous) hm
    AvoidingPath avoidingPath_continuous PathMiddle
    (fun j => (avoidingPath_coordinate_bounds.1 j).le)
    (fun j => (avoidingPath_coordinate_bounds.2 j).le)

end Kreps.PreferenceProperties
