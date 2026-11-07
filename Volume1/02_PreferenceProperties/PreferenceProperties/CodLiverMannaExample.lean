/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Homotheticity
import PreferenceProperties.MonotonicityExamples
import PreferenceProperties.Rationalization

/-!
# The cod liver oil and manna rank reversal

Kreps I, Section 2.7, p. 44. The book ranks `(1,2)` above `(1/5,14/5)` but
ranks `(1,14)` above `(5,10)`, reversing the comparison after multiplication
by five. These two rankings alone contradict homotheticity.

The book does not specify a utility formula. The utility constructed here is
an explicit continuous witness of its rankings: oil's health contribution
saturates at one teaspoon, while additional manna remains desirable.
-/

namespace Kreps.PreferenceProperties

/-- The source's smaller bundle containing one full teaspoon of cod liver oil. -/
def CodLiverMannaHealthBundle : NonnegativeOrthant 2 :=
  PairBundle 1 2 (by norm_num) (by norm_num)

/-- The source's smaller bundle with more manna but only one fifth teaspoon of oil. -/
noncomputable def CodLiverMannaTasteBundle : NonnegativeOrthant 2 :=
  PairBundle (1 / 5) (14 / 5) (by norm_num) (by norm_num)

/-- Multiplying the first source bundle by five gives `(5,10)`. -/
theorem codLiverManna_health_scale_five :
    ScaleBundle 5 CodLiverMannaHealthBundle = PairBundle 5 10 (by norm_num) (by norm_num) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> norm_num [ScaleBundle, CodLiverMannaHealthBundle, PairBundle]

/-- Multiplying the second source bundle by five gives `(1,14)`. -/
theorem codLiverManna_taste_scale_five :
    ScaleBundle 5 CodLiverMannaTasteBundle = PairBundle 1 14 (by norm_num) (by norm_num) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> norm_num [ScaleBundle, CodLiverMannaTasteBundle, PairBundle]

/-- The exact two source rankings already rule out homotheticity, independently of any utility. -/
theorem codLiverManna_rank_reversal_not_homothetic
    {r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop}
    (hsmall : Strict r CodLiverMannaHealthBundle CodLiverMannaTasteBundle)
    (hlarge : Strict r (PairBundle 1 14 (by norm_num) (by norm_num))
      (PairBundle 5 10 (by norm_num) (by norm_num))) : ¬HomotheticPreference r := by
  intro hh
  have h := hh CodLiverMannaHealthBundle CodLiverMannaTasteBundle 5 hsmall.1
  rw [codLiverManna_health_scale_five, codLiverManna_taste_scale_five] at h
  exact hlarge.2 h

/-- A constructed witness of the source rankings, with oil's benefit capped at one teaspoon. -/
noncomputable def CodLiverMannaUtility (x : NonnegativeOrthant 2) : ℝ :=
  2 * min (x.val 0) 1 + x.val 1

/-- The illustrative utility is continuous, including at the oil-satiation threshold. -/
theorem codLiverMannaUtility_continuous : Continuous CodLiverMannaUtility :=
  (continuous_const.mul (((continuous_apply 0).comp continuous_subtype_val).min
    continuous_const)).add ((continuous_apply 1).comp continuous_subtype_val)

/-- The four utility values reproduce the book's strict rank reversal exactly. -/
theorem codLiverMannaUtility_values :
    CodLiverMannaUtility CodLiverMannaHealthBundle = 4 ∧
      CodLiverMannaUtility CodLiverMannaTasteBundle = 16 / 5 ∧
      CodLiverMannaUtility (PairBundle 5 10 (by norm_num) (by norm_num)) = 12 ∧
      CodLiverMannaUtility (PairBundle 1 14 (by norm_num) (by norm_num)) = 16 := by
  norm_num [CodLiverMannaUtility, CodLiverMannaHealthBundle, CodLiverMannaTasteBundle, PairBundle]

/-- One continuous rational preference realizes both exact comparisons in the p. 44 example. -/
theorem codLiverManna_example :
    Rational (UtilityPref CodLiverMannaUtility) ∧
      ContinuousPreference (UtilityPref CodLiverMannaUtility) ∧
      Strict (UtilityPref CodLiverMannaUtility)
        CodLiverMannaHealthBundle CodLiverMannaTasteBundle ∧
      Strict (UtilityPref CodLiverMannaUtility)
        (PairBundle 1 14 (by norm_num) (by norm_num))
        (PairBundle 5 10 (by norm_num) (by norm_num)) ∧
      ¬HomotheticPreference (UtilityPref CodLiverMannaUtility) := by
  have hsmall : Strict (UtilityPref CodLiverMannaUtility)
      CodLiverMannaHealthBundle CodLiverMannaTasteBundle := by
    norm_num [Strict, UtilityPref, codLiverMannaUtility_values.1,
      codLiverMannaUtility_values.2.1]
  have hlarge : Strict (UtilityPref CodLiverMannaUtility)
      (PairBundle 1 14 (by norm_num) (by norm_num))
      (PairBundle 5 10 (by norm_num) (by norm_num)) := by
    norm_num [Strict, UtilityPref, codLiverMannaUtility_values.2.2.1,
      codLiverMannaUtility_values.2.2.2]
  exact ⟨proposition_1_3a _, proposition_2_9_forward (fun _ _ => Iff.rfl)
    codLiverMannaUtility_continuous, hsmall, hlarge,
    codLiverManna_rank_reversal_not_homothetic hsmall hlarge⟩

end Kreps.PreferenceProperties
