/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SplitProductPreference

/-!
# No concave representation of the split product preference

Kreps I, Problem 2.8a, second example. A direct Jensen argument avoids assuming
continuity at the boundary of the consumption domain. Bundles just to the right
of `(2,2)` outrank `(1,4)`, although `(2,2)` is strictly worse than `(1,4)`.
Expressing `(2,2)` as a mixture of such bundles and `(1,2)` contradicts concavity.
-/

namespace Kreps.PreferenceProperties

/-- The ordinal jump at the split level prevents every concave representation. -/
theorem splitProductPreference_no_concave_representation :
    ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref SplitProductUtility) ∧
      ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u := by
  rintro ⟨u, hu, hconc⟩
  let p := PairBundle 2 2 (by norm_num) (by norm_num)
  let b := PairBundle 1 2 (by norm_num) (by norm_num)
  let q := PairBundle 1 4 (by norm_num) (by norm_num)
  have hbp : u b < u p := (strict_iff_utility_lt hu p b).mp (by
    norm_num [Strict, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle, p, b])
  have hpq : u p < u q := (strict_iff_utility_lt hu q p).mp (by
    norm_num [Strict, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle, q, p])
  have hden : 0 < u q - u b := sub_pos.mpr (hbp.trans hpq)
  have hratio0 : 0 < (u p - u b) / (u q - u b) := div_pos (sub_pos.mpr hbp) hden
  have hratio1 : (u p - u b) / (u q - u b) < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  obtain ⟨t, ht, ht1⟩ := exists_between hratio1
  have ht0 : 0 < t := hratio0.trans ht
  have hquantity : 2 < (1 + t) / t := (lt_div_iff₀ ht0).mpr (by linarith)
  let z := PairBundle ((1 + t) / t) 2 (by linarith) (by norm_num)
  have hprod : 4 < TwoGoodProduct z := by
    change 4 < ((1 + t) / t) * 2
    linarith
  have hqz : UtilityPref SplitProductUtility z q := by
    change SplitProductUtility q ≤ SplitProductUtility z
    rw [splitProductUtility_above hprod]
    norm_num [q, SplitProductUtility, TwoGoodProduct, PairBundle]
    change 5 ≤ TwoGoodProduct z + 1
    linarith
  have huqz : u q ≤ u z := (hu z q).mp hqz
  have hm : Mix (convex_Ici (0 : Fin 2 → ℝ)) z b t ⟨ht0.le, ht1.le⟩ = p := by
    apply Subtype.ext
    funext j
    fin_cases j
    · change t * ((1 + t) / t) + (1 - t) * 1 = 2
      field_simp
      ring
    · change t * 2 + (1 - t) * 2 = 2
      ring
  have hj := hconc z b t ⟨ht0.le, ht1.le⟩
  rw [hm] at hj
  have htineq := (div_lt_iff₀ hden).mp ht
  have hmul := mul_le_mul_of_nonneg_left huqz ht0.le
  nlinarith

/-- **Problem 2.8a, second example:** semi-strict convexity without concave representability. -/
theorem problem_2_8a_second :
    Rational (UtilityPref SplitProductUtility) ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref SplitProductUtility) ∧
      SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
        (UtilityPref SplitProductUtility) ∧
      ¬ ContinuousPreference (UtilityPref SplitProductUtility) ∧
      ¬ ∃ u : NonnegativeOrthant 2 → ℝ, Represents u (UtilityPref SplitProductUtility) ∧
        ConcaveUtility (convex_Ici (0 : Fin 2 → ℝ)) u :=
  ⟨proposition_1_3a _, splitProductPreference_convex, splitProductPreference_semiStrict,
    splitProductPreference_not_continuous, splitProductPreference_no_concave_representation⟩

end Kreps.PreferenceProperties
