/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ProductQuasiconcavity
import PreferenceProperties.Rationalization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The split product-level counterexample

Kreps I, Problem 2.8a, second utility. The level with product four is split into
two ranks according to the relative sizes of the two commodities. Preferences
are semi-strictly convex but discontinuous. The obstruction to every concave
representation is proved separately in `SplitProductNoConcavity`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The exact utility `u₂`, with the lower half of the product-four level valued at four. -/
noncomputable def SplitProductUtility (x : NonnegativeOrthant 2) : ℝ :=
  if TwoGoodProduct x < 4 then TwoGoodProduct x
  else if TwoGoodProduct x = 4 then if x.val 1 ≤ x.val 0 then 4 else 5
  else TwoGoodProduct x + 1

/-- Below the split level, the second utility is the commodity product. -/
theorem splitProductUtility_below {x : NonnegativeOrthant 2} (hx : TwoGoodProduct x < 4) :
    SplitProductUtility x = TwoGoodProduct x := by
  simp [SplitProductUtility, hx]

/-- On the lower half of the split level, utility equals four. -/
theorem splitProductUtility_at_lower {x : NonnegativeOrthant 2}
    (hx : TwoGoodProduct x = 4) (hc : x.val 1 ≤ x.val 0) : SplitProductUtility x = 4 := by
  simp [SplitProductUtility, hx, hc]

/-- On the upper half of the split level, utility equals five. -/
theorem splitProductUtility_at_upper {x : NonnegativeOrthant 2}
    (hx : TwoGoodProduct x = 4) (hc : x.val 0 < x.val 1) : SplitProductUtility x = 5 := by
  simp [SplitProductUtility, hx, not_le_of_gt hc]

/-- Above the split level, utility is the product plus one. -/
theorem splitProductUtility_above {x : NonnegativeOrthant 2} (hx : 4 < TwoGoodProduct x) :
    SplitProductUtility x = TwoGoodProduct x + 1 := by
  simp [SplitProductUtility, not_lt_of_ge hx.le, ne_of_gt hx]

/-- Zero-product bundles all have zero utility. -/
theorem splitProductUtility_zero {x : NonnegativeOrthant 2} (hx : TwoGoodProduct x = 0) :
    SplitProductUtility x = 0 := by
  simp [SplitProductUtility, hx]

/-- The second utility is nonnegative everywhere. -/
theorem splitProductUtility_nonneg (x : NonnegativeOrthant 2) : 0 ≤ SplitProductUtility x := by
  have hp : 0 ≤ TwoGoodProduct x := mul_nonneg (x.property 0) (x.property 1)
  unfold SplitProductUtility
  split_ifs <;> linarith

/-- Strictly increasing the product strictly improves utility, including across the split level. -/
theorem splitProductUtility_strict_of_product_lt {x y : NonnegativeOrthant 2}
    (hxy : TwoGoodProduct x < TwoGoodProduct y) :
    SplitProductUtility x < SplitProductUtility y := by
  unfold SplitProductUtility
  split_ifs <;> linarith

/-- A higher utility rank cannot have a lower commodity product. -/
theorem splitProductUtility_product_le {x y : NonnegativeOrthant 2}
    (hxy : SplitProductUtility y ≤ SplitProductUtility x) :
    TwoGoodProduct y ≤ TwoGoodProduct x := by
  by_contra h
  exact not_lt_of_ge hxy (splitProductUtility_strict_of_product_lt (lt_of_not_ge h))

/-- All upper preference contours of the second utility are convex. -/
theorem splitProductPreference_convex :
    ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) (UtilityPref SplitProductUtility) := by
  intro x y hxy a ha
  by_cases h0 : a = 0
  · subst a
    rw [mix_zero]
    exact le_rfl
  by_cases h1 : a = 1
  · subst a
    rw [mix_one]
    exact hxy
  by_cases he : x = y
  · subst x
    rw [mix_self]
    exact le_rfl
  have hai : a ∈ Set.Ioo 0 1 :=
    ⟨lt_of_le_of_ne ha.1 (Ne.symm h0), lt_of_le_of_ne ha.2 h1⟩
  by_cases hy : TwoGoodProduct y = 0
  · change SplitProductUtility y ≤ _
    rw [splitProductUtility_zero hy]
    exact splitProductUtility_nonneg _
  · have hyp : 0 < TwoGoodProduct y :=
      lt_of_le_of_ne (mul_nonneg (y.property 0) (y.property 1)) (Ne.symm hy)
    exact (splitProductUtility_strict_of_product_lt
      (twoGoodProduct_mix_strict hyp (splitProductUtility_product_le hxy) he hai)).le

/-- Strictly ordered endpoints give a strict improvement under every interior mixture. -/
theorem splitProductPreference_semiStrict :
    SemiStrictlyConvexPreference (convex_Ici (0 : Fin 2 → ℝ))
      (UtilityPref SplitProductUtility) := by
  refine ⟨splitProductPreference_convex, ?_⟩
  intro x y hxy a ha
  have hu : Represents SplitProductUtility (UtilityPref SplitProductUtility) := fun _ _ => Iff.rfl
  have hstrict := (strict_iff_utility_lt hu x y).mp hxy
  have hne : x ≠ y := by intro he; subst x; exact lt_irrefl _ hstrict
  apply (strict_iff_utility_lt hu _ y).mpr
  apply splitProductUtility_strict_of_product_lt
  by_cases hy : TwoGoodProduct y = 0
  · have hx : TwoGoodProduct x ≠ 0 := by
      intro hx
      rw [splitProductUtility_zero hx, splitProductUtility_zero hy] at hstrict
      exact lt_irrefl _ hstrict
    have hxp : 0 < TwoGoodProduct x :=
      lt_of_le_of_ne (mul_nonneg (x.property 0) (x.property 1)) (Ne.symm hx)
    rw [hy]
    exact twoGoodProduct_mix_pos hxp ha
  · have hyp : 0 < TwoGoodProduct y :=
      lt_of_le_of_ne (mul_nonneg (y.property 0) (y.property 1)) (Ne.symm hy)
    exact twoGoodProduct_mix_strict hyp (splitProductUtility_product_le hstrict.le) hne ha

/-- A sequence above the split level converges to its lower-rank midpoint. -/
noncomputable def SplitProductApproach (n : ℕ) : NonnegativeOrthant 2 :=
  PairBundle (2 + (1 / 2 : ℝ) ^ n) 2 (by positivity) (by norm_num)

/-- The bundles approaching `(2,2)` have utility strictly above the rank-five bundle `(1,4)`. -/
theorem splitProductApproach_rank (n : ℕ) :
    UtilityPref SplitProductUtility (SplitProductApproach n)
      (PairBundle 1 4 (by norm_num) (by norm_num)) := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hprod : 4 < TwoGoodProduct (SplitProductApproach n) := by
    dsimp [TwoGoodProduct, SplitProductApproach, PairBundle]
    norm_num
    linarith
  change SplitProductUtility _ ≤ SplitProductUtility _
  rw [splitProductUtility_above hprod]
  norm_num [SplitProductUtility, TwoGoodProduct, PairBundle, SplitProductApproach]
  linarith

/-- The sequence converges in the full orthant topology. -/
theorem splitProductApproach_tendsto :
    Filter.Tendsto SplitProductApproach Filter.atTop
      (𝓝 (PairBundle 2 2 (by norm_num) (by norm_num))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · change Filter.Tendsto (fun n : ℕ => 2 + (1 / 2 : ℝ) ^ n) _ (𝓝 (2 : ℝ))
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  · exact tendsto_const_nhds

/-- An upper contour fails to contain the limit of a converging sequence of its members. -/
theorem splitProductPreference_not_continuous :
    ¬ ContinuousPreference (UtilityPref SplitProductUtility) := by
  intro hc
  have hclosed := ((proposition_1_14c (proposition_1_3a SplitProductUtility)).mp hc
    (PairBundle 1 4 (by norm_num) (by norm_num))).2
  have hmem := hclosed.mem_of_tendsto splitProductApproach_tendsto
    (Filter.Eventually.of_forall splitProductApproach_rank)
  norm_num [NoWorseThan, UtilityPref, SplitProductUtility, TwoGoodProduct, PairBundle] at hmem

end Kreps.PreferenceProperties
