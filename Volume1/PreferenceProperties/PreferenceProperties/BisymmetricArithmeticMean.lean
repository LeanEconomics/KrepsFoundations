/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.BisymmetricMeanRanks
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The arithmetic reference mean

Applying the abstract density result to the ordinary arithmetic mean proves
density of dyadic numerical ranks in the unit interval. This avoids assuming
any cardinal representation for the original preference-induced mean.
-/

namespace Kreps.PreferenceProperties

/-- The usual arithmetic mean, restricted to the closed unit interval. -/
noncomputable def UnitArithmeticMean : OrderedBisymmetricMean (Set.Icc (0 : ℝ) 1) where
  mean x y := ⟨(x.val + y.val) / 2, by
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]⟩
  reflexive x := by apply Subtype.ext; simp
  symmetric x y := by apply Subtype.ext; simp [add_comm]
  bisymmetric x y z w := by apply Subtype.ext; dsimp; ring
  strictMono_left y := by
    intro x z hxz
    change (x.val + y.val) / 2 < (z.val + y.val) / 2
    change x.val < z.val at hxz
    linarith
  strictMono_right x := by
    intro y z hyz
    change (x.val + y.val) / 2 < (x.val + z.val) / 2
    change y.val < z.val at hyz
    linarith

/-- The reference mean is jointly continuous. -/
theorem unitArithmeticMean_continuous : Continuous
    (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => UnitArithmeticMean.mean p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)).div_const 2 |>.subtype_mk _

/-- The reference grid realizes the usual dyadic fractions. -/
theorem unitArithmeticMean_grid (n k : ℕ) (hk : k ≤ 2 ^ n) :
    (MeanDyadicGrid UnitArithmeticMean.mean ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ n k).val =
      MeanDyadicRank n k := by
  induction n generalizing k with
  | zero =>
    norm_num at hk
    interval_cases k <;> simp [MeanDyadicGrid, MeanDyadicRank]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have h₀ : k / 2 ≤ 2 ^ n := by omega
    have h₁ : (k + 1) / 2 ≤ 2 ^ n := by omega
    change ((MeanDyadicGrid UnitArithmeticMean.mean _ _ n (k / 2)).val +
      (MeanDyadicGrid UnitArithmeticMean.mean _ _ n ((k + 1) / 2)).val) / 2 = _
    rw [ih _ h₀, ih _ h₁]
    unfold MeanDyadicRank
    have hsum : ((k / 2 : ℕ) : ℝ) + (((k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast (show k / 2 + (k + 1) / 2 = k by omega)
    rw [← add_div, hsum, pow_succ, div_mul_eq_div_div]

/-- The usual unit-interval dyadic points are dense. -/
theorem unitArithmeticMean_dense :
    Dense (MeanDyadicPoints UnitArithmeticMean ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) :=
  meanDyadicPoints_dense UnitArithmeticMean _ _ (fun x => x.property.1)
    (fun x => x.property.2) unitArithmeticMean_continuous

end Kreps.PreferenceProperties
