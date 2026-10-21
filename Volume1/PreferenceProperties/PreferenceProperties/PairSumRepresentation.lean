/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.FiniteSumTransfers
import PreferenceProperties.AdditiveSeparability

/-!
# From pair transfers to a finite additive representation

Preparation for Kreps I, Proposition 2.14. A strictly increasing utility on a
finite interval product is represented by the coordinate sum whenever its
two-coordinate sum-preserving transfers leave utility unchanged. Convex
interpolation supplies the comparison step after the finite transfer argument.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [Fintype I] {S : I → Set ℝ}
variable [∀ i, Set.OrdConnected (S i)]

/-- A smaller total score can be attained at a bundle coordinatewise below the larger one. -/
theorem exists_le_bundle_with_sum (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val ≤ ∑ i, (y i).val) :
    ∃ z : ∀ i, S i, z ≤ y ∧ ∑ i, (z i).val = ∑ i, (x i).val := by
  let m : ∀ i, S i := fun i => min (x i) (y i)
  have hmx : ∑ i, (m i).val ≤ ∑ i, (x i).val :=
    Finset.sum_le_sum (fun i _ => min_le_left _ _)
  have hmy (i : I) : (m i).val ≤ (y i).val := min_le_right _ _
  by_cases he : ∑ i, (y i).val = ∑ i, (m i).val
  · exact ⟨y, le_rfl, le_antisymm (he ▸ hmx) hxy⟩
  · have hpos : 0 < (∑ i, (y i).val) - ∑ i, (m i).val := by
      have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmy i)
      exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm he))
    let θ := ((∑ i, (x i).val) - ∑ i, (m i).val) /
      ((∑ i, (y i).val) - ∑ i, (m i).val)
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hmx) hpos.le
    have hθ1 : θ ≤ 1 := (div_le_one hpos).mpr (by linarith)
    let z : ∀ i, S i := fun i => ⟨(1 - θ) * (m i).val + θ * (y i).val,
      (show Set.OrdConnected (S i) from inferInstance).out (m i).property (y i).property
        ⟨by nlinarith [hmy i], by nlinarith [hmy i]⟩⟩
    refine ⟨z, ?_, ?_⟩
    · intro i
      change (1 - θ) * (m i).val + θ * (y i).val ≤ (y i).val
      nlinarith [hmy i]
    · change (∑ i, ((1 - θ) * (m i).val + θ * (y i).val)) = _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hmul : θ * ((∑ i, (y i).val) - ∑ i, (m i).val) =
          (∑ i, (x i).val) - ∑ i, (m i).val := div_mul_cancel₀ _ hpos.ne'
      nlinarith

/-- Strict comparison of total scores gives strict utility comparison. -/
theorem pairSumInvariant_lt_of_sum_lt [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val < ∑ i, (y i).val) : F x < F y := by
  obtain ⟨z, hzy, hSum⟩ := exists_le_bundle_with_sum x y hxy.le
  have hne : z ≠ y := by
    intro h
    rw [h] at hSum
    exact hxy.ne hSum.symm
  have he := pairSumInvariant_eq_of_sum_eq hF x z hSum.symm
  rw [he]
  exact hm (lt_of_le_of_ne hzy hne)

/-- Every comparison is determined by the sum of the interval coordinates. -/
theorem pairSumInvariant_comparison [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) (x y : ∀ i, S i) :
    F x ≤ F y ↔ (∑ i, (x i).val) ≤ ∑ i, (y i).val := by
  constructor
  · intro h
    by_contra hnot
    exact (not_lt_of_ge h) (pairSumInvariant_lt_of_sum_lt hF hm y x (lt_of_not_ge hnot))
  · intro h
    rcases h.eq_or_lt with he | hl
    · exact (pairSumInvariant_eq_of_sum_eq hF x y he).le
    · exact (pairSumInvariant_lt_of_sum_lt hF hm x y hl).le

/-- Pair-transfer invariance gives the finite additive utility representation. -/
theorem pairSumInvariant_represents [DecidableEq I] {F : (∀ i, S i) → ℝ}
    (hF : PairSumInvariant F) (hm : StrictMono F) :
    Represents (AdditiveUtility (fun i (x : S i) => x.val)) (UtilityPref F) := by
  intro x y
  exact pairSumInvariant_comparison hF hm y x

end Kreps.PreferenceProperties
