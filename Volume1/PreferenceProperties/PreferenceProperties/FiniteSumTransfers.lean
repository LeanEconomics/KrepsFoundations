/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite transfers preserving coordinate sums

Preparation for Kreps I, Proposition 2.14. On a finite product of real intervals,
any two bundles with the same coordinate sum are joined by finitely many
two-coordinate transfers preserving that sum. An objective invariant under
these elementary transfers is therefore constant on every sum level set.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {S : I → Set ℝ}

/-- Taking the numerical values of interval coordinates commutes with coordinate replacement. -/
theorem intervalValues_update [DecidableEq I] (x : ∀ i, S i) (i : I) (a : S i) :
    (fun j => (Function.update x i a j).val) = Function.update (fun j => (x j).val) i a.val := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

/-- Replacing one numerical coordinate changes a finite sum by the difference in its value. -/
theorem sum_interval_update [DecidableEq I] (s : Finset I) (x : ∀ i, S i) {i : I}
    (hi : i ∈ s) (a : S i) :
    (∑ j ∈ s, (Function.update x i a j).val) = (∑ j ∈ s, (x j).val) - (x i).val + a.val := by
  rw [intervalValues_update, Finset.sum_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add s (fun j => (x j).val) hi
  linarith

/-- Unequal finite vectors with the same sum have both a deficit coordinate and a surplus one. -/
theorem finite_sum_opposite_coordinates (s : Finset I) (x y : I → ℝ)
    (hSum : ∑ i ∈ s, x i = ∑ i ∈ s, y i) (hne : ¬∀ i ∈ s, x i = y i) :
    ∃ i ∈ s, ∃ j ∈ s, x i < y i ∧ y j < x j := by
  have hleft : ∃ i ∈ s, x i < y i := by
    by_contra h
    push Not at h
    have he := (Finset.sum_eq_sum_iff_of_le h).mp hSum.symm
    exact hne (fun i hi => (he i hi).symm)
  obtain ⟨i, hi, hix⟩ := hleft
  have hright : ∃ j ∈ s, y j < x j := by
    by_contra h
    push Not at h
    have hlt := Finset.sum_lt_sum h ⟨i, hi, hix⟩
    exact (ne_of_lt hlt) hSum
  obtain ⟨j, hj, hjx⟩ := hright
  exact ⟨i, hi, j, hj, hix, hjx⟩

/-- The elementary two-coordinate transfer invariance needed for the additive construction. -/
def PairSumInvariant [DecidableEq I] (F : (∀ i, S i) → ℝ) : Prop :=
  ∀ (x : ∀ i, S i) (i j : I) (a : S i) (b : S j), i ≠ j →
    a.val + b.val = (x i).val + (x j).val →
      F (Function.update (Function.update x i a) j b) = F x

/-- Equal sums on a finite changing set imply equal utility under pair-transfer invariance. -/
theorem pairSumInvariant_eq_of_sum_eq_on [DecidableEq I] [∀ i, Set.OrdConnected (S i)]
    {F : (∀ i, S i) → ℝ} (hF : PairSumInvariant F) (s : Finset I)
    (x y : ∀ i, S i) (hSum : ∑ i ∈ s, (x i).val = ∑ i ∈ s, (y i).val)
    (hout : ∀ i ∉ s, x i = y i) : F x = F y := by
  induction s using Finset.strongInductionOn generalizing x y with
  | _ s ih =>
    by_cases he : ∀ i ∈ s, (x i).val = (y i).val
    · have hxy : x = y := by
        funext i
        by_cases hi : i ∈ s
        · exact Subtype.ext (he i hi)
        · exact hout i hi
      exact congrArg F hxy
    · obtain ⟨i, hi, j, hj, hix, hjx⟩ :=
        finite_sum_opposite_coordinates s (fun i => (x i).val) (fun i => (y i).val) hSum he
      have hij : i ≠ j := by intro h; subst j; linarith
      let δ := min ((y i).val - (x i).val) ((x j).val - (y j).val)
      have hδ : 0 ≤ δ := le_min (sub_nonneg.mpr hix.le) (sub_nonneg.mpr hjx.le)
      have hδi : δ ≤ (y i).val - (x i).val := min_le_left _ _
      have hδj : δ ≤ (x j).val - (y j).val := min_le_right _ _
      let a : S i := ⟨(x i).val + δ,
        (show Set.OrdConnected (S i) from inferInstance).out (x i).property (y i).property
          ⟨by linarith, by linarith⟩⟩
      let b : S j := ⟨(x j).val - δ,
        (show Set.OrdConnected (S j) from inferInstance).out (y j).property (x j).property
          ⟨by linarith, by linarith⟩⟩
      let z := Function.update (Function.update x i a) j b
      have hzi : z i = a := by simp [z, hij]
      have hzj : z j = b := by simp [z]
      have hzk (k : I) (hki : k ≠ i) (hkj : k ≠ j) : z k = x k := by
        simp only [z, Function.update_of_ne hki, Function.update_of_ne hkj]
      have hsumz : ∑ k ∈ s, (z k).val = ∑ k ∈ s, (y k).val := by
        change (∑ k ∈ s, (Function.update (Function.update x i a) j b k).val) = _
        rw [sum_interval_update s _ hj, sum_interval_update s _ hi,
          Function.update_of_ne hij.symm]
        change (∑ k ∈ s, (x k).val) - (x i).val + ((x i).val + δ) - (x j).val +
          ((x j).val - δ) = _
        linarith
      have hFz : F z = F x := hF x i j a b hij (by dsimp [a, b]; ring)
      have hmatch : ∃ k ∈ s, z k = y k := by
        rcases le_total ((y i).val - (x i).val) ((x j).val - (y j).val) with h | h
        · refine ⟨i, hi, ?_⟩
          rw [hzi]
          apply Subtype.ext
          simp only [a, δ, min_eq_left h]
          ring
        · refine ⟨j, hj, ?_⟩
          rw [hzj]
          apply Subtype.ext
          simp only [b, δ, min_eq_right h]
          ring
      obtain ⟨k, hk, hky⟩ := hmatch
      have hSum' : ∑ m ∈ s.erase k, (z m).val = ∑ m ∈ s.erase k, (y m).val := by
        have hz := Finset.sum_erase_add s (fun m => (z m).val) hk
        have hy := Finset.sum_erase_add s (fun m => (y m).val) hk
        rw [hky] at hz
        linarith
      have hout' (m : I) (hm : m ∉ s.erase k) : z m = y m := by
        by_cases hmk : m = k
        · subst m
          exact hky
        · have hms : m ∉ s := fun h => hm (Finset.mem_erase.mpr ⟨hmk, h⟩)
          have hmi : m ≠ i := fun h => hms (h ▸ hi)
          have hmj : m ≠ j := fun h => hms (h ▸ hj)
          exact (hzk m hmi hmj).trans (hout m hms)
      exact hFz.symm.trans (ih (s.erase k) (Finset.erase_ssubset hk) z y hSum' hout')

/-- On a finite interval product, two bundles with equal total scores have equal utility. -/
theorem pairSumInvariant_eq_of_sum_eq [DecidableEq I] [Fintype I] [∀ i, Set.OrdConnected (S i)]
    {F : (∀ i, S i) → ℝ} (hF : PairSumInvariant F) (x y : ∀ i, S i)
    (hSum : ∑ i, (x i).val = ∑ i, (y i).val) : F x = F y :=
  pairSumInvariant_eq_of_sum_eq_on hF Finset.univ x y hSum (by simp)

end Kreps.PreferenceProperties
