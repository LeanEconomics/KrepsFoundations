/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.LocalToGlobalOrder
import PreferenceProperties.UtilityEquivalence
import Mathlib.Analysis.Convex.Basic

/-!
# Globalizing aligned local additive representations

Supporting Proposition 2.14. Straight paths inside products of real intervals
make their total score monotone between ordered endpoints. Consequently local
representation by one aligned sum is a global representation. Constructing
and aligning those coordinate scales is a separate, explicit obligation.
-/

namespace Kreps.PreferenceProperties

open scoped unitInterval BigOperators

/-- Coordinatewise straight interpolation stays in a product of real intervals. -/
def intervalProductPath {K : Type*} {S : K → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (x y : ∀ i, S i) (t : I) (i : K) : S i :=
  ⟨(1 - t.val) * (x i).val + t.val * (y i).val, by
    simpa only [smul_eq_mul] using (hS i).convex (x i).property (y i).property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩

/-- Straight interpolation is continuous in the product's relative topology. -/
theorem intervalProductPath_continuous {K : Type*} {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i) :
    Continuous (intervalProductPath hS x y) := by
  apply continuous_pi
  intro i
  exact (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

/-- Straight interpolation has the prescribed endpoints. -/
theorem intervalProductPath_endpoints {K : Type*} {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i) :
    intervalProductPath hS x y 0 = x ∧ intervalProductPath hS x y 1 = y := by
  constructor <;> funext i <;> apply Subtype.ext <;> simp [intervalProductPath]

/-- Total score increases along the straight path whenever its endpoint scores are ordered. -/
theorem intervalProductPath_sum_monotone {K : Type*} [Fintype K] {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (x y : ∀ i, S i)
    (hxy : ∑ i, (x i).val ≤ ∑ i, (y i).val) :
    Monotone (fun t : I => ∑ i, (intervalProductPath hS x y t i).val) := by
  have hs (t : I) : (∑ i, (intervalProductPath hS x y t i).val) =
      (1 - t.val) * (∑ i, (x i).val) + t.val * (∑ i, (y i).val) := by
    simp [intervalProductPath, Finset.sum_add_distrib, Finset.mul_sum]
  intro a b hab
  change a.val ≤ b.val at hab
  change (∑ i, (intervalProductPath hS x y a i).val) ≤
    ∑ i, (intervalProductPath hS x y b i).val
  rw [hs, hs]
  have := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hab)
  nlinarith

/-- Local representation by one aligned sum is global on any finite product of real intervals. -/
theorem sum_represents_of_locally_represents {K : Type*} [Fintype K] {S : K → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) {u : (∀ i, S i) → ℝ}
    (hl : ∀ x, ∃ U : Set (∀ i, S i), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ ∑ i, (y i).val ≤ ∑ i, (z i).val) :
    Represents (fun x : ∀ i, S i => ∑ i, (x i).val) (UtilityPref u) := by
  have h := global_order_of_local_comparisons hl (fun x y hxy =>
    ⟨intervalProductPath hS x y, intervalProductPath_continuous hS x y,
      (intervalProductPath_endpoints hS x y).1, (intervalProductPath_endpoints hS x y).2,
      intervalProductPath_sum_monotone hS x y hxy⟩)
  intro x y
  exact h y x

end Kreps.PreferenceProperties
