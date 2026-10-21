/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.NormalizedCoordinatePairs
import PreferenceProperties.PairwiseAdditiveRepresentation

/-!
# Compatibility of pair sums in local additive charts

Strong separability transports two-coordinate comparisons between the centers
of different additive charts. Their remaining coordinate contributions cancel,
so the charts preserve equal pair sums wherever both coordinate domains overlap.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B C : I → Type*}

/-- In a fixed context the unchanged additive contributions cancel from pair indifferences. -/
theorem additiveUtility_pair_eq_iff [Fintype I] (w : ∀ i, B i → ℝ) (z : ∀ i, B i)
    {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    AdditiveUtility w (Function.update (Function.update z i a) j b) =
      AdditiveUtility w (Function.update (Function.update z i a') j b') ↔
        w i a + w j b = w i a' + w j b' := by
  have hformula (p : B i) (q : B j) :
      AdditiveUtility w (Function.update (Function.update z i p) j q) =
        w i p + w j q + ∑ k ∈ ({i, j} : Finset I)ᶜ, w k (z k) := by
    have h := additiveUtility_piecewise w {i, j}
      (Function.update (Function.update z i p) j q) z
    rw [piecewise_pair_updates z z hij p q] at h
    simpa [hij, hij.symm] using h
  rw [hformula, hformula, add_left_inj]

/-- Pair comparisons are independent of the surrounding context, for arbitrary block types. -/
theorem stronglySeparable_pair_comparison_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) {i j : I}
    (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update z i a) j b) ≤
        V (Function.update (Function.update z i a') j b') ↔
      V (Function.update (Function.update t i a) j b) ≤
        V (Function.update (Function.update t i a') j b') := by
  have h := hs {i, j} (Function.update (Function.update z i a') j b')
    (Function.update (Function.update z i a) j b) z t
  simpa only [piecewise_pair_updates _ _ hij, UtilityPref] using h

/-- Pair indifferences are independent of every unvaried coordinate. -/
theorem stronglySeparable_pair_equality_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) {i j : I}
    (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update z i a) j b) =
        V (Function.update (Function.update z i a') j b') ↔
      V (Function.update (Function.update t i a) j b) =
        V (Function.update (Function.update t i a') j b') := by
  simp only [le_antisymm_iff,
    stronglySeparable_pair_comparison_iff hs z t hij a a' b b',
    stronglySeparable_pair_comparison_iff hs z t hij a' a b' b]

/-- A represented additive chart identifies pair indifference with equality of its pair sums. -/
theorem represented_additive_pair_eq_iff [Fintype I]
    (w : ∀ i, B i → ℝ) (e : ∀ i, B i → C i) {V : (∀ i, C i) → ℝ}
    (hu : Represents (AdditiveUtility w) (UtilityPref (fun x => V (fun i => e i (x i)))))
    (z : ∀ i, B i) {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update (fun k => e k (z k)) i (e i a)) j (e j b)) =
        V (Function.update (Function.update (fun k => e k (z k)) i (e i a')) j (e j b')) ↔
      w i a + w j b = w i a' + w j b' := by
  have hv : Represents (fun x : ∀ i, B i => V (fun i => e i (x i)))
      (UtilityPref (fun x : ∀ i, B i => V (fun i => e i (x i)))) := fun _ _ => Iff.rfl
  have h : V (fun k => e k (Function.update (Function.update z i a) j b k)) =
        V (fun k => e k (Function.update (Function.update z i a') j b' k)) ↔
      AdditiveUtility w (Function.update (Function.update z i a) j b) =
        AdditiveUtility w (Function.update (Function.update z i a') j b') :=
    ⟨same_utility_fibers hv hu, same_utility_fibers hu hv⟩
  simpa only [coordinateMap_update] using h.trans (additiveUtility_pair_eq_iff w z hij a a' b b')

end Kreps.PreferenceProperties
