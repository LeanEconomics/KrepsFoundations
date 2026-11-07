/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ScalarChartCompatibility

/-!
# Ordered pair comparisons in scalar additive charts

The unchanged coordinate contributions cancel from weak comparisons as well
as indifference. Strong separability then transports the local pair formula to
any surrounding context, even when that context is outside the chart.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {B C : I → Type*}

/-- The unvaried additive contributions cancel from a weak pair comparison. -/
theorem additiveUtility_pair_le_iff (w : ∀ i, B i → ℝ) (z : ∀ i, B i)
    {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    AdditiveUtility w (Function.update (Function.update z i a) j b) ≤
      AdditiveUtility w (Function.update (Function.update z i a') j b') ↔
        w i a + w j b ≤ w i a' + w j b' := by
  have hformula (p : B i) (q : B j) :
      AdditiveUtility w (Function.update (Function.update z i p) j q) =
        w i p + w j q + ∑ k ∈ ({i, j} : Finset I)ᶜ, w k (z k) := by
    have h := additiveUtility_piecewise w {i, j}
      (Function.update (Function.update z i p) j q) z
    rw [piecewise_pair_updates z z hij p q] at h
    simpa [hij, hij.symm] using h
  rw [hformula, hformula, add_le_add_iff_right]

/-- A local additive chart compares pairs by their two-coordinate sums. -/
theorem represented_additive_pair_le_iff
    (w : ∀ i, B i → ℝ) (e : ∀ i, B i → C i) {V : (∀ i, C i) → ℝ}
    (hu : Represents (AdditiveUtility w) (UtilityPref (fun x => V (fun i => e i (x i)))))
    (z : ∀ i, B i) {i j : I} (hij : i ≠ j) (a a' : B i) (b b' : B j) :
    V (Function.update (Function.update (fun k => e k (z k)) i (e i a)) j (e j b)) ≤
        V (Function.update (Function.update (fun k => e k (z k)) i (e i a')) j (e j b')) ↔
      w i a + w j b ≤ w i a' + w j b' := by
  have h := hu (Function.update (Function.update z i a') j b')
    (Function.update (Function.update z i a) j b)
  simp only [UtilityPref, coordinateMap_update] at h
  exact h.trans (additiveUtility_pair_le_iff w z hij a a' b b')

/-- A scalar chart's pair formula holds in every surrounding context. -/
theorem ScalarAdditiveChart.pair_comparison_iff {S : I → Set ℝ} {V : (∀ i, S i) → ℝ}
    (C : ScalarAdditiveChart V) (hs : StronglySeparable (UtilityPref V))
    (center : ∀ p, C.domain p) (t : ∀ p, S p) {i j : I} (hij : i ≠ j)
    (x : ℝ) (hx : x ∈ C.domain i) (x' : ℝ) (hx' : x' ∈ C.domain i)
    (y : ℝ) (hy : y ∈ C.domain j) (y' : ℝ) (hy' : y' ∈ C.domain j) :
    V (Function.update (Function.update t i ⟨x, C.subset i hx⟩) j ⟨y, C.subset j hy⟩) ≤
        V (Function.update (Function.update t i ⟨x', C.subset i hx'⟩) j ⟨y', C.subset j hy'⟩) ↔
      C.coord i x + C.coord j y ≤ C.coord i x' + C.coord j y' := by
  have h := represented_additive_pair_le_iff
    (fun p (q : C.domain p) => C.coord p q.val) (fun p => Set.inclusion (C.subset p))
    C.represents center hij ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩ ⟨y', hy'⟩
  exact (stronglySeparable_pair_comparison_iff hs t
    (fun p => Set.inclusion (C.subset p) (center p)) hij
    ⟨x, C.subset i hx⟩ ⟨x', C.subset i hx'⟩ ⟨y, C.subset j hy⟩ ⟨y', C.subset j hy'⟩).trans h

end Kreps.PreferenceProperties
