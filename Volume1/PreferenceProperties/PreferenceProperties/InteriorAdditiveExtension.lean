/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveSeparability
import PreferenceProperties.DenseProductRepresentation
import PreferenceProperties.IntervalEndpointExtension

/-!
# Additive representation on full interval products

The interior of each nondegenerate score interval is dense. Continuous strictly
increasing extensions of the interior coordinate scales therefore represent the
original utility on the full product, including attained endpoints.
-/

namespace Kreps.PreferenceProperties

/-- A finite sum of strictly increasing coordinate scales is strictly increasing. -/
theorem additiveUtility_strictMono {I : Type*} [Fintype I] {B : I → Type*}
    [∀ i, LinearOrder (B i)] {g : ∀ i, B i → ℝ} (hg : ∀ i, StrictMono (g i)) :
    StrictMono (AdditiveUtility g) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := not_forall.mp (not_le_of_gt hxy)
  apply Finset.sum_lt_sum
  · intro j _
    exact (hg j).monotone (hxy.le j)
  · exact ⟨i, Finset.mem_univ i, hg i (lt_of_not_ge hi)⟩

/-- Interior additive comparisons extend to all endpoints once the scales are continuous. -/
theorem additive_comparison_of_interior {I : Type*} [Fintype I] {S : I → Set ℝ}
    (hS : ∀ i, (S i).OrdConnected) (hn : ∀ i, (interior (S i)).Nonempty)
    {u : (∀ i, S i) → ℝ} (hu : Continuous u) (hum : StrictMono u)
    {g : ∀ i, S i → ℝ} (hg : ∀ i, Continuous (g i)) (hgm : ∀ i, StrictMono (g i))
    (hr : ∀ x y : ∀ i, interior (S i),
      u (fun i => Set.inclusion interior_subset (x i)) ≤
        u (fun i => Set.inclusion interior_subset (y i)) ↔
      (∑ i, g i (Set.inclusion interior_subset (x i))) ≤
        ∑ i, g i (Set.inclusion interior_subset (y i))) :
    Represents (AdditiveUtility g) (UtilityPref u) := by
  let : ∀ i, Fact (S i).OrdConnected := fun i => ⟨hS i⟩
  let D : Set (∀ i, S i) := Set.pi Set.univ (fun i => {x : S i | x.val ∈ interior (S i)})
  have hD : Dense D := dense_pi Set.univ (fun i _ => interval_interior_dense (hS i) (hn i))
  have hlocal : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ AdditiveUtility g x ≤ AdditiveUtility g y := by
    intro x hx y hy
    exact hr (fun i => ⟨(x i).val, hx i (Set.mem_univ i)⟩)
      (fun i => ⟨(y i).val, hy i (Set.mem_univ i)⟩)
  have hglobal := dense_product_comparison hD hu (additiveUtility_continuous hg)
    hum (additiveUtility_strictMono hgm) hlocal
  intro x y
  exact hglobal y x

end Kreps.PreferenceProperties
