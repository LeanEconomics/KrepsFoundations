/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveEndpointBounds
import PreferenceProperties.IntervalEndpointExtension
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Bounds on interior additive coordinates at attained endpoints

Preparation for Proposition 2.14. A continuous strictly increasing preference utility on a
finite product prevents an interior additive coordinate from diverging at an attained endpoint.
An interior change in a companion coordinate gives the strict comparison needed for the bound.
No boundedness or endpoint limit of the additive coordinate is assumed.
-/

namespace Kreps.PreferenceProperties

open Set

/-- Replacing one coordinate changes an additive score by its coordinate-score difference. -/
theorem sum_coordinate_scores_update {I : Type*} [Fintype I] [DecidableEq I]
    {B : I → Type*} (f : ∀ i, B i → ℝ) (z : ∀ i, B i) (i : I) (x : B i) :
    (∑ k, f k (Function.update z i x k)) = (∑ k, f k (z k)) - f i (z i) + f i x := by
  simp_rw [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add Finset.univ (fun k => f k (z k)) (Finset.mem_univ i)
  linarith

/-- Interior inclusion commutes with coordinate replacement. -/
theorem interior_product_inclusion_update {I : Type*} [DecidableEq I] {S : I → Set ℝ}
    (z : ∀ i, interior (S i)) (i : I) (x : interior (S i)) :
    (fun k => inclusion interior_subset (Function.update z i x k)) =
      Function.update (fun k => inclusion interior_subset (z k)) i
        (inclusion interior_subset x) :=
  funext (Function.apply_update (fun k => inclusion (s := interior (S k)) interior_subset) z i x)

/-- Fixing all other coordinates cancels their contribution to interior additive comparisons. -/
theorem interior_additive_pair_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} {f : ∀ i, interior (S i) → ℝ}
    (hr : ∀ x y : ∀ i, interior (S i),
      V (fun i => inclusion interior_subset (x i)) ≤
          V (fun i => inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i))
    (z : ∀ i, interior (S i)) {i j : I} (hij : i ≠ j)
    (x y : interior (S i)) (b c : interior (S j)) :
    V (Function.update (Function.update (fun k => inclusion interior_subset (z k))
        j (inclusion interior_subset b)) i (inclusion interior_subset x)) ≤
      V (Function.update (Function.update (fun k => inclusion interior_subset (z k))
        j (inclusion interior_subset c)) i (inclusion interior_subset y)) ↔
      f i x + f j b ≤ f i y + f j c := by
  have h := hr (Function.update (Function.update z j b) i x)
    (Function.update (Function.update z j c) i y)
  simp_rw [interior_product_inclusion_update] at h
  rw [sum_coordinate_scores_update, sum_coordinate_scores_update,
    sum_coordinate_scores_update, sum_coordinate_scores_update] at h
  simp only [Function.update_of_ne hij] at h
  exact h.trans (by constructor <;> intro hle <;> linarith)

/-- Every attained least or greatest rank gives a finite bound on its interior additive scale. -/
theorem interior_additive_scale_bounds {I : Type*} [Fintype I] [Nontrivial I]
    {S : I → Set ℝ} (hS : ∀ i, (S i).OrdConnected)
    (hne : ∀ i, (interior (S i)).Nonempty) {V : (∀ i, S i) → ℝ}
    (hc : Continuous V) (hm : StrictMono V) {f : ∀ i, interior (S i) → ℝ}
    (hr : ∀ x y : ∀ i, interior (S i),
      V (fun i => inclusion interior_subset (x i)) ≤
          V (fun i => inclusion interior_subset (y i)) ↔
        (∑ i, f i (x i)) ≤ ∑ i, f i (y i)) (i : I) :
    (∀ a : S i, IsBot a → BddBelow (range (f i))) ∧
      ∀ a : S i, IsTop a → BddAbove (range (f i)) := by
  classical
  choose z hz using fun k => hne k
  let q : ∀ k, interior (S k) := fun k => ⟨z k, hz k⟩
  let qFull : ∀ k, S k := fun k => inclusion interior_subset (q k)
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := Ne.symm hji
  obtain ⟨L, R, hLR, hsub⟩ := isOpen_interior.exists_Ioo_subset (hne j)
  obtain ⟨b', hLb, hbR⟩ := exists_between hLR
  obtain ⟨c', hbc, hcR⟩ := exists_between hbR
  let b : interior (S j) := ⟨b', hsub ⟨hLb, hbR⟩⟩
  let c : interior (S j) := ⟨c', hsub ⟨hLb.trans hbc, hcR⟩⟩
  let D : Set (S i) := {x | x.val ∈ interior (S i)}
  let f' : S i → ℝ := fun x => if hx : x.val ∈ interior (S i) then f i ⟨x.val, hx⟩ else 0
  have hf' (x : S i) (hx : x ∈ D) : f' x = f i ⟨x.val, hx⟩ := by
    have hx' : x.val ∈ interior (S i) := hx
    simp [f', hx']
  have himage : f' '' D = range (f i) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, hx⟩, (hf' x hx).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨inclusion interior_subset x, x.property, hf' _ x.property⟩
  let u : S i × interior (S j) → ℝ := fun p =>
    V (Function.update (Function.update qFull j (inclusion interior_subset p.2)) i p.1)
  have huc (d : interior (S j)) : Continuous (fun x : S i => u (x, d)) := by
    change Continuous (fun x : S i => V
      (Function.update (Function.update qFull j (inclusion interior_subset d)) i x))
    exact hc.comp (continuous_const.update i continuous_id)
  have hum (d : interior (S j)) : Monotone (fun x : S i => u (x, d)) := by
    change Monotone (fun x : S i => V
      (Function.update (Function.update qFull j (inclusion interior_subset d)) i x))
    exact hm.monotone.comp Function.update_mono
  have hubc (a : S i) : u (a, b) < u (a, c) := by
    dsimp [u]
    rw [Function.update_comm hji, Function.update_comm hji]
    exact hm (Function.update_strictMono hbc)
  have hur : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f' x + f j b ≤ f' y + f j c := by
    intro x hx y hy
    rw [hf' x hx, hf' y hy]
    exact interior_additive_pair_comparison hr q hij ⟨x.val, hx⟩ ⟨y.val, hy⟩ b c
  constructor
  · intro a ha
    have h := additive_scale_bddBelow_at_least (interval_interior_dense (hS i) (hne i))
      ha (huc b) (hum c) (hubc a) hur
    rwa [himage] at h
  · intro a ha
    have h := additive_scale_bddAbove_at_greatest (interval_interior_dense (hS i) (hne i))
      ha (huc c) (hum b) (hubc a) hur
    rwa [himage] at h

end Kreps.PreferenceProperties
