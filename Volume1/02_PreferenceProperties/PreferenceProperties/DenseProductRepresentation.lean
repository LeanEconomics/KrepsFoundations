/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Extending utility comparisons from a dense product domain

Continuous strictly increasing utilities on products of densely ordered blocks
represent the same preference if they agree on a dense subset. The perturbation
argument preserves strict comparisons at boundary bundles; continuity alone
would only preserve their weak limits.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- Agreement on a dense set transports strict comparisons to weak comparisons everywhere. -/
theorem dense_comparison_strict_implies_le {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y) {x y : X} (hxy : u x < u y) :
    v x ≤ v y := by
  by_contra! h
  have hopen : IsOpen {p : X × X | u p.1 < u p.2 ∧ v p.2 < v p.1} :=
    (isOpen_lt (hu.comp continuous_fst) (hu.comp continuous_snd)).inter
      (isOpen_lt (hv.comp continuous_snd) (hv.comp continuous_fst))
  obtain ⟨⟨a, b⟩, hab, hub, hvb⟩ := (hD.prod hD).exists_mem_open hopen ⟨(x, y), hxy, h⟩
  exact (not_lt_of_ge ((hr a hab.1 b hab.2).mp hub.le)) hvb

/-- There is room for a strict improvement below any higher continuous monotone utility level. -/
theorem exists_product_improvement_below {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {u v : (∀ i, B i) → ℝ} (hu : StrictMono u) (hv : Continuous v) (hvm : Monotone v)
    {x y : ∀ i, B i} (hxy : v x < v y) :
    ∃ z, u x < u z ∧ v z < v y := by
  classical
  have hnot : ¬ y ≤ x := fun h => (not_lt_of_ge (hvm h)) hxy
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hxi : x i < y i := lt_of_not_ge hi
  have hc : Continuous (fun a : B i => v (Function.update x i a)) :=
    hv.comp (continuous_const.update i continuous_id)
  have hn : {a : B i | v (Function.update x i a) < v y} ∈ 𝓝 (x i) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hxy)
  obtain ⟨b, hb, hsub⟩ := exists_Ico_subset_of_mem_nhds hn ⟨y i, hxi⟩
  obtain ⟨a, hxa, hab⟩ := exists_between hb
  have hlt : x < Function.update x i a := by
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simpa using hxa.le
      · simp only [Function.update_of_ne hj, le_refl]
    · intro h
      have hi' := h i
      simp only [Function.update_self] at hi'
      exact (not_le_of_gt hxa) hi'
  exact ⟨Function.update x i a, hu hlt, hsub ⟨hxa.le, hab⟩⟩

/-- Dense agreement preserves strict comparisons on products, including their endpoints. -/
theorem dense_product_strict_comparison {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {D : Set (∀ i, B i)} (hD : Dense D) {u v : (∀ i, B i) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hum : StrictMono u) (hvm : Monotone v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y)
    {x y : ∀ i, B i} (hxy : v x < v y) : u x < u y := by
  have hr' : ∀ x ∈ D, ∀ y ∈ D, v x ≤ v y ↔ u x ≤ u y :=
    fun x hx y hy => (hr x hx y hy).symm
  have hle := dense_comparison_strict_implies_le hD hv hu hr' hxy
  by_contra! hnot
  have heq := le_antisymm hle hnot
  obtain ⟨z, hzu, hzv⟩ := exists_product_improvement_below hum hv hvm hxy
  have hle' := dense_comparison_strict_implies_le hD hv hu hr' hzv
  exact (not_lt_of_ge (hle'.trans_eq heq.symm)) hzu

/-- Continuous strictly increasing product utilities agreeing densely agree everywhere. -/
theorem dense_product_comparison {I : Type*} {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, DenselyOrdered (B i)]
    [∀ i, TopologicalSpace (B i)] [∀ i, OrderTopology (B i)]
    {D : Set (∀ i, B i)} (hD : Dense D) {u v : (∀ i, B i) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hum : StrictMono u) (hvm : StrictMono v)
    (hr : ∀ x ∈ D, ∀ y ∈ D, u x ≤ u y ↔ v x ≤ v y) :
    ∀ x y, u x ≤ u y ↔ v x ≤ v y := by
  intro x y
  constructor
  · intro h
    by_contra! hv'
    exact (not_lt_of_ge h) (dense_product_strict_comparison hD hu hv hum hvm.monotone hr hv')
  · intro h
    by_contra! hu'
    exact (not_lt_of_ge h) (dense_product_strict_comparison hD hv hu hvm hum.monotone
      (fun x hx y hy => (hr x hx y hy).symm) hu')

end Kreps.PreferenceProperties
