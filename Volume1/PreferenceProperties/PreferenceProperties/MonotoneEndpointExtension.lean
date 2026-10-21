/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Extending interval scales to attained endpoints

A continuous monotone scale on a dense subset extends continuously when the
only missing points are least or greatest elements and the corresponding
one-sided range is bounded. On a densely ordered domain, strict monotonicity
is preserved. These lemmas supply the endpoint step for Proposition 2.14.
-/

namespace Kreps.PreferenceProperties

open Filter
open scoped Topology

/-- Approaching a missing least element is cofinal in the dense domain's lower end. -/
theorem tendsto_dense_comap_atBot {X : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] {D : Set X} {a : X} (ha : a ∉ D) (hmin : IsBot a) :
    Tendsto (id : D → D) ((𝓝 a).comap ((↑) : D → X)) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have hab : a < (b : X) := lt_of_le_of_ne (hmin b) (fun h => ha (h ▸ b.property))
  have hn : {x : D | (x : X) < (b : X)} ∈ (𝓝 a).comap ((↑) : D → X) :=
    Filter.preimage_mem_comap (Iio_mem_nhds hab)
  exact Filter.mem_of_superset hn (fun _ hx => hx.le)

/-- Approaching a missing greatest element is cofinal in the dense domain's upper end. -/
theorem tendsto_dense_comap_atTop {X : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] {D : Set X} {a : X} (ha : a ∉ D) (hmax : IsTop a) :
    Tendsto (id : D → D) ((𝓝 a).comap ((↑) : D → X)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hab : (b : X) < a := lt_of_le_of_ne (hmax b) (fun h => ha (h ▸ b.property))
  have hn : {x : D | (b : X) < (x : X)} ∈ (𝓝 a).comap ((↑) : D → X) :=
    Filter.preimage_mem_comap (Ioi_mem_nhds hab)
  exact Filter.mem_of_superset hn (fun _ hx => hx.le)

/-- Finite one-sided bounds give a continuous extension across missing extreme points. -/
theorem exists_continuous_endpoint_extension {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    (hedge : ∀ x, x ∉ D → IsBot x ∨ IsTop x) {f : D → ℝ}
    (hf : Continuous f) (hm : Monotone f)
    (hlo : ∀ x, x ∉ D → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x, x ∉ D → IsTop x → BddAbove (Set.range f)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x : D, g x = f x := by
  have hlimit : ∀ x : X, ∃ y : ℝ,
      Tendsto f ((𝓝 x).comap ((↑) : D → X)) (𝓝 y) := by
    intro x
    by_cases hx : x ∈ D
    · refine ⟨f ⟨x, hx⟩, ?_⟩
      rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
      exact hf.continuousAt
    · rcases hedge x hx with hmin | hmax
      · exact ⟨⨅ d, f d, (tendsto_atBot_ciInf hm (hlo x hx hmin)).comp
          (tendsto_dense_comap_atBot hx hmin)⟩
      · exact ⟨⨆ d, f d, (tendsto_atTop_ciSup hm (hhi x hx hmax)).comp
          (tendsto_dense_comap_atTop hx hmax)⟩
  exact ⟨hD.extend f, hD.continuous_extend hlimit, hD.extend_eq hf⟩

/-- A continuous extension of a dense monotone function is below every later dense value. -/
theorem continuous_extension_le_dense {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : Monotone f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) {x : X} {a : D} (hxa : x < (a : X)) :
    g x ≤ f a := by
  by_contra! h
  have hopen : IsOpen {z : X | f a < g z ∧ z < (a : X)} :=
    (isOpen_lt continuous_const hg).inter isOpen_Iio
  obtain ⟨z, hz, hzg, hza⟩ := hD.exists_mem_open hopen ⟨x, h, hxa⟩
  have hmono := hm (show (⟨z, hz⟩ : D) ≤ a from hza.le)
  rw [← heq ⟨z, hz⟩] at hmono
  exact (not_lt_of_ge hmono) hzg

/-- A continuous extension of a dense monotone function is above every earlier dense value. -/
theorem dense_le_continuous_extension {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : Monotone f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) {x : X} {a : D} (hax : (a : X) < x) :
    f a ≤ g x := by
  by_contra! h
  have hopen : IsOpen {z : X | g z < f a ∧ (a : X) < z} :=
    (isOpen_lt hg continuous_const).inter isOpen_Ioi
  obtain ⟨z, hz, hzg, haz⟩ := hD.exists_mem_open hopen ⟨x, h, hax⟩
  have hmono := hm (show a ≤ (⟨z, hz⟩ : D) from haz.le)
  rw [← heq ⟨z, hz⟩] at hmono
  exact (not_lt_of_ge hmono) hzg

/-- A continuous extension of a strictly increasing dense scale stays strictly increasing. -/
theorem continuous_extension_strictMono {X : Type*} [LinearOrder X] [DenselyOrdered X]
    [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    {f : D → ℝ} (hm : StrictMono f) {g : X → ℝ} (hg : Continuous g)
    (heq : ∀ x : D, g x = f x) : StrictMono g := by
  intro x y hxy
  obtain ⟨a, ha, hxa, hay⟩ := hD.exists_between hxy
  obtain ⟨b, hb, hab, hby⟩ := hD.exists_between hay
  have hlo := continuous_extension_le_dense hD hm.monotone hg heq
    (a := ⟨a, ha⟩) hxa
  have hhi := dense_le_continuous_extension hD hm.monotone hg heq
    (a := ⟨b, hb⟩) hby
  exact hlo.trans_lt ((hm (show (⟨a, ha⟩ : D) < ⟨b, hb⟩ from hab)).trans_le hhi)

/-- A dense strict scale extends continuously and strictly across bounded attained endpoints. -/
theorem exists_continuous_strictMono_endpoint_extension {X : Type*} [LinearOrder X]
    [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X] {D : Set X} (hD : Dense D)
    (hedge : ∀ x, x ∉ D → IsBot x ∨ IsTop x) {f : D → ℝ}
    (hf : Continuous f) (hm : StrictMono f)
    (hlo : ∀ x, x ∉ D → IsBot x → BddBelow (Set.range f))
    (hhi : ∀ x, x ∉ D → IsTop x → BddAbove (Set.range f)) :
    ∃ g : X → ℝ, Continuous g ∧ StrictMono g ∧ ∀ x : D, g x = f x := by
  obtain ⟨g, hg, heq⟩ := exists_continuous_endpoint_extension hD hedge hf hm.monotone hlo hhi
  exact ⟨g, hg, continuous_extension_strictMono hD hm hg heq, heq⟩

end Kreps.PreferenceProperties
