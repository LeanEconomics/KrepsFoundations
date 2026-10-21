/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Finite additive scales at attained endpoints

Preparation for the boundary cases in Proposition 2.14. Continuity of the
original pair utility and a strict comparison in a companion coordinate
bound the interior additive scale at any attained least or greatest rank.
No boundedness of the constructed cardinal scale is assumed.
-/

namespace Kreps.PreferenceProperties

/-- A least attained rank and one strict companion comparison bound the additive scale below. -/
theorem additive_scale_bddBelow_at_least {X Y : Type*} [Preorder X] [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u : X × Y → ℝ}
    {f : X → ℝ} {g : Y → ℝ} {a : X} (ha : ∀ x, a ≤ x) {b c : Y}
    (hc : Continuous (fun x => u (x, b))) (hm : Monotone (fun x => u (x, c)))
    (hbc : u (a, b) < u (a, c))
    (hr : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f x + g b ≤ f y + g c) :
    BddBelow (f '' D) := by
  have hopen : IsOpen {x | u (x, b) < u (a, c)} := isOpen_lt hc continuous_const
  obtain ⟨x, hx, hux⟩ := hD.exists_mem_open hopen ⟨a, hbc⟩
  refine ⟨f x + g b - g c, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hu : u (x, b) ≤ u (y, c) := hux.le.trans (hm (ha y))
  have := (hr x hx y hy).mp hu
  linarith

/-- A greatest attained rank and one strict companion comparison bound the scale above. -/
theorem additive_scale_bddAbove_at_greatest {X Y : Type*} [Preorder X] [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {u : X × Y → ℝ}
    {f : X → ℝ} {g : Y → ℝ} {a : X} (ha : ∀ x, x ≤ a) {b c : Y}
    (hc : Continuous (fun x => u (x, c))) (hm : Monotone (fun x => u (x, b)))
    (hbc : u (a, b) < u (a, c))
    (hr : ∀ x ∈ D, ∀ y ∈ D,
      u (x, b) ≤ u (y, c) ↔ f x + g b ≤ f y + g c) :
    BddAbove (f '' D) := by
  have hopen : IsOpen {x | u (a, b) < u (x, c)} := isOpen_lt continuous_const hc
  obtain ⟨x, hx, hux⟩ := hD.exists_mem_open hopen ⟨a, hbc⟩
  refine ⟨f x + g c - g b, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hu : u (y, b) ≤ u (x, c) := (hm (ha y)).trans hux.le
  have := (hr y hy x hx).mp hu
  linarith

end Kreps.PreferenceProperties
