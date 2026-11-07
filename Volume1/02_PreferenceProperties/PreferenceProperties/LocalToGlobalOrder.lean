/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

/-!
# Global order from local representations along paths

Supporting the global assembly in Proposition 2.14. A finite subdivision of
a path transports local comparisons from one endpoint to the other. This
step does not assume global representability, differentiability, or a
uniform radius for the local charts.
-/

namespace Kreps.PreferenceProperties

open scoped unitInterval

/-- Local comparisons transport along a monotone-score path, including indifference. -/
theorem interval_order_of_local_comparisons {u v : I → ℝ} (hv : Monotone v)
    (hl : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z) :
    u 0 ≤ u 1 ∧ (u 0 = u 1 → v 0 = v 1) := by
  classical
  choose U hU hx hrel using hl
  have hcover : Set.univ ⊆ ⋃ x, U x :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht0, htm, ⟨N, hN⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU hcover
  have hstep (n : ℕ) : u (t n) ≤ u (t (n + 1)) := by
    obtain ⟨i, hi⟩ := htU n
    have hn := htm (Nat.le_succ n)
    exact (hrel i _ (hi ⟨le_rfl, hn⟩) _ (hi ⟨hn, le_rfl⟩)).mpr (hv hn)
  have hum : Monotone (fun n => u (t n)) := monotone_nat_of_le_succ hstep
  have hle : u 0 ≤ u 1 := by
    simpa only [ht0, hN N le_rfl] using hum (Nat.zero_le N)
  refine ⟨hle, fun he => ?_⟩
  have huconst (n : ℕ) : u (t n) = u 0 := by
    apply le_antisymm
    · calc
        u (t n) ≤ u (t (max n N)) := hum (le_max_left _ _)
        _ = u 1 := congrArg u (hN _ (le_max_right _ _))
        _ = u 0 := he.symm
    · simpa only [ht0] using hum (Nat.zero_le n)
  have hvconst (n : ℕ) : v (t n) = v 0 := by
    induction n with
    | zero => rw [ht0]
    | succ n ih =>
      obtain ⟨i, hi⟩ := htU n
      have hn := htm (Nat.le_succ n)
      have hlmem := hi (show t n ∈ Set.Icc (t n) (t (n + 1)) from ⟨le_rfl, hn⟩)
      have hrmem := hi (show t (n + 1) ∈ Set.Icc (t n) (t (n + 1)) from ⟨hn, le_rfl⟩)
      have hvle : v (t (n + 1)) ≤ v (t n) :=
        (hrel i _ hrmem _ hlmem).mp (by rw [huconst, huconst])
      exact (le_antisymm hvle (hv hn)).trans ih
  simpa only [hN N le_rfl] using (hvconst N).symm

/-- A strict endpoint score difference is strict in the locally represented order as well. -/
theorem interval_strict_order_of_local_comparisons {u v : I → ℝ} (hv : Monotone v)
    (hl : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z) (hstrict : v 0 < v 1) :
    u 0 < u 1 := by
  obtain ⟨hle, he⟩ := interval_order_of_local_comparisons hv hl
  exact lt_of_le_of_ne hle (fun h => (ne_of_lt hstrict) (he h))

/-- Continuous paths carry a local comparison cover back to the compact unit interval. -/
theorem path_order_of_local_comparisons {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hl : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z)
    {p : I → X} (hp : Continuous p) (hv : Monotone (v ∘ p)) :
    u (p 0) ≤ u (p 1) ∧ (u (p 0) = u (p 1) → v (p 0) = v (p 1)) := by
  apply interval_order_of_local_comparisons (u := u ∘ p) hv
  intro t
  obtain ⟨U, hU, ht, hrel⟩ := hl (p t)
  exact ⟨p ⁻¹' U, hU.preimage hp, ht, fun _ hs _ hr => hrel _ hs _ hr⟩

/-- Local representation is global when every ordered pair admits a monotone-score path. -/
theorem global_order_of_local_comparisons {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hl : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, u y ≤ u z ↔ v y ≤ v z)
    (hp : ∀ x y, v x ≤ v y → ∃ p : I → X,
      Continuous p ∧ p 0 = x ∧ p 1 = y ∧ Monotone (v ∘ p)) :
    ∀ x y, u x ≤ u y ↔ v x ≤ v y := by
  have hle (x y : X) (hxy : v x ≤ v y) :
      u x ≤ u y ∧ (u x = u y → v x = v y) := by
    obtain ⟨p, hpc, hp0, hp1, hpm⟩ := hp x y hxy
    simpa only [hp0, hp1] using path_order_of_local_comparisons hl hpc hpm
  intro x y
  constructor
  · intro hxy
    by_contra hvxy
    have hvyx : v y < v x := lt_of_not_ge hvxy
    obtain ⟨huyx, he⟩ := hle y x hvyx.le
    exact (ne_of_lt hvyx) (he (le_antisymm huyx hxy))
  · intro hxy
    exact (hle x y hxy).1

end Kreps.PreferenceProperties
