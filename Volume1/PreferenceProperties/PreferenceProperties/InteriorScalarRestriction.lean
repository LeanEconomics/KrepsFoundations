/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveSeparability
import Mathlib.Topology.Algebra.Order.UpperLower

/-!
# Restricting scalar preferences to interval interiors

Nondegenerate real intervals have nonempty interiors. Coordinatewise restriction
preserves strong separability, continuity and strict monotonicity, supplying the
open-domain hypotheses used in the additive-existence construction.
-/

namespace Kreps.PreferenceProperties

/-- A nondegenerate real interval contains an interior point. -/
theorem nontrivial_interval_interior_nonempty {S : Set ℝ} [Nontrivial S]
    (hS : S.OrdConnected) : (interior S).Nonempty := by
  have hnt : S.Nontrivial := Set.nontrivial_coe_sort.mp inferInstance
  obtain ⟨a, ha, b, hb, hab⟩ := hnt.exists_lt
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (Ioo_mem_nhds hac hcb)
    (fun _ hx => hS.out ha hb ⟨hx.1.le, hx.2.le⟩)

/-- Coordinatewise maps commute with replacing a finite collection of blocks. -/
theorem coordinateMap_piecewise {I : Type*} [DecidableEq I] {A B : I → Type*}
    (f : ∀ i, A i → B i) (s : Finset I) (x y : ∀ i, A i) :
    (fun i => f i (s.piecewise x y i)) =
      s.piecewise (fun i => f i (x i)) (fun i => f i (y i)) := by
  funext i
  by_cases hi : i ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- Strong separability is preserved by arbitrary coordinatewise restriction maps. -/
theorem stronglySeparable_coordinate_pullback {I : Type*} [DecidableEq I]
    {A B : I → Type*} {r : (∀ i, B i) → (∀ i, B i) → Prop}
    (hr : StronglySeparable r) (f : ∀ i, A i → B i) :
    StronglySeparable (fun x y => r (fun i => f i (x i)) (fun i => f i (y i))) := by
  intro s x y z t
  simp only [coordinateMap_piecewise]
  exact hr s _ _ _ _

/-- Include every interior coordinate in its full scalar interval. -/
def InteriorScalarInclusion {I : Type*} {S : I → Set ℝ}
    (x : ∀ i, interior (S i)) : ∀ i, S i :=
  fun i => Set.inclusion interior_subset (x i)

/-- The coordinatewise interior inclusion is continuous. -/
theorem interiorScalarInclusion_continuous {I : Type*} {S : I → Set ℝ} :
    Continuous (@InteriorScalarInclusion I S) :=
  continuous_pi (fun i => (continuous_inclusion interior_subset).comp (continuous_apply i))

/-- The coordinatewise interior inclusion preserves the strict product order. -/
theorem interiorScalarInclusion_strictMono {I : Type*} {S : I → Set ℝ} :
    StrictMono (@InteriorScalarInclusion I S) := by
  intro x y hxy
  apply lt_iff_le_not_ge.mpr
  refine ⟨fun i => hxy.le i, ?_⟩
  intro h
  exact (not_le_of_gt hxy) (fun i => h i)

/-- Strong separability survives restricting all scalar intervals to their interiors. -/
theorem interiorScalarInclusion_stronglySeparable {I : Type*} [DecidableEq I]
    {S : I → Set ℝ} {V : (∀ i, S i) → ℝ} (hs : StronglySeparable (UtilityPref V)) :
    StronglySeparable (UtilityPref (V ∘ InteriorScalarInclusion)) :=
  stronglySeparable_coordinate_pullback hs (fun _ => Set.inclusion interior_subset)

end Kreps.PreferenceProperties
