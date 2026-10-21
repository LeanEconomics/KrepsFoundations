/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.PairSumRepresentation
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.IntermediateValue

/-!
# Additive representation after a change of coordinate scales

Preparation for Kreps I, Proposition 2.14. Continuous strictly increasing
coordinate scales on connected ordered blocks have interval ranges. The
finite transfer theorem therefore applies directly to pair comparisons stated
in those scales, and yields their sum as an actual utility representation.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B C : I → Type*}

/-- Applying coordinate maps commutes with replacing one coordinate. -/
theorem coordinateMap_update [DecidableEq I] (f : ∀ i, B i → C i) (x : ∀ i, B i)
    (i : I) (a : B i) :
    (fun j => f j (Function.update x i a j)) =
      Function.update (fun j => f j (x j)) i (f i a) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

/-- Pair transfers stated in continuous increasing scales determine the full additive utility. -/
theorem represents_additive_of_pair_scale_invariance [DecidableEq I] [Fintype I]
    [∀ i, LinearOrder (B i)] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {F : (∀ i, B i) → ℝ} (hm : StrictMono F)
    (w : ∀ i, B i → ℝ) (hwc : ∀ i, Continuous (w i)) (hwm : ∀ i, StrictMono (w i))
    (hp : ∀ (x : ∀ i, B i) (i j : I) (a : B i) (b : B j), i ≠ j →
      w i a + w j b = w i (x i) + w j (x j) →
        F (Function.update (Function.update x i a) j b) = F x) :
    Represents (AdditiveUtility w) (UtilityPref F) := by
  let : ∀ i, Set.OrdConnected (Set.range (w i)) :=
    fun i => (isPreconnected_range (hwc i)).ordConnected
  let e (i : I) : B i ≃o Set.range (w i) := (hwm i).orderIso (w i)
  let E : (∀ i, B i) ≃o (∀ i, Set.range (w i)) :=
    { toEquiv := Equiv.piCongrRight (fun i => (e i).toEquiv)
      map_rel_iff' := by
        intro x y
        exact forall_congr' (fun i => (e i).le_iff_le) }
  let G : (∀ i, Set.range (w i)) → ℝ := fun q => F (E.symm q)
  have hEi (i : I) (q : Set.range (w i)) : w i ((e i).symm q) = q.val :=
    congrArg Subtype.val ((e i).apply_symm_apply q)
  have hGp : PairSumInvariant G := by
    intro q i j a b hij hab
    have hnum : w i ((e i).symm a) + w j ((e j).symm b) =
        w i ((E.symm q) i) + w j ((E.symm q) j) := by
      change w i ((e i).symm a) + w j ((e j).symm b) =
        w i ((e i).symm (q i)) + w j ((e j).symm (q j))
      simpa only [hEi] using hab
    have hh := hp (E.symm q) i j ((e i).symm a) ((e j).symm b) hij hnum
    change F (fun k => (e k).symm (Function.update (Function.update q i a) j b k)) = _
    rw [coordinateMap_update, coordinateMap_update]
    exact hh
  have hGm : StrictMono G := hm.comp E.symm.strictMono
  intro x y
  have hcmp := pairSumInvariant_comparison hGp hGm (E y) (E x)
  change F (E.symm (E y)) ≤ F (E.symm (E x)) ↔ _ at hcmp
  rw [E.symm_apply_apply, E.symm_apply_apply] at hcmp
  exact hcmp

end Kreps.PreferenceProperties
