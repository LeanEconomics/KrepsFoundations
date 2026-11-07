/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConcaveUtility
import Mathlib.Analysis.Convex.Continuous

/-!
# Appendix 3: concave and convex functions

Kreps I, Definition A3.16, Proposition A3.17 and Proposition A3.23, pp. 461–466.
The weighted affine-composition statements explicitly require the affine arguments
to remain in the original domain. This makes the book's implicit domain convention
precise. Continuity is asserted on the interior, as in the text.
-/

namespace Kreps.PreferenceProperties

open scoped BigOperators

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {S : Set E} {T : Set F} {f : E → ℝ}

/-- **Proposition A3.17a:** an affine function is convex and concave. -/
theorem proposition_A3_17a (hS : Convex ℝ S) (g : E →ᵃ[ℝ] ℝ) :
    ConvexOn ℝ S g ∧ ConcaveOn ℝ S g := by
  constructor
  · exact ⟨hS, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).le⟩
  · exact ⟨hS, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).ge⟩

/-- **Proposition A3.17b:** the pointwise minimum of a finite nonempty family is concave. -/
theorem proposition_A3_17b_min (t : Finset ι) (ht : t.Nonempty) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConcaveOn ℝ S (g i)) : ConcaveOn ℝ S (t.inf' ht g) :=
  Finset.inf'_induction ht g (fun _ hf _ hh => hf.inf hh) hg

/-- **Proposition A3.17c:** the pointwise maximum of a finite nonempty family is convex. -/
theorem proposition_A3_17c_max (t : Finset ι) (ht : t.Nonempty) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConvexOn ℝ S (g i)) : ConvexOn ℝ S (t.sup' ht g) :=
  Finset.sup'_induction ht g (fun _ hf _ hh => hf.sup hh) hg

/-- Finite sums of concave functions are concave, including the empty sum. -/
theorem concaveOn_finite_sum (hS : Convex ℝ S) (t : Finset ι) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConcaveOn ℝ S (g i)) : ConcaveOn ℝ S (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using concaveOn_const (0 : ℝ) hS
  | @insert i t hi ih =>
      have hgi := hg i (Finset.mem_insert_self i t)
      have hgt := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      convert hgi.add hgt using 1
      ext x
      exact Finset.sum_insert hi

/-- Finite sums of convex functions are convex, including the empty sum. -/
theorem convexOn_finite_sum (hS : Convex ℝ S) (t : Finset ι) (g : ι → E → ℝ)
    (hg : ∀ i ∈ t, ConvexOn ℝ S (g i)) : ConvexOn ℝ S (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using convexOn_const (0 : ℝ) hS
  | @insert i t hi ih =>
      have hgi := hg i (Finset.mem_insert_self i t)
      have hgt := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      convert hgi.add hgt using 1
      ext x
      exact Finset.sum_insert hi

/-- **Proposition A3.17b:** nonnegative weighted sums after affine changes of argument. -/
theorem proposition_A3_17b_sum (hS : Convex ℝ S) (t : Finset ι) (w : ι → ℝ)
    (g : ι → F → ℝ) (A : ι → E →ᵃ[ℝ] F) (hw : ∀ i ∈ t, 0 ≤ w i)
    (hg : ∀ i ∈ t, ConcaveOn ℝ T (g i)) (hA : ∀ i ∈ t, Set.MapsTo (A i) S T) :
    ConcaveOn ℝ S (fun x => ∑ i ∈ t, w i * g i (A i x)) := by
  apply concaveOn_finite_sum hS t
  intro i hi
  exact (((hg i hi).comp_affineMap (A i)).subset (hA i hi) hS).smul (hw i hi)

/-- **Proposition A3.17c:** the corresponding convex weighted affine-composition rule. -/
theorem proposition_A3_17c_sum (hS : Convex ℝ S) (t : Finset ι) (w : ι → ℝ)
    (g : ι → F → ℝ) (A : ι → E →ᵃ[ℝ] F) (hw : ∀ i ∈ t, 0 ≤ w i)
    (hg : ∀ i ∈ t, ConvexOn ℝ T (g i)) (hA : ∀ i ∈ t, Set.MapsTo (A i) S T) :
    ConvexOn ℝ S (fun x => ∑ i ∈ t, w i * g i (A i x)) := by
  apply convexOn_finite_sum hS t
  intro i hi
  exact (((hg i hi).comp_affineMap (A i)).subset (hA i hi) hS).smul (hw i hi)

/-- **Proposition A3.17d:** upper contour sets of a concave function are convex. -/
theorem proposition_A3_17d (hf : ConcaveOn ℝ S f) (r : ℝ) :
    Convex ℝ {x ∈ S | r ≤ f x} := hf.convex_ge r

/-- **Proposition A3.17e:** lower contour sets of a convex function are convex. -/
theorem proposition_A3_17e (hf : ConvexOn ℝ S f) (r : ℝ) :
    Convex ℝ {x ∈ S | f x ≤ r} := hf.convex_le r

/-- **Proposition A3.17f:** concavity is convexity of the negative. -/
theorem proposition_A3_17f : ConcaveOn ℝ S f ↔ ConvexOn ℝ S (-f) :=
  neg_convexOn_iff.symm

/-- **Proposition A3.23:** concavity is equivalent to convexity of the hypograph. -/
theorem proposition_A3_23 : ConcaveOn ℝ S f ↔
    Convex ℝ {p : E × ℝ | p.1 ∈ S ∧ p.2 ≤ f p.1} := concaveOn_iff_convex_hypograph

/-- The epigraph version mentioned following Proposition A3.25. -/
theorem convexOn_iff_convex_epigraph_appendix : ConvexOn ℝ S f ↔
    Convex ℝ {p : E × ℝ | p.1 ∈ S ∧ f p.1 ≤ p.2} := convexOn_iff_convex_epigraph

/-- **Proposition A3.17g:** finite-dimensional concavity implies continuity on the interior. -/
theorem proposition_A3_17g_concave {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D : Set G} {g : G → ℝ} (hg : ConcaveOn ℝ D g) :
    ContinuousOn g (interior D) := hg.continuousOn_interior

/-- **Proposition A3.17g:** the corresponding continuity statement for convex functions. -/
theorem proposition_A3_17g_convex {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D : Set G} {g : G → ℝ} (hg : ConvexOn ℝ D g) :
    ContinuousOn g (interior D) := hg.continuousOn_interior

end Kreps.PreferenceProperties
