/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.BisymmetricMeanGrid
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions.SumProd

/-!
# Density of bisymmetric mean grids

On a compact ordered interval the dyadic mean grid is dense. Its closure is
closed under the continuous mean; any gap in that closure would contain the
mean of its two boundary points, contradicting strict internality.
-/

namespace Kreps.PreferenceProperties

open Set

variable {α : Type*} [LinearOrder α] [TopologicalSpace α]

/-- Continuity preserves closure under the mean. -/
theorem meanDyadicPoints_closure_mean (M : OrderedBisymmetricMean α) (a b : α)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) {x y : α}
    (hx : x ∈ closure (MeanDyadicPoints M a b))
    (hy : y ∈ closure (MeanDyadicPoints M a b)) :
    M.mean x y ∈ closure (MeanDyadicPoints M a b) := by
  have hm : MapsTo (fun p : α × α => M.mean p.1 p.2)
      (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) (MeanDyadicPoints M a b) :=
    fun _ hp => meanDyadicPoints_mean M a b hp.1 hp.2
  exact hm.closure hc (show (x, y) ∈ closure
    (MeanDyadicPoints M a b ×ˢ MeanDyadicPoints M a b) from
    by simpa only [closure_prod_eq, mem_prod] using And.intro hx hy)

/-- A continuous strict bisymmetric mean has a dense dyadic grid on a compact interval. -/
theorem meanDyadicPoints_dense [OrderTopology α] [CompactSpace α]
    (M : OrderedBisymmetricMean α) (a b : α)
    (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b)
    (hc : Continuous (fun p : α × α => M.mean p.1 p.2)) :
    Dense (MeanDyadicPoints M a b) := by
  intro x
  have hleft : a ∈ closure (MeanDyadicPoints M a b) :=
    subset_closure ⟨0, 0, by norm_num, (meanDyadicGrid_left M a b 0).symm⟩
  have hright : b ∈ closure (MeanDyadicPoints M a b) :=
    subset_closure ⟨0, 1, by norm_num, (meanDyadicGrid_right M a b 0).symm⟩
  have hloClosed : IsClosed (closure (MeanDyadicPoints M a b) ∩ Iic x) :=
    isClosed_closure.inter isClosed_Iic
  have hhiClosed : IsClosed (closure (MeanDyadicPoints M a b) ∩ Ici x) :=
    isClosed_closure.inter isClosed_Ici
  obtain ⟨l, hl⟩ := hloClosed.isCompact.exists_isGreatest ⟨a, hleft, ha x⟩
  obtain ⟨r, hr⟩ := hhiClosed.isCompact.exists_isLeast ⟨b, hright, hb x⟩
  by_contra hx
  have hlx : l < x := lt_of_le_of_ne hl.1.2 (fun h => hx (h ▸ hl.1.1))
  have hxr : x < r := lt_of_le_of_ne hr.1.2 (fun h => hx (h.symm ▸ hr.1.1))
  have hbetween := orderedMean_between M (hlx.trans hxr)
  have hm := meanDyadicPoints_closure_mean M a b hc hl.1.1 hr.1.1
  rcases le_total (M.mean l r) x with h | h
  · exact (not_le_of_gt hbetween.1) (hl.2 ⟨hm, h⟩)
  · exact (not_le_of_gt hbetween.2) (hr.2 ⟨hm, h⟩)

end Kreps.PreferenceProperties
