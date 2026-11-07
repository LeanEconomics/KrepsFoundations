/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ScalarAdditiveChart
import PreferenceProperties.AdditiveChartPairCompatibility

/-!
# Pair compatibility of scalar additive charts

Charts centered at unrelated bundles give the same pair indifferences on
overlapping coordinate domains. Strong separability transports the comparison
between their centers; the finite additive representations cancel their fixed
coordinate contributions.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

/-- Equal pair sums in one local chart remain equal in every overlapping local chart. -/
theorem ScalarAdditiveChart.pair_compatible (C D : ScalarAdditiveChart V)
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, C.domain i) (t : ∀ i, D.domain i)
    {i j : I} (hij : i ≠ j)
    (x : ℝ) (hx : x ∈ C.domain i ∩ D.domain i)
    (x' : ℝ) (hx' : x' ∈ C.domain i ∩ D.domain i)
    (y : ℝ) (hy : y ∈ C.domain j ∩ D.domain j)
    (y' : ℝ) (hy' : y' ∈ C.domain j ∩ D.domain j)
    (he : C.coord i x + C.coord j y = C.coord i x' + C.coord j y') :
    D.coord i x + D.coord j y = D.coord i x' + D.coord j y' := by
  have hC := represented_additive_pair_eq_iff
    (fun p (q : C.domain p) => C.coord p q.val) (fun p => Set.inclusion (C.subset p))
    C.represents z hij ⟨x, hx.1⟩ ⟨x', hx'.1⟩ ⟨y, hy.1⟩ ⟨y', hy'.1⟩
  have hD := represented_additive_pair_eq_iff
    (fun p (q : D.domain p) => D.coord p q.val) (fun p => Set.inclusion (D.subset p))
    D.represents t hij ⟨x, hx.2⟩ ⟨x', hx'.2⟩ ⟨y, hy.2⟩ ⟨y', hy'.2⟩
  apply hD.mp
  exact (stronglySeparable_pair_equality_iff hs
    (fun p => Set.inclusion (C.subset p) (z p)) (fun p => Set.inclusion (D.subset p) (t p))
    hij ⟨x, C.subset i hx.1⟩ ⟨x', C.subset i hx'.1⟩
    ⟨y, C.subset j hy.1⟩ ⟨y', C.subset j hy'.1⟩).mp (hC.mpr he)

end Kreps.PreferenceProperties
