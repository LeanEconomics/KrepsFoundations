/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.PrimitiveAdditiveExistence
import PreferenceProperties.CommodityPartitionTopology

/-!
# Additive utility on the original partitioned commodity orthant

**Proposition 2.14**, p. 42, on the book's original nonnegative commodity
orthant. A total assignment `owner` specifies the full partition: each good
belongs to exactly one block. Grouping quantities is a homeomorphism, so the
primitive preference assumptions give continuous functions of the original
block quantities whose sum represents preference. Empty or inessential blocks
are allowed; only three blocks are required to be nontrivial.
-/

namespace Kreps.PreferenceProperties

variable {k n : ℕ}

/-- Original preference expressed in the quantities of a full commodity partition. -/
def PartitionPreference (owner : Fin k → Fin n)
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop)
    (x y : ∀ i, PartitionBlock owner i) : Prop :=
  r (PartitionUngroup owner x) (PartitionUngroup owner y)

/-- Sum the block utilities at the original commodity bundle. -/
def PartitionAdditiveUtility (owner : Fin k → Fin n)
    (w : ∀ i, PartitionBlock owner i → ℝ) (x : NonnegativeOrthant k) : ℝ :=
  AdditiveUtility w (PartitionGroup owner x)

/-- Rationality is unchanged when the original quantities are grouped into blocks. -/
theorem partitionPreference_rational (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    Rational (PartitionPreference owner r) :=
  ⟨fun x y => hr.1 (PartitionUngroup owner x) (PartitionUngroup owner y),
    fun x y z => hr.2 (PartitionUngroup owner x) (PartitionUngroup owner y)
      (PartitionUngroup owner z)⟩

/-- Continuity of preference survives the homeomorphic regrouping of commodity quantities. -/
theorem partitionPreference_continuous (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hc : ContinuousPreference r) :
    ContinuousPreference (PartitionPreference owner r) :=
  hc.preimage (((partitionUngroup_continuous owner).comp continuous_fst).prodMk
    ((partitionUngroup_continuous owner).comp continuous_snd))

/-- Continuous block utility functions give a continuous utility of the original commodities. -/
theorem partitionAdditiveUtility_continuous (owner : Fin k → Fin n)
    {w : ∀ i, PartitionBlock owner i → ℝ} (hw : ∀ i, Continuous (w i)) :
    Continuous (PartitionAdditiveUtility owner w) :=
  (additiveUtility_continuous hw).comp (partitionGroup_continuous owner)

/-- **Proposition 2.14**, existence on the original nonnegative commodity orthant. -/
theorem proposition_2_14_orthant (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r)
    (hs : StronglySeparable (PartitionPreference owner r))
    (hthree : ThreeNontrivialBlocks (PartitionPreference owner r)) :
    ∃ w : ∀ i, PartitionBlock owner i → ℝ, (∀ i, Continuous (w i)) ∧
      Represents (PartitionAdditiveUtility owner w) r := by
  obtain ⟨w, hwc, hwr⟩ := proposition_2_14_exists (partitionPreference_rational owner hr)
    (partitionPreference_continuous owner hc) hs hthree
  refine ⟨w, hwc, fun x y => ?_⟩
  simpa only [PartitionPreference, partitionUngroup_group, PartitionAdditiveUtility] using
    hwr (PartitionGroup owner x) (PartitionGroup owner y)

/-- **Proposition 2.14**, converse on the original orthant, without continuity assumptions. -/
theorem proposition_2_14_orthant_additive (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    {w : ∀ i, PartitionBlock owner i → ℝ}
    (hw : Represents (PartitionAdditiveUtility owner w) r) :
    StronglySeparable (PartitionPreference owner r) := by
  apply proposition_2_14_additive (w := w)
  intro x y
  simpa only [PartitionPreference, PartitionAdditiveUtility, partitionGroup_ungroup] using
    hw (PartitionUngroup owner x) (PartitionUngroup owner y)

/-- The full additive characterization for a partition of the original commodity orthant. -/
theorem proposition_2_14_orthant_iff (owner : Fin k → Fin n)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hr : Rational r) (hc : ContinuousPreference r)
    (hthree : ThreeNontrivialBlocks (PartitionPreference owner r)) :
    StronglySeparable (PartitionPreference owner r) ↔
      ∃ w : ∀ i, PartitionBlock owner i → ℝ, (∀ i, Continuous (w i)) ∧
        Represents (PartitionAdditiveUtility owner w) r := by
  constructor
  · intro hs
    exact proposition_2_14_orthant owner hr hc hs hthree
  · rintro ⟨_, _, hw⟩
    exact proposition_2_14_orthant_additive owner hw

end Kreps.PreferenceProperties
