/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveChartPairCompatibility
import PreferenceProperties.PairwiseAdditiveRepresentation

/-!
# From reference pair comparisons to the full additive representation

Strong separability transports pair indifferences from one reference bundle to
every surrounding context. The finite pair-transfer argument then represents
the entire preference by the sum of those same coordinate scales.
-/

namespace Kreps.PreferenceProperties

/-- Reference pair comparisons in continuous increasing scales determine full additive utility. -/
theorem represents_additive_of_reference_pair_comparisons
    {I : Type*} [DecidableEq I] [Fintype I] {B : I → Type*}
    [∀ i, LinearOrder (B i)] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (z : ∀ i, B i)
    (w : ∀ i, B i → ℝ) (hwc : ∀ i, Continuous (w i)) (hwm : ∀ i, StrictMono (w i))
    (hp : ∀ i j, i ≠ j → ∀ (a a' : B i) (b b' : B j),
      V (Function.update (Function.update z i a) j b) ≤
          V (Function.update (Function.update z i a') j b') ↔
        w i a + w j b ≤ w i a' + w j b') :
    Represents (AdditiveUtility w) (UtilityPref V) := by
  apply represents_additive_of_pair_scale_invariance hm w hwc hwm
  intro x i j a b hij he
  have hpair : V (Function.update (Function.update z i a) j b) =
      V (Function.update (Function.update z i (x i)) j (x j)) :=
    le_antisymm ((hp i j hij a (x i) b (x j)).mpr he.le)
      ((hp i j hij (x i) a (x j) b).mpr he.ge)
  have hcontext := (stronglySeparable_pair_equality_iff hs z x hij a (x i) b (x j)).mp hpair
  simpa only [Function.update_eq_self] using hcontext

end Kreps.PreferenceProperties
