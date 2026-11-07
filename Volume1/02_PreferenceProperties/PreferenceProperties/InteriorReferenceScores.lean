/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.IntervalScoreRepresentation
import PreferenceProperties.StrongSeparabilityTopology

/-!
# Interior reference scores

Preparation for Kreps I, Proposition 2.14. The reference bundle can be chosen
so that every nontrivial block has both strictly better and strictly worse
alternatives. Consequently its common baseline utility lies in the interior
of each nontrivial block's real score interval.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- A connected nontrivial block has an intermediate rank at every fixed surrounding bundle. -/
theorem nontrivialBlock_interior_rank_at (hr : Rational r) (hc : ContinuousPreference r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I) [PreconnectedSpace (B i)]
    (hnt : NontrivialBlock r i) :
    ∃ a lo hi, Strict r (Function.update z i a) (Function.update z i lo) ∧
      Strict r (Function.update z i hi) (Function.update z i a) := by
  let : Nonempty (∀ i, B i) := ⟨z⟩
  obtain ⟨hi, lo, hh⟩ := (nontrivialBlock_iff_every_context hs i).mp hnt
  let f : B i → ∀ j, B j := fun a => Function.update z i a
  have hfc : Continuous f := continuous_const.update i continuous_id
  obtain ⟨a, hhia, halo⟩ := exists_strict_between (rational_preference_pullback hr f)
    (continuousPreference_pullback hc hfc) (hh z)
  exact ⟨a, lo, hi, halo, hhia⟩

/-- One reference bundle simultaneously puts all nontrivial blocks at interior preference ranks. -/
theorem exists_interior_reference [∀ i, PreconnectedSpace (B i)]
    (hr : Rational r) (hc : ContinuousPreference r) (hs : StronglySeparable r)
    (z : ∀ i, B i) :
    ∃ t : ∀ i, B i, ∀ i, NontrivialBlock r i →
      ∃ lo hi, Strict r t (Function.update t i lo) ∧
        Strict r (Function.update t i hi) t := by
  classical
  have hp (i : I) : ∃ a : B i, NontrivialBlock r i →
      ∃ lo hi, Strict r (Function.update z i a) (Function.update z i lo) ∧
        Strict r (Function.update z i hi) (Function.update z i a) := by
    by_cases hnt : NontrivialBlock r i
    · obtain ⟨a, lo, hi, hlo, hhi⟩ := nontrivialBlock_interior_rank_at hr hc hs z i hnt
      exact ⟨a, fun _ => ⟨lo, hi, hlo, hhi⟩⟩
    · exact ⟨z i, fun h => (hnt h).elim⟩
  choose t ht using hp
  refine ⟨t, fun i hnt => ?_⟩
  obtain ⟨lo, hi, hlo, hhi⟩ := ht i hnt
  have hl := (weaklySeparable_strict (stronglySeparable_weakly hs)
    i (t i) lo (z, ()) (t, ())).mp hlo
  have hh := (weaklySeparable_strict (stronglySeparable_weakly hs)
    i hi (t i) (z, ()) (t, ())).mp hhi
  exact ⟨lo, hi, by simpa only [Strict, ReplaceBlock, Function.update_eq_self] using hl,
    by simpa only [Strict, ReplaceBlock, Function.update_eq_self] using hh⟩

/-- Interior ordinal rank is interior membership in the baseline score interval. -/
theorem baselineScores_reference_interior {u : (∀ i, B i) → ℝ} (hu : Represents u r)
    (hc : Continuous u) (z : ∀ i, B i) (i : I) [PreconnectedSpace (B i)]
    (hi : ∃ lo hi, Strict r z (Function.update z i lo) ∧
      Strict r (Function.update z i hi) z) :
    u z ∈ interior (Set.range (BaselineScores u z i)) := by
  obtain ⟨lo, hi, hlo, hhi⟩ := hi
  have hl : BaselineScores u z i lo < u z := (strict_iff_utility_lt hu _ _).mp hlo
  have hh : u z < BaselineScores u z i hi := (strict_iff_utility_lt hu _ _).mp hhi
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds hl hh)
  intro v hv
  exact (baselineScores_ordConnected hc z i).out ⟨lo, rfl⟩ ⟨hi, rfl⟩
    ⟨hv.1.le, hv.2.le⟩

/-- All nontrivial score intervals can share the same interior reference utility. -/
theorem exists_interior_baseline_scores [∀ i, PreconnectedSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) :
    ∃ t : ∀ i, B i, ∀ i, NontrivialBlock r i →
      u t ∈ interior (Set.range (BaselineScores u t i)) := by
  obtain ⟨t, ht⟩ := exists_interior_reference hr (proposition_2_9_forward hu hc) hs z
  exact ⟨t, fun i hi => baselineScores_reference_interior hu hc t i (ht i hi)⟩

end Kreps.PreferenceProperties
