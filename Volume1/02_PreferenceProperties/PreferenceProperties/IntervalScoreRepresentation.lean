/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SubutilityContinuity
import PreferenceProperties.FiniteProductContinuity
import PreferenceProperties.AdditiveSeparability

/-!
# Reduction to continuous increasing utility on real intervals

Preparation for Kreps I, Proposition 2.14. The baseline construction turns
connected commodity blocks into real intervals and preserves strong
separability. Its aggregator is jointly continuous and strictly increasing.
Every baseline axis is normalized to the same original utility scale.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}

/-- The utility score of each commodity block at a common reference bundle. -/
def BaselineScores (u : (∀ i, B i) → ℝ) (z : ∀ i, B i) (i : I) (a : B i) : ℝ :=
  BaselineSubutility (fun p : BlockBundle B Unit => u p.1) (z, ()) i a

/-- The exact utility aggregator on the attained real block-score ranges. -/
noncomputable def ScoreAggregator (u : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (q : ∀ i, Set.range (BaselineScores u z i)) : ℝ :=
  SubutilityAggregator (fun p : BlockBundle B Unit => u p.1) (BaselineScores u z) (q, ())

/-- Every block's reference score equals the reference bundle's overall utility. -/
theorem baselineScores_reference (u : (∀ i, B i) → ℝ) (z : ∀ i, B i) (i : I) :
    BaselineScores u z i (z i) = u z := by
  simp only [BaselineScores, BaselineSubutility, ReplaceBlock, Function.update_eq_self]

/-- The baseline block scores are continuous. -/
theorem baselineScores_continuous [∀ i, TopologicalSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hc : Continuous u) (z : ∀ i, B i) (i : I) :
    Continuous (BaselineScores u z i) :=
  baselineSubutility_continuous (hc.comp continuous_fst) (z, ()) i

/-- Each connected commodity block is replaced by a real interval. -/
theorem baselineScores_ordConnected [∀ i, TopologicalSpace (B i)]
    {u : (∀ i, B i) → ℝ} (hc : Continuous u) (z : ∀ i, B i) (i : I)
    [PreconnectedSpace (B i)] : Set.OrdConnected (Set.range (BaselineScores u z i)) :=
  (isPreconnected_range (baselineScores_continuous hc z i)).ordConnected

/-- Strong separability gives an exact factorization through the scalar scores. -/
theorem scoreAggregator_factors [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z x : ∀ i, B i) :
    u x = ScoreAggregator u z (BlockScores (BaselineScores u z) x) :=
  subutilityAggregator_factors (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs)
    (z, ()) (x, ())

/-- The scalar-score aggregator is strictly increasing. -/
theorem scoreAggregator_strictMono [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) : StrictMono (ScoreAggregator u z) :=
  subutilityAggregator_increasing (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs) (z, ()) ()

/-- The scalar-score aggregator is jointly continuous on its finite interval product. -/
theorem scoreAggregator_continuous [Finite I] [∀ i, TopologicalSpace (B i)]
    [∀ i, PreconnectedSpace (B i)] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) :
    Continuous (ScoreAggregator u z) := by
  let : ∀ i, Set.OrdConnected (Set.range (BaselineScores u z i)) :=
    fun i => baselineScores_ordConnected hc z i
  apply finiteProductMonotone_continuous (scoreAggregator_strictMono hu hs z).monotone
  intro q i
  exact subutilityAggregator_coordinate_continuous (fun x y : BlockBundle B Unit => hu x.1 y.1)
    (stronglySeparable_weakly hs) (hc.comp continuous_fst) (z, ()) q () i

/-- Representative selection respects a partition into a set of coordinates and its complement. -/
theorem scoreRepresentatives_piecewise (w : ∀ i, B i → ℝ) (s : Finset I)
    (p q : ∀ i, Set.range (w i)) :
    (fun i => ScoreRepresentative w i (s.piecewise p q i)) =
      s.piecewise (fun i => ScoreRepresentative w i (p i))
        (fun i => ScoreRepresentative w i (q i)) := by
  funext i
  by_cases hi : i ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hi]
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi]

/-- Strong separability survives the reduction to scalar block scores. -/
theorem scoreAggregator_stronglySeparable {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) :
    StronglySeparable (UtilityPref (ScoreAggregator u z)) := by
  intro s a b p q
  unfold UtilityPref ScoreAggregator SubutilityAggregator
  simp only [scoreRepresentatives_piecewise]
  rw [← hu, ← hu]
  exact hs s _ _ _ _

/-- Along any reference axis, the aggregator equals the numerical score on that axis. -/
theorem scoreAggregator_reference_axis [Finite I] {u : (∀ i, B i) → ℝ}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hu : Represents u r)
    (hs : StronglySeparable r) (z : ∀ i, B i) (i : I)
    (t : Set.range (BaselineScores u z i)) :
    ScoreAggregator u z (Function.update (BlockScores (BaselineScores u z) z) i t) = t.val := by
  obtain ⟨a, ha⟩ := t.property
  have ht : (⟨BaselineScores u z i a, a, rfl⟩ : Set.range (BaselineScores u z i)) = t :=
    Subtype.ext ha
  have hf := scoreAggregator_factors hu hs z (Function.update z i a)
  rw [blockScores_update, ht] at hf
  exact hf.symm.trans ha

end Kreps.PreferenceProperties
