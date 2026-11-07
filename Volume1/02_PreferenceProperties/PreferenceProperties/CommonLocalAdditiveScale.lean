/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.SmallPairInterval
import PreferenceProperties.LocalPairAdditiveScale

/-!
# Local additive scales from the original preference assumptions

The common-score restriction, attainable compact pair domain and explicit
bisymmetric cardinal construction combine to give a continuous additive scale
for local pair comparisons. No cancellation or representation premise is added.
-/

namespace Kreps.PreferenceProperties

/-- A normalized continuous additive scale on a compact interval around the reference score. -/
def HasLocalCommonPairScale {J : Set ℝ} (v : J × J × J → ℝ) (e : J) : Prop :=
  ∃ (a b : ℝ) (hab : a < b) (hsub : Set.Icc a b ⊆ J) (φ : Set.Icc a b → ℝ),
    a < e.val ∧ e.val < b ∧ Continuous φ ∧ StrictMono φ ∧
      φ ⟨a, le_rfl, hab.le⟩ = 0 ∧ φ ⟨b, hab.le, le_rfl⟩ = 1 ∧
      ∀ x y z w : Set.Icc a b,
        v (Set.inclusion hsub x, Set.inclusion hsub y, e) ≤
          v (Set.inclusion hsub z, Set.inclusion hsub w, e) ↔
          φ x + φ y ≤ φ z + φ w

/-- Normalized continuous independent factors have an actual local additive pair scale. -/
theorem normalizedThreeAxes_local_pair_scale {J : Set ℝ} (hJ : IsOpen J)
    {v : J × J × J → ℝ} (hc : Continuous v) {e : J}
    (hi : ThreeFactorIndependent (UtilityPref v)) (hn : NormalizedThreeAxes v Subtype.val e)
    (hleft : ∀ y, StrictMono (fun x => v (x, y, e)))
    (hright : ∀ x, StrictMono (fun y => v (x, y, e))) :
    HasLocalCommonPairScale v e := by
  obtain ⟨a, b, hae, heb, hsub, hsmall⟩ := normalizedThreeAxes_small_pair_interval hJ hc hn
  have hab : a < b := hae.trans heb
  let : PreconnectedSpace (Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let lo : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let up : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let k : Set.Icc a b → J := Set.inclusion hsub
  have hk : StrictMono k := fun _ _ h => h
  have hl : ∀ y, StrictMono (fun x => v (k x, k y, e)) :=
    fun y => (hleft (k y)).comp hk
  have hr : ∀ x, StrictMono (fun y => v (k x, k y, e)) :=
    fun x => (hright (k x)).comp hk
  have hkc : Continuous k := continuous_inclusion hsub
  have hpc : Continuous (fun p : Set.Icc a b × Set.Icc a b => v (k p.1, k p.2, e)) :=
    hc.comp ((hkc.comp continuous_fst).prodMk
      ((hkc.comp continuous_snd).prodMk continuous_const))
  have hdiag : StrictMono (fun p : J => v (p, p, e)) := by
    intro x y hxy
    exact (hleft x hxy).trans (hright y hxy)
  have hpair : ∀ x y, ∃ p : J, v (k x, k y, e) = p.val := by
    intro x y
    exact ⟨⟨v (k x, k y, e), hsmall (k x) (k y) x.property y.property⟩, rfl⟩
  obtain ⟨φ, hφc, hφm, hφlo, hφup, hφpair⟩ :=
    exists_pair_additive_scale_of_partialMedial (fun x y => v (x, y, e)) Subtype.val k
      (lo := lo) (hi := up) hab (fun x => x.property.1) (fun x => x.property.2)
      hl hr hpc (fun x y => normalized_threeFactor_pair_symmetric hi hn (k x) (k y))
      hpair (normalized_threeFactor_partialMedial hi hn) hdiag.injective
  exact ⟨a, b, hab, hsub, φ, hae, heb, hφc, hφm, hφlo, hφup, hφpair⟩

variable {I : Type*} [DecidableEq I] [Finite I] {B : I → Type*}
variable [∀ i, TopologicalSpace (B i)] [∀ i, PreconnectedSpace (B i)]
variable {r : (∀ i, B i) → (∀ i, B i) → Prop} {u : (∀ i, B i) → ℝ}

/-- The original preference assumptions imply a common local additive pair representation. -/
theorem exists_common_local_pair_scale (hr : Rational r) (hu : Represents u r)
    (hs : StronglySeparable r) (hc : Continuous u) (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : NontrivialBlock r i) (hj : NontrivialBlock r j) (hl : NontrivialBlock r l) :
    ∃ (t : ∀ i, B i) (L R : ℝ)
      (hsi : Set.Ioo L R ⊆ Set.range (BaselineScores u t i))
      (hsj : Set.Ioo L R ⊆ Set.range (BaselineScores u t j))
      (hsl : Set.Ioo L R ⊆ Set.range (BaselineScores u t l)) (e : Set.Ioo L R),
      e.val = u t ∧ HasLocalCommonPairScale
        (CommonThreeScoreUtility (ScoreAggregator u t) (BlockScores (BaselineScores u t) t)
          i j l hsi hsj hsl) e := by
  obtain ⟨t, L, R, he, hsi, hsj, hsl⟩ :=
    exists_common_baseline_score_interval hr hu hs hc z i j l hi hj hl
  let e : Set.Ioo L R := ⟨u t, he⟩
  let q := BlockScores (BaselineScores u t) t
  refine ⟨t, L, R, hsi, hsj, hsl, e, rfl, ?_⟩
  apply normalizedThreeAxes_local_pair_scale isOpen_Ioo
    (commonThreeScoreUtility_continuous (scoreAggregator_continuous hu hs hc t)
      q i j l hsi hsj hsl)
    (commonThreeScoreUtility_independent (scoreAggregator_stronglySeparable hu hs t)
      q hij hil hjl hsi hsj hsl)
    (scoreAggregator_commonThree_axes hu hs t hij hil hjl hsi hsj hsl e rfl)
  · intro y
    exact commonThreeScoreUtility_first_strictMono (scoreAggregator_strictMono hu hs t)
      q hij hil hsi hsj hsl y e
  · intro x
    exact commonThreeScoreUtility_second_strictMono (scoreAggregator_strictMono hu hs t)
      q hjl hsi hsj hsl x e

end Kreps.PreferenceProperties
