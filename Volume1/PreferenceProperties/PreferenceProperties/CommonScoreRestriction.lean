/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.InteriorReferenceScores
import PreferenceProperties.NormalizedThreeFactorUtility

/-!
# Restriction to three common scalar-score axes

A common subset of three score ranges defines a scalar three-factor utility.
The restriction inherits independence, continuity and strict coordinate
monotonicity. Baseline normalization gives the same numerical scale on all axes.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- The scalar aggregator restricted to three axes with a common score domain. -/
def CommonThreeScoreUtility (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) (i j l : I)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (p : J × J × J) : ℝ :=
  V (ThreeCoordinateBundle z i j l (Set.inclusion hi p.1)
    (Set.inclusion hj p.2.1) (Set.inclusion hl p.2.2))

/-- Three-factor independence is preserved by restricting each factor through a map. -/
theorem threeFactorIndependent_pullback {A B C D E F : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hr : ThreeFactorIndependent r)
    (f : D → A) (g : E → B) (h : F → C) :
    ThreeFactorIndependent (fun p q : D × E × F =>
      r (f p.1, g p.2.1, h p.2.2) (f q.1, g q.2.1, h q.2.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a a' b b' c c'
    exact hr.1 (f a) (f a') (g b) (g b') (h c) (h c')
  · intro b b' a a' c c'
    exact hr.2.1 (g b) (g b') (f a) (f a') (h c) (h c')
  · intro c c' a a' b b'
    exact hr.2.2 (h c) (h c') (f a) (f a') (g b) (g b')

/-- A common score restriction inherits three-factor independence. -/
theorem commonThreeScoreUtility_independent [Finite I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, S i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) :
    ThreeFactorIndependent (UtilityPref (CommonThreeScoreUtility V z i j l hi hj hl)) :=
  threeFactorIndependent_pullback (stronglySeparable_threeFactor hs z hij hil hjl)
    (Set.inclusion hi) (Set.inclusion hj) (Set.inclusion hl)

/-- Restricting a continuous scalar aggregator to the three common axes is continuous. -/
theorem commonThreeScoreUtility_continuous {V : (∀ i, S i) → ℝ} (hc : Continuous V)
    (z : ∀ i, S i) (i j l : I) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) :
    Continuous (CommonThreeScoreUtility V z i j l hi hj hl) :=
  hc.comp ((threeCoordinateBundle_continuous z i j l).comp
    ((continuous_inclusion hi).prodMap
      ((continuous_inclusion hj).prodMap (continuous_inclusion hl))))

/-- The first restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_first_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) {i j l : I} (hij : i ≠ j) (hil : i ≠ l)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (b c : J) :
    StrictMono (fun a : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  have hx := threeCoordinateBundle_update_first z hij hil
    (Set.inclusion hi x) (Set.inclusion hi x) (Set.inclusion hj b) (Set.inclusion hl c)
  have hy := threeCoordinateBundle_update_first z hij hil
    (Set.inclusion hi x) (Set.inclusion hi y) (Set.inclusion hj b) (Set.inclusion hl c)
  rw [← hx, ← hy]
  exact Function.update_strictMono hxy

/-- The second restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_second_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) {i j l : I} (hjl : j ≠ l)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (a c : J) :
    StrictMono (fun b : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  have hx := threeCoordinateBundle_update_second z hjl
    (Set.inclusion hi a) (Set.inclusion hj x) (Set.inclusion hj x) (Set.inclusion hl c)
  have hy := threeCoordinateBundle_update_second z hjl
    (Set.inclusion hi a) (Set.inclusion hj x) (Set.inclusion hj y) (Set.inclusion hl c)
  rw [← hx, ← hy]
  exact Function.update_strictMono hxy

/-- The third restricted coordinate remains strictly increasing. -/
theorem commonThreeScoreUtility_third_strictMono {V : (∀ i, S i) → ℝ}
    (hm : StrictMono V) (z : ∀ i, S i) (i j l : I)
    {J : Set ℝ} (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (a b : J) :
    StrictMono (fun c : J => CommonThreeScoreUtility V z i j l hi hj hl (a, b, c)) := by
  intro x y hxy
  apply hm
  exact Function.update_strictMono hxy

/-- A reference-normalized aggregator has the same numerical scale on all common axes. -/
theorem commonThreeScoreUtility_axes {V : (∀ i, S i) → ℝ} (z : ∀ i, S i)
    (hv : ∀ k (q : S k), V (Function.update z k q) = q.val) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {J : Set ℝ}
    (hi : J ⊆ S i) (hj : J ⊆ S j) (hl : J ⊆ S l) (e : J)
    (he : ∀ k, (z k).val = e.val) :
    NormalizedThreeAxes (CommonThreeScoreUtility V z i j l hi hj hl) Subtype.val e := by
  have hei : Set.inclusion hi e = z i := Subtype.ext (he i).symm
  have hej : Set.inclusion hj e = z j := Subtype.ext (he j).symm
  have hel : Set.inclusion hl e = z l := Subtype.ext (he l).symm
  refine ⟨?_, ?_, ?_⟩
  · intro a
    unfold CommonThreeScoreUtility
    rw [hej, hel]
    have h := threeCoordinateBundle_update_first z hij hil (z i)
      (Set.inclusion hi a) (z j) (z l)
    simp only [ThreeCoordinateBundle, Function.update_eq_self] at h ⊢
    rw [← h, hv]
  · intro a
    unfold CommonThreeScoreUtility
    rw [hei, hel]
    have h := threeCoordinateBundle_update_second z hjl (z i) (z j)
      (Set.inclusion hj a) (z l)
    simp only [ThreeCoordinateBundle, Function.update_eq_self] at h ⊢
    rw [← h, hv]
  · intro a
    unfold CommonThreeScoreUtility
    rw [hei, hej]
    simp only [ThreeCoordinateBundle, Function.update_eq_self, hv]

end Kreps.PreferenceProperties
