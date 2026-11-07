/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AffineIntervalLocal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Positive affine atlases on real intervals

A local increasing coordinate system with positive affine transition maps can be continued
uniquely from any seed chart. This supplies the one-dimensional gluing step for additive utility
scales in Proposition 2.14. Compatibility is a hypothesis on every chart overlap; synchronizing
the scales of distinct economic coordinates is a separate obligation.
-/

namespace Kreps.PreferenceProperties

open Set

/-- An interval cover with increasing coordinates and positive affine changes of coordinate. -/
structure PositiveAffineIntervalAtlas (ι : Type*) (S : Set ℝ) where
  /-- The open domain of each chart. -/
  domain : ι → Set ℝ
  /-- Chart values, with values outside the chart domain immaterial. -/
  coord : ι → ℝ → ℝ
  /-- Chart domains are open in the real line. -/
  isOpen : ∀ i, IsOpen (domain i)
  /-- Chart domains are intervals. -/
  interval : ∀ i, (domain i).OrdConnected
  /-- Every chart stays in the underlying interval. -/
  subset : ∀ i, domain i ⊆ S
  /-- The charts cover the underlying interval. -/
  cover : ∀ x ∈ S, ∃ i, x ∈ domain i
  /-- Each coordinate is continuous on its domain. -/
  continuous : ∀ i, ContinuousOn (coord i) (domain i)
  /-- Each coordinate preserves orientation. -/
  increasing : ∀ i, StrictMonoOn (coord i) (domain i)
  /-- Changes of coordinate are positive affine on every overlap. -/
  transition : ∀ i j, ∃ A B : ℝ, 0 < A ∧
    ∀ x ∈ domain i ∩ domain j, coord i x = A * coord j x + B

/-- A coordinate is locally compatible with all the charts that meet its domain. -/
def PositiveAffineIntervalAtlas.Compatible {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ i, LocallyPositiveAffineOn f (a.coord i) (D ∩ a.domain i)

variable {ι : Type*} {S : Set ℝ}

/-- A continuation of a seed chart to a larger open interval. -/
structure AffineIntervalSection (a : PositiveAffineIntervalAtlas ι S) (seed : ι) where
  /-- The interval on which this continuation is defined. -/
  domain : Set ℝ
  /-- The continuation domain is open. -/
  isOpen : IsOpen domain
  /-- The continuation domain is an interval. -/
  interval : domain.OrdConnected
  /-- The continuation stays in the underlying interval. -/
  subset : domain ⊆ S
  /-- The continued coordinate. -/
  value : ℝ → ℝ
  /-- Continuation preserves continuity. -/
  continuous : ContinuousOn value domain
  /-- Continuation preserves strict increase. -/
  increasing : StrictMonoOn value domain
  /-- The continuation respects the given local coordinate system. -/
  compatible : a.Compatible value domain
  /-- The seed chart remains inside the continuation domain. -/
  seed_subset : a.domain seed ⊆ domain
  /-- The scale agrees with the prescribed normalization on the seed chart. -/
  seed_eq : ∀ x ∈ a.domain seed, value x = a.coord seed x

/-- Every chart is compatible with the atlas. -/
theorem PositiveAffineIntervalAtlas.compatible_chart {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (i : ι) : a.Compatible (a.coord i) (a.domain i) := by
  intro j
  obtain ⟨A, B, hA, he⟩ := a.transition i j
  exact locallyPositiveAffineOn_of_affine ((a.isOpen i).inter (a.isOpen j)) hA he

/-- The seed chart itself is a continuation with the prescribed normalization. -/
def PositiveAffineIntervalAtlas.seedSection {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (seed : ι) : AffineIntervalSection a seed where
  domain := a.domain seed
  isOpen := a.isOpen seed
  interval := a.interval seed
  subset := a.subset seed
  value := a.coord seed
  continuous := a.continuous seed
  increasing := a.increasing seed
  compatible := a.compatible_chart seed
  seed_subset := Subset.rfl
  seed_eq := fun _ _ => rfl

/-- Compatibility gives a single affine relation on each nonempty connected chart overlap. -/
theorem PositiveAffineIntervalAtlas.Compatible.affine {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ} (h : a.Compatible f D)
    (hD : D.OrdConnected) (i : ι) :
    ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ D ∩ a.domain i, f x = A * a.coord i x + B := by
  by_cases hne : (D ∩ a.domain i).Nonempty
  · exact locallyPositiveAffineOn_global (hD.inter (a.interval i)).isPreconnected hne
      ((a.increasing i).mono inter_subset_right) (h i)
  · exact ⟨1, 0, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Two compatible coordinates are locally positive affine functions of one another. -/
theorem PositiveAffineIntervalAtlas.Compatible.local_relation {ι : Type*} {S D E : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f g : ℝ → ℝ}
    (hf : a.Compatible f D) (hg : a.Compatible g E) (hDS : D ⊆ S) :
    LocallyPositiveAffineOn f g (D ∩ E) := by
  intro x hx
  obtain ⟨i, hxi⟩ := a.cover x (hDS hx.1)
  obtain ⟨U, hU, hxU, hUD, A, B, hA, heF⟩ := hf i x ⟨hx.1, hxi⟩
  obtain ⟨V, hV, hxV, hVE, C, F, hC, heG⟩ := hg i x ⟨hx.2, hxi⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    fun _ hz => ⟨(hUD hz.1).1, (hVE hz.2).1⟩,
    A / C, B - A / C * F, div_pos hA hC, ?_⟩
  intro y hy
  rw [heF y hy.1, heG y hy.2]
  field_simp
  nlinarith [ne_of_gt hC]

/-- Seed-normalized continuations agree on their entire overlap. -/
theorem AffineIntervalSection.unique {ι : Type*} {S : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {seed : ι}
    (hne : (a.domain seed).Nonempty) (p q : AffineIntervalSection a seed) :
    EqOn p.value q.value (p.domain ∩ q.domain) := by
  obtain ⟨x, hx⟩ := hne
  have hdom : (p.domain ∩ q.domain).Nonempty := ⟨x, p.seed_subset hx, q.seed_subset hx⟩
  obtain ⟨A, B, _, he⟩ := locallyPositiveAffineOn_global
    (p.interval.inter q.interval).isPreconnected hdom
    (q.increasing.mono inter_subset_right)
    (p.compatible.local_relation q.compatible p.subset)
  have hcoeff := affine_coefficients_unique (q.increasing.mono q.seed_subset)
    (a.isOpen seed) ⟨x, hx⟩ Subset.rfl
    (A := A) (B := B) (C := 1) (D := 0) (fun y hy => by
      have hey := he y ⟨p.seed_subset hy, q.seed_subset hy⟩
      rw [p.seed_eq y hy, ← q.seed_eq y hy] at hey
      simpa only [one_mul, add_zero] using hey.symm)
  intro y hy
  simpa only [hcoeff.1, hcoeff.2, one_mul, add_zero] using he y hy

end Kreps.PreferenceProperties
