/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.StrongSeparabilityCancellation
import PreferenceProperties.OrthantRepresentation

/-!
# Topological foundations of the additive construction

Preparation for Kreps I, Proposition 2.14. A nontrivial connected third block
has an interior preference rank. Strong separability then gives local Thomsen
cancellation on a slice through the other two blocks. All hypotheses in this
step are derived from the original preference; no additive representation or
hexagon condition is assumed.
-/

namespace Kreps.PreferenceProperties

/-- Restricting a rational preference through a map preserves rationality. -/
theorem rational_preference_pullback {X Y : Type*} {r : X → X → Prop}
    (hr : Rational r) (f : Y → X) : Rational (fun x y => r (f x) (f y)) :=
  ⟨fun x y => hr.1 (f x) (f y), fun x y z => hr.2 (f x) (f y) (f z)⟩

/-- A continuous parametrization preserves the joint openness of strict preference. -/
theorem continuousPreference_pullback {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {r : X → X → Prop} (hc : ContinuousPreference r) {f : Y → X} (hf : Continuous f) :
    ContinuousPreference (fun x y => r (f x) (f y)) := hc.preimage (hf.prodMap hf)

variable {I : Type*} [DecidableEq I] {B : I → Type*}

/-- Varying three coordinates is a continuous parametrization of the commodity product. -/
theorem threeCoordinateBundle_continuous [∀ i, TopologicalSpace (B i)]
    (z : ∀ i, B i) (i j l : I) :
    Continuous (fun p : B i × B j × B l =>
      ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2) :=
  ((continuous_const.update i continuous_fst).update j continuous_snd.fst).update l
    continuous_snd.snd

/-- Preference restricted to a three-coordinate slice. -/
def ThreeCoordinatePreference (r : (∀ i, B i) → (∀ i, B i) → Prop)
    (z : ∀ i, B i) (i j l : I) (p q : B i × B j × B l) : Prop :=
  r (ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2)
    (ThreeCoordinateBundle z i j l q.1 q.2.1 q.2.2)

/-- Connectedness gives an interior rank between any strict pair in the third factor. -/
theorem third_factor_interior_rank {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (a : A) (b : B) {cLow cHigh : C}
    (hstrict : Strict r (a, b, cHigh) (a, b, cLow)) :
    ∃ c, Strict r (a, b, c) (a, b, cLow) ∧ Strict r (a, b, cHigh) (a, b, c) := by
  have hf : Continuous (fun c : C => (a, b, c)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  obtain ⟨c, hhi, hlo⟩ := exists_strict_between
    (rational_preference_pullback hr (fun c => (a, b, c)))
    (continuousPreference_pullback hc hf) hstrict
  exact ⟨c, hlo, hhi⟩

/-- A nontrivial third factor supplies the interior rank needed for local cancellation. -/
theorem third_factor_local_hexagon_of_nontrivial {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hi : ThreeFactorIndependent r) (a₁ : A) (b₁ : B)
    (hnt : ∃ cHigh cLow, Strict r (a₁, b₁, cHigh) (a₁, b₁, cLow)) :
    ∃ c : C, ∃ U : Set (A × B), IsOpen U ∧ (a₁, b₁) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, b₁) ∈ U →
        Indifferent r (a₂, b₁, c) (a₁, b₂, c) →
        Indifferent r (a₃, b₁, c) (a₁, b₃, c) →
        Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨cHigh, cLow, hstrict⟩ := hnt
  obtain ⟨c, hlo, hhi⟩ := third_factor_interior_rank hr hc a₁ b₁ hstrict
  obtain ⟨U, hU, hp, hhex⟩ := third_factor_local_hexagon hr hc hi a₁ b₁ c cLow cHigh hlo hhi
  exact ⟨c, U, hU, hp, hhex⟩

/-- Strong separability, continuity and a connected nontrivial third block imply a local hexagon. -/
theorem stronglySeparable_local_hexagon [Finite I] [∀ i, TopologicalSpace (B i)]
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StronglySeparable r)
    {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    [PreconnectedSpace (B l)] (hnt : NontrivialBlock r l) :
    ∃ z : ∀ i, B i, ∃ c : B l, ∃ U : Set (B i × B j), IsOpen U ∧ (z i, z j) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, z j) ∈ U →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₂, z j, c) (z i, b₂, c) →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₃, z j, c) (z i, b₃, c) →
        Indifferent (ThreeCoordinatePreference r z i j l) (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨cHigh, cLow, z, hz⟩ := hnt
  have hr' : Rational (ThreeCoordinatePreference r z i j l) :=
    rational_preference_pullback hr _
  have hc' : ContinuousPreference (ThreeCoordinatePreference r z i j l) :=
    continuousPreference_pullback hc (threeCoordinateBundle_continuous z i j l)
  have hi : ThreeFactorIndependent (ThreeCoordinatePreference r z i j l) :=
    stronglySeparable_threeFactor hs z hij hil hjl
  have hnt' : ∃ a b, Strict (ThreeCoordinatePreference r z i j l)
      (z i, z j, a) (z i, z j, b) := by
    refine ⟨cHigh, cLow, ?_⟩
    simpa only [Strict, ThreeCoordinatePreference, ThreeCoordinateBundle,
      Function.update_eq_self] using hz
  obtain ⟨c, U, hU, hp, hhex⟩ :=
    third_factor_local_hexagon_of_nontrivial hr' hc' hi (z i) (z j) hnt'
  exact ⟨z, c, U, hU, hp, hhex⟩

end Kreps.PreferenceProperties
