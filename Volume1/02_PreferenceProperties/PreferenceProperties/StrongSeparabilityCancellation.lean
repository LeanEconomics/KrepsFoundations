/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AdditiveSeparability

/-!
# Strong separability and third-factor cancellation

Preparation for Kreps I, Proposition 2.14. Debreu's 1959 discussion paper,
pp. 12-13, derives the local Thomsen hexagon by compensating in a third block.
The cancellation below is proved from strong separability, not assumed as an axiom.
Connectedness and continuity supply the compensator locally. The cardinal-scale
construction and its global extension culminate in `proposition_2_14_exists`
in `PrimitiveAdditiveExistence`.

Source: https://cowles.yale.edu/sites/default/files/2022-08/d0076.pdf
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*}
  {r : (∀ i, B i) → (∀ i, B i) → Prop}

/-- Independence of the complement of a block allows its common value to be changed. -/
theorem stronglySeparable_complement_iff [Finite I] (hs : StronglySeparable r)
    (i : I) (x y : ∀ i, B i) (a b : B i) :
    r (Function.update x i a) (Function.update y i a) ↔
      r (Function.update x i b) (Function.update y i b) := by
  let : Fintype I := Fintype.ofFinite I
  simpa only [Finset.piecewise_erase_univ, Function.update_self] using
    hs (Finset.univ.erase i) x y (Function.update x i a) (Function.update x i b)

/-- When two bundles have the same block, changing that common block preserves comparison. -/
theorem stronglySeparable_common_update_iff [Finite I] (hs : StronglySeparable r)
    {i : I} {x y : ∀ i, B i} (hxy : x i = y i) (a : B i) :
    r x y ↔ r (Function.update x i a) (Function.update y i a) := by
  have hy : Function.update y i (x i) = y := by
    rw [hxy, Function.update_eq_self]
  simpa only [Function.update_eq_self, hy] using
    stronglySeparable_complement_iff hs i x y (x i) a

/-- A three-coordinate slice through a reference bundle. -/
def ThreeCoordinateBundle (z : ∀ i, B i) (i j l : I)
    (a : B i) (b : B j) (c : B l) : ∀ i, B i :=
  Function.update (Function.update (Function.update z i a) j b) l c

/-- Replacing the first selected coordinate stays in the same three-coordinate slice. -/
theorem threeCoordinateBundle_update_first (z : ∀ i, B i) {i j l : I}
    (hij : i ≠ j) (hil : i ≠ l) (a a' : B i) (b : B j) (c : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) i a' =
      ThreeCoordinateBundle z i j l a' b c := by
  unfold ThreeCoordinateBundle
  rw [Function.update_comm hil.symm, Function.update_comm hij.symm, Function.update_idem]

/-- Replacing the second selected coordinate stays in the same slice. -/
theorem threeCoordinateBundle_update_second (z : ∀ i, B i) {i j l : I}
    (hjl : j ≠ l) (a : B i) (b b' : B j) (c : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) j b' =
      ThreeCoordinateBundle z i j l a b' c := by
  unfold ThreeCoordinateBundle
  rw [Function.update_comm hjl.symm, Function.update_idem]

/-- Replacing the third selected coordinate stays in the same slice. -/
theorem threeCoordinateBundle_update_third (z : ∀ i, B i) (i j l : I)
    (a : B i) (b : B j) (c c' : B l) :
    Function.update (ThreeCoordinateBundle z i j l a b c) l c' =
      ThreeCoordinateBundle z i j l a b c' := by
  simp only [ThreeCoordinateBundle, Function.update_idem]

/-- Independence of each pair of factors from the remaining factor. -/
def ThreeFactorIndependent {A B C : Type*}
    (r : (A × B × C) → (A × B × C) → Prop) : Prop :=
  (∀ a a' b b' c c', r (a, b, c) (a, b', c') ↔ r (a', b, c) (a', b', c')) ∧
  (∀ b b' a a' c c', r (a, b, c) (a', b, c') ↔ r (a, b', c) (a', b', c')) ∧
  (∀ c c' a a' b b', r (a, b, c) (a', b', c) ↔ r (a, b, c') (a', b', c'))

/-- Strong separability supplies all three independence properties on every distinct-block slice. -/
theorem stronglySeparable_threeFactor [Finite I] (hs : StronglySeparable r)
    (z : ∀ i, B i) {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ThreeFactorIndependent (fun p q : B i × B j × B l =>
      r (ThreeCoordinateBundle z i j l p.1 p.2.1 p.2.2)
        (ThreeCoordinateBundle z i j l q.1 q.2.1 q.2.2)) := by
  constructor
  · intro a a' b b' c c'
    have he : ThreeCoordinateBundle z i j l a b c i =
        ThreeCoordinateBundle z i j l a b' c' i := by
      simp [ThreeCoordinateBundle, hij, hil]
    simpa only [threeCoordinateBundle_update_first z hij hil] using
      stronglySeparable_common_update_iff hs he a'
  constructor
  · intro b b' a a' c c'
    have he : ThreeCoordinateBundle z i j l a b c j =
        ThreeCoordinateBundle z i j l a' b c' j := by
      simp [ThreeCoordinateBundle, hjl]
    simpa only [threeCoordinateBundle_update_second z hjl] using
      stronglySeparable_common_update_iff hs he b'
  · intro c c' a a' b b'
    have he : ThreeCoordinateBundle z i j l a b c l =
        ThreeCoordinateBundle z i j l a' b' c l := by
      simp [ThreeCoordinateBundle]
    simpa only [threeCoordinateBundle_update_third] using
      stronglySeparable_common_update_iff hs he c'

/-- Transitivity of weak preference gives transitivity of indifference. -/
theorem indifferent_transitive {X : Type*} {r : X → X → Prop} (ht : TransitivePref r)
    {x y z : X} (hxy : Indifferent r x y) (hyz : Indifferent r y z) : Indifferent r x z :=
  ⟨ht x y z hxy.1 hyz.1, ht z y x hyz.2 hxy.2⟩

/-- The first-factor independence condition transports both directions of indifference. -/
theorem threeFactor_first_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (a a' : A) (b b' : B) (c c' : C) :
    Indifferent r (a, b, c) (a, b', c') ↔ Indifferent r (a', b, c) (a', b', c') :=
  and_congr (hi.1 a a' b b' c c') (hi.1 a a' b' b c' c)

/-- The second-factor independence condition transports indifference. -/
theorem threeFactor_second_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (b b' : B) (a a' : A) (c c' : C) :
    Indifferent r (a, b, c) (a', b, c') ↔ Indifferent r (a, b', c) (a', b', c') :=
  and_congr (hi.2.1 b b' a a' c c') (hi.2.1 b b' a' a c' c)

/-- The third-factor independence condition transports indifference. -/
theorem threeFactor_third_indifferent {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (hi : ThreeFactorIndependent r)
    (c c' : C) (a a' : A) (b b' : B) :
    Indifferent r (a, b, c) (a', b', c) ↔ Indifferent r (a, b, c') (a', b', c') :=
  and_congr (hi.2.2 c c' a a' b b') (hi.2.2 c c' a' a b' b)

/-- Debreu's third-factor hexagon: a compensating third coordinate closes the indifference chain. -/
theorem third_factor_hexagon {A B C : Type*}
    {r : (A × B × C) → (A × B × C) → Prop} (ht : TransitivePref r)
    (hi : ThreeFactorIndependent r) (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B) (c c' : C)
    (hab : Indifferent r (a₂, b₁, c) (a₁, b₂, c))
    (hcd : Indifferent r (a₃, b₁, c) (a₁, b₃, c))
    (hp : Indifferent r (a₁, b₁, c') (a₂, b₁, c)) :
    Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  have hpb := indifferent_transitive ht hp hab
  have hqe := (threeFactor_first_indifferent hi a₁ a₃ b₁ b₂ c' c).mp hpb
  have hrf := (threeFactor_second_indifferent hi b₁ b₃ a₁ a₂ c' c).mp hp
  have hqr := (threeFactor_third_indifferent hi c c' a₃ a₁ b₁ b₃).mp hcd
  exact indifferent_transitive ht ⟨hqe.2, hqe.1⟩ (indifferent_transitive ht hqr hrf)

/-- An interior rank in a connected third factor can compensate every sufficiently nearby pair. -/
theorem third_factor_local_compensation {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (a : A) (b : B) (c cLow cHigh : C)
    (hlo : Strict r (a, b, c) (a, b, cLow)) (hhi : Strict r (a, b, cHigh) (a, b, c)) :
    ∃ U : Set (A × B), IsOpen U ∧ (a, b) ∈ U ∧
      ∀ p ∈ U, ∃ d, Indifferent r (a, b, d) (p.1, p.2, c) := by
  let f : A × B → A × B × C := fun p => (p.1, p.2, c)
  have hf : Continuous f := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let U := f ⁻¹' (StrictlyBetterThan r (a, b, cLow) ∩ StrictlyWorseThan r (a, b, cHigh))
  have ho := continuousPreference_openStrictContours hc
  refine ⟨U, ((ho (a, b, cLow)).1.inter (ho (a, b, cHigh)).2).preimage hf,
    ⟨hlo, hhi⟩, ?_⟩
  intro p hp
  exact indifference_on_connected_image hr hc (fun d => (a, b, d))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (p.1, p.2, c) hp.2.1 hp.1.1

/-- Continuity and the third-factor bracket turn the algebraic hexagon into local cancellation. -/
theorem third_factor_local_hexagon {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [PreconnectedSpace C]
    {r : (A × B × C) → (A × B × C) → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hi : ThreeFactorIndependent r)
    (a₁ : A) (b₁ : B) (c cLow cHigh : C)
    (hlo : Strict r (a₁, b₁, c) (a₁, b₁, cLow))
    (hhi : Strict r (a₁, b₁, cHigh) (a₁, b₁, c)) :
    ∃ U : Set (A × B), IsOpen U ∧ (a₁, b₁) ∈ U ∧
      ∀ a₂ a₃ b₂ b₃, (a₂, b₁) ∈ U →
        Indifferent r (a₂, b₁, c) (a₁, b₂, c) →
        Indifferent r (a₃, b₁, c) (a₁, b₃, c) →
        Indifferent r (a₃, b₂, c) (a₂, b₃, c) := by
  obtain ⟨U, hU, hp, hcomp⟩ := third_factor_local_compensation hr hc a₁ b₁ c cLow cHigh hlo hhi
  refine ⟨U, hU, hp, ?_⟩
  intro a₂ a₃ b₂ b₃ hmem hab hcd
  obtain ⟨c', hc'⟩ := hcomp (a₂, b₁) hmem
  exact third_factor_hexagon hr.2 hi a₁ a₂ a₃ b₁ b₂ b₃ c c' hab hcd hc'

end Kreps.PreferenceProperties
