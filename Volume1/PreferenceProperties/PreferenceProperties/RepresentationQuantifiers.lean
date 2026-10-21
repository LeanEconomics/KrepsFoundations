/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.Monotonicity
import PreferenceProperties.ConcaveUtility
import PreferenceProperties.GeneralContinuousRepresentation
import PreferenceProperties.WeakSeparability
import PreferenceProperties.AdditiveSeparability
import PreferenceProperties.QuasiLinear
import PreferenceProperties.SignedHomotheticRepresentation

/-!
# Quantifiers over utility representations

Kreps I, Problem 2.1 and Table 2.1, p. 45. The ordinal rows have an `all`
forward implication and a `some` converse. Existence of a representation is
explicit when interpreting an `all` statement as an equivalence, preventing
vacuous conclusions for unrepresentable preferences. Continuity, quasi-linearity,
and continuous degree-one homogeneity instead admit the indicated `some` forms.
The strict-convex-to-strict-concave box excluded by the book is not asserted.
The additive-existence direction remains the separate Proposition 2.14 obligation.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : X → X → Prop}

/-- `All` in the representation columns of Table 2.1. -/
def EveryRepresentation (r : X → X → Prop) (P : (X → ℝ) → Prop) : Prop :=
  ∀ u, Represents u r → P u

/-- `Some` in the representation columns of Table 2.1. -/
def SomeRepresentation (r : X → X → Prop) (P : (X → ℝ) → Prop) : Prop :=
  ∃ u, Represents u r ∧ P u

/-- An ordinal property gives both quantifiers once at least one representation exists. -/
theorem representation_quantifiers_of_invariance {P : Prop} {Q : (X → ℝ) → Prop}
    (hex : ∃ u, Represents u r) (hQ : ∀ u, Represents u r → (P ↔ Q u)) :
    (P ↔ EveryRepresentation r Q) ∧ (P ↔ SomeRepresentation r Q) := by
  obtain ⟨u₀, hu₀⟩ := hex
  constructor
  · exact ⟨fun hp u hu => (hQ u hu).mp hp, fun hall => (hQ u₀ hu₀).mpr (hall u₀ hu₀)⟩
  · constructor
    · intro hp
      exact ⟨u₀, hu₀, (hQ u₀ hu₀).mp hp⟩
    · rintro ⟨u, hu, hqu⟩
      exact (hQ u hu).mpr hqu

/-- Table 2.1, monotonicity: `all` forward and `some` backward. -/
theorem table_monotone [PartialOrder X] (hex : ∃ u, Represents u r) :
    (MonotonePreference r ↔ EveryRepresentation r Monotone) ∧
      (MonotonePreference r ↔ SomeRepresentation r Monotone) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_2_monotone hu)

/-- Table 2.1, strict monotonicity: `all` forward and `some` backward. -/
theorem table_strictlyMonotone [PartialOrder X] (hex : ∃ u, Represents u r) :
    (StrictlyMonotonePreference r ↔ EveryRepresentation r StrictMono) ∧
      (StrictlyMonotonePreference r ↔ SomeRepresentation r StrictMono) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_2_strict hu)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- Table 2.1, convexity and quasi-concavity: `all` forward and `some` backward. -/
theorem table_quasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (ConvexPreference hS r ↔ EveryRepresentation r (QuasiConcaveUtility hS)) ∧
      (ConvexPreference hS r ↔ SomeRepresentation r (QuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex (fun _ hu => (proposition_2_8b_quasi hu).symm)

/-- Table 2.1, semi-strict convexity: `all` forward and `some` backward. -/
theorem table_semiStrictlyQuasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (SemiStrictlyConvexPreference hS r ↔
      EveryRepresentation r (SemiStrictlyQuasiConcaveUtility hS)) ∧
      (SemiStrictlyConvexPreference hS r ↔
        SomeRepresentation r (SemiStrictlyQuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex
    (fun _ hu => (proposition_2_8b_semiStrict hu).symm)

/-- Table 2.1, strict convexity and strict quasi-concavity: `all` and `some`. -/
theorem table_strictlyQuasiConcave (hS : Convex ℝ S) {r : S → S → Prop}
    (hex : ∃ u, Represents u r) :
    (StrictlyConvexPreference hS r ↔ EveryRepresentation r (StrictlyQuasiConcaveUtility hS)) ∧
      (StrictlyConvexPreference hS r ↔ SomeRepresentation r (StrictlyQuasiConcaveUtility hS)) :=
  representation_quantifiers_of_invariance hex (fun _ hu => (proposition_2_8b_strict hu).symm)

/-- Table 2.1, a `some` concave representation implies convex preference. -/
theorem table_concave_converse (hS : Convex ℝ S) {r : S → S → Prop}
    (h : SomeRepresentation r (ConcaveUtility hS)) : ConvexPreference hS r := by
  obtain ⟨u, hu, hcu⟩ := h
  exact proposition_2_8a_concave hu hcu

/-- Table 2.1, a `some` strictly concave representation implies strict convexity. -/
theorem table_strictlyConcave_converse (hS : Convex ℝ S) {r : S → S → Prop}
    (h : SomeRepresentation r (StrictlyConcaveUtility hS)) : StrictlyConvexPreference hS r := by
  obtain ⟨u, hu, hcu⟩ := h
  exact proposition_2_8a_strict hu hcu

/-- Table 2.1, continuity: `some` in both directions. -/
theorem table_continuous (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ↔ SomeRepresentation r Continuous := proposition_2_9 k hr

/-- Table 2.1, weak separability: the exact given utility has the factorized form. -/
theorem table_weaklySeparable {I : Type*} {B : I → Type*} {L : Type*}
    [DecidableEq I] [Finite I] [Nonempty (BlockBundle B L)]
    {r : BlockBundle B L → BlockBundle B L → Prop} (hex : ∃ u, Represents u r) :
    (WeaklySeparable r ↔ EveryRepresentation r WeakSeparabilityRepresentation) ∧
      (WeaklySeparable r ↔ SomeRepresentation r WeakSeparabilityRepresentation) :=
  representation_quantifiers_of_invariance hex (fun _ hu => proposition_2_12 hu)

/-- Exact additive form of a given utility, as opposed to ordinal additive representability. -/
def AdditiveForm {I : Type*} [Fintype I] {B : I → Type*} (u : (∀ i, B i) → ℝ) : Prop :=
  ∃ w : ∀ i, B i → ℝ, u = AdditiveUtility w

/-- Table 2.1, the `some` additive representation implies strong separability. -/
theorem table_additive_converse {I : Type*} [Fintype I] [DecidableEq I] {B : I → Type*}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} (h : SomeRepresentation r AdditiveForm) :
    StronglySeparable r := by
  obtain ⟨u, hu, w, rfl⟩ := h
  exact proposition_2_14_additive hu

/-- The existential table entry is exactly additive representability. -/
theorem some_additiveForm_iff {I : Type*} [Fintype I] {B : I → Type*}
    {r : (∀ i, B i) → (∀ i, B i) → Prop} :
    SomeRepresentation r AdditiveForm ↔ AdditivelyRepresentable r := by
  constructor
  · rintro ⟨u, hu, w, rfl⟩
    exact ⟨w, hu⟩
  · rintro ⟨w, hw⟩
    exact ⟨AdditiveUtility w, hw, w, rfl⟩

/-- Exact quasi-linear form uses money coefficient one. -/
def QuasiLinearForm (U : X × ℝ≥0 → ℝ) : Prop :=
  ∃ u : X → ℝ, U = QuasiLinearUtility u

/-- The existential quasi-linear table entry is exactly quasi-linearity. -/
theorem some_quasiLinearForm_iff {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop} :
    SomeRepresentation r QuasiLinearForm ↔ QuasiLinear r := by
  constructor
  · rintro ⟨U, hU, u, rfl⟩
    exact ⟨u, hU⟩
  · rintro ⟨u, hu⟩
    exact ⟨QuasiLinearUtility u, hu, u, rfl⟩

/-- Table 2.1, the three money properties and normalized quasi-linearity: `some` both ways. -/
theorem table_quasiLinear [Nonempty X] {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}
    (hr : Rational r) :
    (OwnMoneyOrder r ∧ MoneyTranslation r ∧ MoneyCompensable r) ↔
      SomeRepresentation r QuasiLinearForm :=
  (proposition_2_16 hr).symm.trans some_quasiLinearForm_iff.symm

/-- Table 2.1, continuous homothetic preference: `some` continuous homogeneous utility. -/
theorem table_homogeneous (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    (ContinuousPreference r ∧ HomotheticPreference r) ↔
      SomeRepresentation r (fun u => Continuous u ∧ HomogeneousUtility u) :=
  proposition_2_19 k hr

end Kreps.PreferenceProperties
