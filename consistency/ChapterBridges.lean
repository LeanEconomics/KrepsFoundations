/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility
import PreferenceProperties
import ConsumerDemand
import RevealedPreference

/-!
# Compatibility of the four independent chapter libraries

These checks use the actual public chapter definitions and results. Equalities
detect changes to copied economic conventions; the final constructions compose
Chapter 4's Afriat utility with Chapter 2's concavity bridge and Chapter 3's
consumer maximum theorem. The independent Lake packages remain unchanged.

The repository consistency checker jointly elaborates the chapter sources and
these checks, replacing only these root imports with their actual source bodies.
This is an integration audit, not an additional economic chapter.
-/

namespace Kreps.Compatibility

open scoped NNReal

variable {X : Type*}

/-- Completeness retains its quantifiers throughout all four chapters. -/
theorem complete_agrees (r : X → X → Prop) :
    ChoicePreferenceUtility.Complete r = PreferenceProperties.Complete r ∧
      PreferenceProperties.Complete r = ConsumerDemand.Complete r ∧
      ConsumerDemand.Complete r = RevealedPreference.Complete r := ⟨rfl, rfl, rfl⟩

/-- Transitivity retains its argument orientation throughout all four chapters. -/
theorem transitive_agrees (r : X → X → Prop) :
    ChoicePreferenceUtility.TransitivePref r = PreferenceProperties.TransitivePref r ∧
      PreferenceProperties.TransitivePref r = ConsumerDemand.TransitivePref r ∧
      ConsumerDemand.TransitivePref r = RevealedPreference.TransitivePref r := ⟨rfl, rfl, rfl⟩

/-- Rationality is the same complete-and-transitive condition in each chapter. -/
theorem rational_agrees (r : X → X → Prop) :
    ChoicePreferenceUtility.Rational r = PreferenceProperties.Rational r ∧
      PreferenceProperties.Rational r = ConsumerDemand.Rational r ∧
      ConsumerDemand.Rational r = RevealedPreference.Rational r := ⟨rfl, rfl, rfl⟩

/-- Strict preference always means weak preference without its reverse. -/
theorem strict_agrees (r : X → X → Prop) :
    ChoicePreferenceUtility.Strict r = PreferenceProperties.Strict r ∧
      PreferenceProperties.Strict r = ConsumerDemand.Strict r ∧
      ConsumerDemand.Strict r = RevealedPreference.Strict r := ⟨rfl, rfl, rfl⟩

/-- Indifference has the same two-direction definition in all four namespaces. -/
theorem indifferent_agrees (r : X → X → Prop) :
    ChoicePreferenceUtility.Indifferent r = PreferenceProperties.Indifferent r ∧
      PreferenceProperties.Indifferent r = ConsumerDemand.Indifferent r ∧
      ConsumerDemand.Indifferent r = RevealedPreference.Indifferent r := ⟨rfl, rfl, rfl⟩

/-- Maximizing a preference returns the same full choice set in every chapter. -/
theorem preferenceChoice_agrees (r : X → X → Prop) (A : Set X) :
    ChoicePreferenceUtility.PrefChoice r A = PreferenceProperties.PrefChoice r A ∧
      PreferenceProperties.PrefChoice r A = ConsumerDemand.PrefChoice r A ∧
      ConsumerDemand.PrefChoice r A = RevealedPreference.PrefChoice r A := ⟨rfl, rfl, rfl⟩

/-- Higher numerical utility is consistently oriented as the preferred alternative. -/
theorem utilityPreference_agrees (u : X → ℝ) :
    ChoicePreferenceUtility.UtilityPref u = PreferenceProperties.UtilityPref u ∧
      PreferenceProperties.UtilityPref u = ConsumerDemand.UtilityPref u ∧
      ConsumerDemand.UtilityPref u = RevealedPreference.UtilityPref u := ⟨rfl, rfl, rfl⟩

/-- Representation preserves all and only weak comparisons in each chapter. -/
theorem represents_agrees (u : X → ℝ) (r : X → X → Prop) :
    ChoicePreferenceUtility.Represents u r = PreferenceProperties.Represents u r ∧
      PreferenceProperties.Represents u r = ConsumerDemand.Represents u r ∧
      ConsumerDemand.Represents u r = RevealedPreference.Represents u r := ⟨rfl, rfl, rfl⟩

/-- The commodity type includes exactly the same boundary bundles in all four chapters. -/
theorem orthant_agrees (k : ℕ) :
    ChoicePreferenceUtility.NonnegativeOrthant k = PreferenceProperties.NonnegativeOrthant k ∧
      PreferenceProperties.NonnegativeOrthant k = ConsumerDemand.NonnegativeOrthant k ∧
      ConsumerDemand.NonnegativeOrthant k = RevealedPreference.NonnegativeOrthant k :=
  ⟨rfl, rfl, rfl⟩

/-- Local insatiability uses the same metric and closed-radius convention. -/
theorem localInsatiability_agrees [PseudoMetricSpace X] (r : X → X → Prop) :
    PreferenceProperties.LocallyInsatiable r = ConsumerDemand.LocallyInsatiable r ∧
      ConsumerDemand.LocallyInsatiable r = RevealedPreference.LocallyInsatiable r := ⟨rfl, rfl⟩

/-- Preference continuity uses the same strict-comparison graph. -/
theorem preferenceContinuity_agrees [TopologicalSpace X] (r : X → X → Prop) :
    PreferenceProperties.ContinuousPreference r = ConsumerDemand.ContinuousPreference r ∧
      ConsumerDemand.ContinuousPreference r = RevealedPreference.ContinuousPreference r :=
  ⟨rfl, rfl⟩

/-- Strict monotonicity agrees with the copy used by Chapter 3's representation machinery. -/
theorem strictMonotonicity_agrees [PartialOrder X] (r : X → X → Prop) :
    PreferenceProperties.StrictlyMonotonePreference r =
      ConsumerDemand.Representation.StrictlyMonotonePreference r ∧
    ConsumerDemand.Representation.StrictlyMonotonePreference r =
      RevealedPreference.StrictlyMonotonePreference r := ⟨rfl, rfl⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- Convex mixing uses the same endpoint weights and underlying commodity vector. -/
theorem mixture_agrees (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    PreferenceProperties.Mix hS x y a ha = ConsumerDemand.Mix hS x y a ha ∧
      ConsumerDemand.Mix hS x y a ha = RevealedPreference.Mix hS x y a ha := ⟨rfl, rfl⟩

/-- Convex menus in Chapter 3 use Chapter 2's domain-internal notion. -/
theorem convexMenu_agrees (hS : Convex ℝ S) (A : Set S) :
    PreferenceProperties.ConvexMenu hS A = ConsumerDemand.ConvexMenu hS A := rfl

/-- Weak convexity of preference is unchanged from structural theory to revealed preference. -/
theorem convexPreference_agrees (hS : Convex ℝ S) (r : S → S → Prop) :
    PreferenceProperties.ConvexPreference hS r = ConsumerDemand.ConvexPreference hS r ∧
      ConsumerDemand.ConvexPreference hS r = RevealedPreference.ConvexPreference hS r :=
  ⟨rfl, rfl⟩

/-- Strict convexity keeps distinct endpoints and strictly interior weights in all copies. -/
theorem strictlyConvexPreference_agrees (hS : Convex ℝ S) (r : S → S → Prop) :
    PreferenceProperties.StrictlyConvexPreference hS r =
      ConsumerDemand.StrictlyConvexPreference hS r ∧
    ConsumerDemand.StrictlyConvexPreference hS r =
      RevealedPreference.StrictlyConvexPreference hS r := ⟨rfl, rfl⟩

/-- The concavity condition used for consumer optimization is Chapter 2's condition. -/
theorem concaveUtility_agrees (hS : Convex ℝ S) (u : S → ℝ) :
    PreferenceProperties.ConcaveUtility hS u = ConsumerDemand.ConcaveUtility hS u := rfl

/-- Weak quasi-concavity is unchanged in the demand existence and convexity results. -/
theorem quasiConcaveUtility_agrees (hS : Convex ℝ S) (u : S → ℝ) :
    PreferenceProperties.QuasiConcaveUtility hS u = ConsumerDemand.QuasiConcaveUtility hS u :=
  rfl

/-- Strict quasi-concavity retains the distinct-endpoint convention needed for uniqueness. -/
theorem strictlyQuasiConcaveUtility_agrees (hS : Convex ℝ S) (u : S → ℝ) :
    PreferenceProperties.StrictlyQuasiConcaveUtility hS u =
      ConsumerDemand.StrictlyQuasiConcaveUtility hS u := rfl

/-- Nonnegative bundle scaling, including zero, agrees between Chapters 2 and 3. -/
theorem bundleScaling_agrees {k : ℕ} (a : ℝ≥0) (x : ConsumerDemand.NonnegativeOrthant k) :
    PreferenceProperties.ScaleBundle a x = ConsumerDemand.ScaleBundle a x := rfl

/-- Homothetic demand uses precisely Chapter 2's preference condition. -/
theorem homotheticPreference_agrees {k : ℕ}
    (r : ConsumerDemand.NonnegativeOrthant k → ConsumerDemand.NonnegativeOrthant k → Prop) :
    PreferenceProperties.HomotheticPreference r = ConsumerDemand.HomotheticPreference r := rfl

/-- The price subtype changes packaging, not the expenditure formula. -/
theorem expenditure_agrees {k : ℕ} (p : ConsumerDemand.PositivePrices k)
    (x : ConsumerDemand.NonnegativeOrthant k) :
    ConsumerDemand.Expenditure p x = RevealedPreference.Expenditure p.val x.val := rfl

/-- The observed-data budget is the consumer budget after attaching its primitive sign proofs. -/
theorem budget_agrees {k : ℕ} (p : ConsumerDemand.PositivePrices k) (y : ℝ≥0) :
    ConsumerDemand.BudgetSet p y = RevealedPreference.Budget p.val (y : ℝ) := rfl

/-- An observed preference rationalization is exactly choice in the Chapter 3 budgets. -/
theorem rationalizes_iff_preferenceChoice {I : Type*} {k : ℕ}
    (D : RevealedPreference.MarketData I k)
    (r : ConsumerDemand.NonnegativeOrthant k → ConsumerDemand.NonnegativeOrthant k → Prop) :
    RevealedPreference.Rationalizes D r ↔ ∀ i,
      D.bundle i ∈ ConsumerDemand.PrefChoice r
        (ConsumerDemand.BudgetSet ⟨D.price i, D.price_pos i⟩
          ⟨D.income i, D.income_nonneg i⟩) := Iff.rfl

/-- Numerical rationalization is membership in the full Marshallian demand correspondence. -/
theorem rationalizes_iff_marshallianDemand {I : Type*} {k : ℕ}
    (D : RevealedPreference.MarketData I k) (u : ConsumerDemand.NonnegativeOrthant k → ℝ) :
    RevealedPreference.Rationalizes D (RevealedPreference.UtilityPref u) ↔ ∀ i,
      D.bundle i ∈ ConsumerDemand.MarshallianDemand u
        ⟨D.price i, D.price_pos i⟩ ⟨D.income i, D.income_nonneg i⟩ := Iff.rfl

/-- A Chapter 1 representation can be passed directly to Chapter 3's choice-to-demand bridge. -/
theorem chapterOne_representation_gives_demand {k : ℕ}
    {r : ConsumerDemand.NonnegativeOrthant k → ConsumerDemand.NonnegativeOrthant k → Prop}
    {u : ConsumerDemand.NonnegativeOrthant k → ℝ}
    (hu : ChoicePreferenceUtility.Represents u r)
    (p : ConsumerDemand.PositivePrices k) (y : ℝ≥0) :
    ChoicePreferenceUtility.PrefChoice r (ConsumerDemand.BudgetSet p y) =
      ConsumerDemand.MarshallianDemand u p y := ConsumerDemand.preferenceChoice_eq_demand hu p y

/-- Chapter 2's primitive continuity and rationality produce actual demand at every budget. -/
theorem chapterTwo_preferences_give_demand {k : ℕ}
    {r : ConsumerDemand.NonnegativeOrthant k → ConsumerDemand.NonnegativeOrthant k → Prop}
    (hr : PreferenceProperties.Rational r) (hc : PreferenceProperties.ContinuousPreference r) :
    ∃ u : ConsumerDemand.NonnegativeOrthant k → ℝ,
      PreferenceProperties.Represents u r ∧ Continuous u ∧
      ∀ p y, (ConsumerDemand.MarshallianDemand u p y).Nonempty := by
  obtain ⟨u, hu, huc⟩ := (PreferenceProperties.proposition_2_9 k hr).mp hc
  exact ⟨u, hu, huc, ConsumerDemand.proposition_3_1b huc⟩

/-- Afriat concavity passes through Chapter 2 to the exact Chapter 3 quasi-concavity API. -/
theorem afriatUtility_quasiConcave {k : ℕ} {u : (Fin k → ℝ) → ℝ}
    (hc : ConcaveOn ℝ Set.univ u) :
    ConsumerDemand.QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ))
      (fun x : ConsumerDemand.NonnegativeOrthant k => u x.val) := by
  apply PreferenceProperties.concaveUtility_quasi
  exact (PreferenceProperties.concaveUtility_iff_concaveOn
    (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u).mpr
      (hc.subset (Set.subset_univ _) (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)))

/-- GARP constructs an actual utility whose full Chapter 3 demand contains every observation. -/
theorem garp_gives_consumer_demand {I : Type*} [Finite I] {k : ℕ}
    {D : RevealedPreference.MarketData I k} (hG : RevealedPreference.GARP D) :
    ∃ u : (Fin k → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ i, D.bundle i ∈ ConsumerDemand.MarshallianDemand
        (fun x : ConsumerDemand.NonnegativeOrthant k => u x.val)
        ⟨D.price i, D.price_pos i⟩ ⟨D.income i, D.income_nonneg i⟩) ∧
      (∀ p y, (ConsumerDemand.MarshallianDemand
        (fun x : ConsumerDemand.NonnegativeOrthant k => u x.val) p y).Nonempty) ∧
      ∀ p y, ConsumerDemand.ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ))
        (ConsumerDemand.MarshallianDemand
          (fun x : ConsumerDemand.NonnegativeOrthant k => u x.val) p y) := by
  obtain ⟨u, hc, hm, hconc, hR⟩ := RevealedPreference.garp_exists_concave_utility hG
  exact ⟨u, hc, hm, hconc, (rationalizes_iff_marshallianDemand D _).mp hR,
    ConsumerDemand.proposition_3_1b (hc.comp continuous_subtype_val),
    ConsumerDemand.proposition_3_1c_convex (afriatUtility_quasiConcave hconc)⟩

/-- The constructed Afriat utility also satisfies Chapter 3's complete maximum theorem. -/
theorem garp_gives_consumer_maximum_theorem {I : Type*} [Finite I] {k : ℕ}
    {D : RevealedPreference.MarketData I k} (hG : RevealedPreference.GARP D) :
    ∃ u : ConsumerDemand.NonnegativeOrthant k → ℝ,
      RevealedPreference.Rationalizes D (RevealedPreference.UtilityPref u) ∧ Continuous u ∧
      (∀ θ : ConsumerDemand.PriceIncome k,
        (ConsumerDemand.MarshallianDemand u θ.1 θ.2).Nonempty) ∧
      ConsumerDemand.SequentialUpper
        (fun θ : ConsumerDemand.PriceIncome k => ConsumerDemand.MarshallianDemand u θ.1 θ.2) ∧
      ConsumerDemand.LocalCompactBound
        (fun θ : ConsumerDemand.PriceIncome k => ConsumerDemand.MarshallianDemand u θ.1 θ.2) ∧
      Continuous (fun θ : ConsumerDemand.PriceIncome k =>
        ConsumerDemand.IndirectUtility u θ.1 θ.2) := by
  obtain ⟨u, hc, _, _, hR⟩ := RevealedPreference.garp_exists_concave_utility hG
  exact ⟨fun x => u x.val, hR, hc.comp continuous_subtype_val,
    ConsumerDemand.consumer_maximum_theorem (hc.comp continuous_subtype_val)⟩

end Kreps.Compatibility
