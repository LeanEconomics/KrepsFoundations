/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic

/-!
# Preference and consumption-domain prerequisites

Selected definitions and elementary results copied or adapted from Chapter 2,
commit `7d496c5`: `Basic`, `OrthantRepresentation`, `Monotonicity`,
`ConvexPreference`, and `ConcaveUtility`. Their economic conventions are unchanged.
Only the ingredients used by consumer demand are included in this independent
chapter package. The mathematical source is Kreps I, Chapters 1-2, pp. 1-44.
-/

namespace Kreps.ConsumerDemand

variable {X : Type*}

/-- Every pair of alternatives can be compared, including an alternative with itself. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- Weak preference is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- The book's standing rationality assumption: complete and transitive preference. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Alternatives at least as good as every feasible alternative. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Preference induced by utility, oriented with the preferred alternative first. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- A utility represents exactly the given weak preference. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Strict preference is weak preference without its reverse. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference is weak preference in both directions. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- Utility-induced preferences satisfy the chapter's rationality assumption. -/
theorem utilityPref_rational (u : X → ℝ) : Rational (UtilityPref u) :=
  ⟨fun x y => le_total (u y) (u x), fun _ _ _ hxy hyz => hyz.trans hxy⟩

/-- The consumption domain includes every boundary bundle and the origin. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- Local insatiability uses the book's closed-ball inequality. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- A convex combination as a point of its convex consumption domain. -/
def Mix (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- Internal convexity of a feasible menu agrees with closure under mixtures. -/
def ConvexMenu (hS : Convex ℝ S) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a, ∀ ha : a ∈ Set.Icc 0 1, Mix hS x y a ha ∈ A

/-- Mixtures are weakly better than the worse endpoint. -/
def ConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- Distinct endpoints give strictly better interior mixtures than the worse endpoint. -/
def StrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- Jensen's concavity inequality, on the actual consumption domain. -/
def ConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1,
    a * u x + (1 - a) * u y ≤ u (Mix hS x y a ha)

/-- The mixture's utility is at least the lesser endpoint utility. -/
def QuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, min (u x) (u y) ≤ u (Mix hS x y a ha)

/-- Distinct endpoints give a strict utility improvement over the worse one. -/
def StrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

end Kreps.ConsumerDemand
