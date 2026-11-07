/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.StrictPreference
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Mixture spaces and their preference axioms

Kreps I, Sections 5.1–5.2, pp. 88–92. Mathlib's convex spaces supply the
usual mixture identities on abstract spaces. The independence axiom compares
different common backgrounds at a fixed weight, including both endpoint weights.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- A mixture weight, including both endpoints. -/
abbrev Weight := Set.Icc (0 : ℝ) 1

/-- The mixture with probability `a` on the first alternative. -/
noncomputable def Mix {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x y : Z) : Z :=
  convexCombPair a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
    (by ring) x y

/-- A numerical index is affine in the book's binary mixtures. -/
def AffineInMix {Z : Type*} [ConvexSpace ℝ Z] (u : Z → ℝ) : Prop :=
  ∀ (a : Weight) x y, u (Mix a x y) = a.val * u x + (1 - a.val) * u y

/-- Part (b) of Proposition 5.4 compares strict rankings under a change of common background. -/
def BackgroundIndependent {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ (a : Weight) x y z w,
    Strict r (Mix a x z) (Mix a y z) ↔ Strict r (Mix a x w) (Mix a y w)

/-- Part (c) of Proposition 5.4 requires both strict comparisons near weight one. -/
def MixtureContinuous {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ x y, Strict r x y → ∀ z, ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ a : Weight,
    c < a.val → Strict r (Mix a x z) y ∧ Strict r x (Mix a y z)

/-- The three primitive hypotheses of the mixture-space theorem. -/
def MixtureAxioms {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  Rational r ∧ BackgroundIndependent r ∧ MixtureContinuous r

/-- Complementary mixture weight. -/
def Complement (a : Weight) : Weight :=
  ⟨1 - a.val, sub_nonneg.mpr a.property.2, sub_le_self _ a.property.1⟩

/-- Mixing a point with itself leaves it fixed. -/
theorem mix_self {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x : Z) : Mix a x x = x :=
  convexCombPair_same _ _ _

/-- Zero weight selects the second alternative. -/
theorem mix_zero {Z : Type*} [ConvexSpace ℝ Z] (x y : Z) : Mix 0 x y = y := by
  simp [Mix]

/-- Unit weight selects the first alternative. -/
theorem mix_one {Z : Type*} [ConvexSpace ℝ Z] (x y : Z) : Mix 1 x y = x := by
  simp [Mix]

/-- Complementing the weight and swapping alternatives preserves a mixture. -/
theorem mix_swap {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x y : Z) :
    Mix a x y = Mix (Complement a) y x := by
  unfold Mix Complement
  rw [convexCombPair_symm]
  congr 1
  ring

end Kreps.ChoiceUnderUncertainty
