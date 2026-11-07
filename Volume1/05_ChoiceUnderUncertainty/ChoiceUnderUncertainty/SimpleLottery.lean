/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureSpace

/-!
# Finite-support lotteries and expected utility

Kreps I, Definition 5.2 and equation (5.3), pp. 85–88. Prize types may be
infinite. Mathlib's standard simplex gives each lottery its own finite support.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- A finitely supported probability distribution on an arbitrary prize space. -/
abbrev SimpleLottery (X : Type*) := StdSimplex ℝ X

/-- Degenerate lottery paying the given prize with certainty. -/
noncomputable def PureLottery {X : Type*} (x : X) : SimpleLottery X :=
  StdSimplex.single x

/-- The finite support sum of probability times prize utility. -/
noncomputable def ExpectedUtility {X : Type*} (U : X → ℝ) (p : SimpleLottery X) : ℝ :=
  p.weights.sum (fun x a => a * U x)

/-- Expected utility equals Mathlib's barycentric evaluation of the prize index. -/
theorem expectedUtility_eq_affineMap {X : Type*} (U : X → ℝ) (p : SimpleLottery X) :
    ExpectedUtility U p = StdSimplex.affineMapMk U p := by
  rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum]
  rfl

/-- A sure prize has exactly its specified prize utility. -/
theorem expectedUtility_pure {X : Type*} (U : X → ℝ) (x : X) :
    ExpectedUtility U (PureLottery x) = U x := by
  rw [expectedUtility_eq_affineMap]
  exact StdSimplex.affineMapMk_single U x

/-- Reduction of compound lotteries is coordinatewise probability averaging. -/
theorem lottery_mix_weight {X : Type*} (a : Weight) (p q : SimpleLottery X) (x : X) :
    (Mix a p q).weights x = a.val * p.weights x + (1 - a.val) * q.weights x := by
  simp [Mix]

/-- Expected utility is affine under objective mixtures of any two simple lotteries. -/
theorem expectedUtility_affine {X : Type*} (U : X → ℝ) : AffineInMix (ExpectedUtility U) := by
  intro a p q
  simp only [expectedUtility_eq_affineMap, Mix]
  rw [(StdSimplex.affineMapMk U).isAffineMap.map_convexCombPair, convexCombPair_eq_sum]
  rfl

/-- On a finite prize type the support sum also equals the sum over the entire type. -/
theorem expectedUtility_eq_sum {X : Type*} [Fintype X] (U : X → ℝ) (p : SimpleLottery X) :
    ExpectedUtility U p = ∑ x, p.weights x * U x := by
  exact Finsupp.sum_fintype _ _ (by simp)

end Kreps.ChoiceUnderUncertainty
