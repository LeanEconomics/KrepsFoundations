/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotterySimpleLottery
import Mathlib.Geometry.Convex.Set

/-!
Local prerequisite copy of ChoiceUnderUncertainty.LotteryEvaluation from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Recovering a prize index from an affine lottery index

Kreps I, Proposition 5.3, pp. 95–96. Agreement on sure prizes extends to the
entire simplex. Mathlib proves closure under finite convex combinations from
binary closure by splitting off one positively weighted prize and normalizing
the remaining lottery, as in the source's support induction.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

/-- Any binary-mixture affine index has the expected-utility form on every simple lottery. -/
theorem affineInMix_eq_expectedUtility {X : Type*} {u : SimpleLottery X → ℝ}
    (hu : AffineInMix u) (p : SimpleLottery X) :
    u p = ExpectedUtility (fun x => u (PureLottery x)) p := by
  let U : X → ℝ := fun x => u (PureLottery x)
  let s : Set (SimpleLottery X) := {q | u q = ExpectedUtility U q}
  have hs : IsConvexSet ℝ s := by
    apply IsConvexSet.of_convexCombPair_mem
    intro a b ha hb hab x hx y hy
    have he : b = 1 - a := by linarith
    subst b
    let t : Weight := ⟨a, ha, by linarith⟩
    change u (Mix t x y) = ExpectedUtility U (Mix t x y)
    rw [hu, expectedUtility_affine, show u x = ExpectedUtility U x from hx,
      show u y = ExpectedUtility U y from hy]
  have hp : p.iConvexComb (fun x => PureLottery x) ∈ s := by
    apply hs.iConvexComb_mem
    intro x _
    exact (expectedUtility_pure U x).symm
  change p ∈ s
  simpa only [PureLottery, StdSimplex.iConvexComb_single] using hp

end Kreps.UtilityForMoney.LotteryTheory
