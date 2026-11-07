/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.LotteryMixtureSpace

/-!
Local prerequisite copy of ChoiceUnderUncertainty.MixtureAlgebra from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Algebra of a binary mixture segment

Kreps I, p. 89. Two nested mixtures of the same prizes reduce to a single
mixture whose first probability is the weighted mean of the inner probabilities.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

open Convexity

/-- A weighted mean of two probabilities lies in the unit interval. -/
def WeightMean (a b c : Weight) : Weight :=
  ⟨a.val * b.val + (1 - a.val) * c.val,
    add_nonneg (mul_nonneg a.property.1 b.property.1)
      (mul_nonneg (sub_nonneg.mpr a.property.2) c.property.1), by
    nlinarith [mul_nonneg a.property.1 (sub_nonneg.mpr b.property.2),
      mul_nonneg (sub_nonneg.mpr a.property.2) (sub_nonneg.mpr c.property.2)]⟩

/-- A mixture of mixtures on the same segment reduces to one weighted mean. -/
theorem mix_mix {Z : Type*} [ConvexSpace ℝ Z] (a b c : Weight) (x y : Z) :
    Mix a (Mix b x y) (Mix c x y) = Mix (WeightMean a b c) x y := by
  let d (t : Weight) : StdSimplex ℝ Z :=
    .duple x y t.property.1 (sub_nonneg.mpr t.property.2) (by ring)
  change Mix a (sConvexComb (d b)) (sConvexComb (d c)) = sConvexComb (d _)
  unfold Mix
  rw [← sConvexComb_convexCombPair]
  apply congrArg sConvexComb
  apply StdSimplex.ext
  classical
  simp only [StdSimplex.weights_convexCombPair, d, StdSimplex.weights_duple, smul_add,
    Finsupp.smul_single, smul_eq_mul, WeightMean]
  rw [add_add_add_comm, ← Finsupp.single_add, ← Finsupp.single_add]
  congr 2
  ring

end Kreps.UtilityForMoney.LotteryTheory
