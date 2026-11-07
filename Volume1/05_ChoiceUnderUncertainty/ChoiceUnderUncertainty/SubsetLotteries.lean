/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.CompoundExamples

/-!
# Lotteries over entire subsets and lotteries over inclusion marginals

Kreps I, Problem 5.5, pp. 118–119. A binary roulette is affinely parameterized
by its probability of inclusion. Arbitrary set utility extends to lotteries of
subsets. On the cube of marginal inclusion probabilities an affine index has an
additive restriction to the deterministic vertices after normalizing its origin.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The inclusion probability of a binary lottery lies in the unit interval. -/
noncomputable def InclusionProbability (p : SimpleLottery Bool) : Weight :=
  ⟨p.weights true, p.nonneg true, p.weights_apply_le_one true⟩

/-- The unique Bernoulli lottery having the chosen inclusion probability. -/
noncomputable def InclusionLottery (a : Weight) : SimpleLottery Bool :=
  Convexity.StdSimplex.duple true false a.property.1 (sub_nonneg.mpr a.property.2) (by ring)

/-- The Bernoulli law has precisely its specified marginal. -/
theorem inclusionProbability_lottery (a : Weight) :
    InclusionProbability (InclusionLottery a) = a := by
  apply Subtype.ext
  simp [InclusionProbability, InclusionLottery]

/-- Its inclusion probability determines the entire binary lottery. -/
theorem inclusionLottery_probability (p : SimpleLottery Bool) :
    InclusionLottery (InclusionProbability p) = p := by
  apply Convexity.StdSimplex.ext
  ext b
  have ht := p.total_of_fintype
  rw [Fintype.sum_bool] at ht
  cases b <;> simp [InclusionProbability, InclusionLottery]
  linarith

/-- Binary roulette marginals mix coordinatewise by the affine formula prescribed on the cube. -/
theorem inclusionProbability_mix (a : Weight) (p q : SimpleLottery Bool) :
    (InclusionProbability (Mix a p q)).val =
      a.val * (InclusionProbability p).val + (1 - a.val) * (InclusionProbability q).val :=
  lottery_mix_weight a p q true

/-- A deterministic subset has inclusion probabilities zero or one at every coordinate. -/
noncomputable def SubsetVertex {X : Type*} [DecidableEq X] (z : Finset X) :
    HorseLottery X Bool := fun x => if x ∈ z then PureLottery true else PureLottery false

/-- The map from subsets really gives their pointwise characteristic probabilities. -/
theorem subsetVertex_probability {X : Type*} [DecidableEq X] (z : Finset X) (x : X) :
    (InclusionProbability (SubsetVertex z x)).val = if x ∈ z then 1 else 0 := by
  by_cases hx : x ∈ z <;> simp [SubsetVertex, InclusionProbability, PureLottery, hx]

/-- Any utility on whole subsets extends to a mixture-affine utility on lotteries of subsets. -/
theorem subsetLottery_extension {X : Type*} (U : Finset X → ℝ) :
    AffineInMix (ExpectedUtility U) ∧ ∀ z, ExpectedUtility U (PureLottery z) = U z :=
  ⟨expectedUtility_affine U, expectedUtility_pure U⟩

/-- Normalizing an affine marginal utility at the empty subset gives additive item values. -/
theorem subsetMargin_additive {X : Type*} [Finite X] [DecidableEq X]
    {F : HorseLottery X Bool → ℝ} (hF : AffineInMix F) :
    ∃ U : X → ℝ, ∀ z : Finset X, F (SubsetVertex z) - F (SubsetVertex ∅) = ∑ x ∈ z, U x := by
  let _ := Fintype.ofFinite X
  let b : HorseLottery X Bool := fun _ => PureLottery false
  have hbase : SubsetVertex (∅ : Finset X) = b := by ext x; simp [SubsetVertex, b]
  let U : X → ℝ := fun x => StateIncrement F b x (PureLottery true)
  refine ⟨U, fun z => ?_⟩
  rw [hbase, horseValue_of_affine hF b (SubsetVertex z)]
  unfold HorseValue StateAdditiveValue
  calc
    _ = ∑ x, (if x ∈ z then U x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ z
      · simp [SubsetVertex, hx, expectedUtility_pure, U]
      · simp [SubsetVertex, hx, expectedUtility_pure, StateIncrement, b]
    _ = _ := by simp

/-- An explicit joint value on two objects violates item additivity, even up to a constant. -/
theorem wholeSubset_utility_nonadditive :
    ¬∃ (U : Bool → ℝ) (B : ℝ), ∀ z : Finset Bool,
      (if z = {true, false} then (1 : ℝ) else 0) = B + ∑ x ∈ z, U x := by
  rintro ⟨U, B, h⟩
  have a := h ∅
  have b := h {true}
  have c := h {false}
  have d := h {true, false}
  have e₀ : (∅ : Finset Bool) ≠ {true, false} := by decide
  have e₁ : ({true} : Finset Bool) ≠ {true, false} := by decide
  have e₂ : ({false} : Finset Bool) ≠ {true, false} := by decide
  norm_num [e₀, e₁, e₂] at a b c d
  linarith

/-- The affine index on the entire marginal cube is linear in the inclusion probabilities. -/
theorem subsetMargin_cube_value {X : Type*} [Fintype X] [DecidableEq X]
    {F : HorseLottery X Bool → ℝ} (hF : AffineInMix F) :
    ∃ U : X → ℝ, ∀ q : X → Weight,
      F (fun x => InclusionLottery (q x)) - F (SubsetVertex ∅) = ∑ x, (q x).val * U x := by
  let b : HorseLottery X Bool := fun _ => PureLottery false
  have hbase : SubsetVertex (∅ : Finset X) = b := by ext x; simp [SubsetVertex, b]
  let U : X → ℝ := fun x => StateIncrement F b x (PureLottery true)
  refine ⟨U, fun q => ?_⟩
  rw [hbase, horseValue_of_affine hF b]
  apply Finset.sum_congr rfl
  intro i _
  change ExpectedUtility (fun x => StateIncrement F b i (PureLottery x)) (InclusionLottery (q i)) =
    (q i).val * U i
  rw [expectedUtility_eq_sum, Fintype.sum_bool]
  simp [InclusionLottery, U, StateIncrement, b]

end Kreps.ChoiceUnderUncertainty
