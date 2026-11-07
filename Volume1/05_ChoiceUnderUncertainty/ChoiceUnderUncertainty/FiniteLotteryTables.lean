/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.SimpleLottery

/-!
# Finite lottery diagrams

Kreps I, Definition 5.2 and Figures 5.2–5.11, pp. 85–117. Branches can lead
to the same prize. Pushing the branch probabilities forward adds their masses
and produces a finitely supported lottery on the original prize space.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- A finite branch table carries nonnegative probabilities summing to one. -/
structure BranchTable (n : ℕ) where
  /-- The probability written on each branch. -/
  mass : Fin n → ℝ
  /-- Each branch has nonnegative probability. -/
  nonnegative : ∀ i, 0 ≤ mass i
  /-- The probabilities sum to one. -/
  normalized : ∑ i, mass i = 1

/-- The probability distribution on the branch indices themselves. -/
noncomputable def BranchTable.distribution {n : ℕ} (p : BranchTable n) :
    Convexity.StdSimplex ℝ (Fin n) where
  weights := Finsupp.equivFunOnFinite.symm p.mass
  nonneg := fun i => by simpa using p.nonnegative i
  total := by simpa [Finsupp.sum_fintype] using p.normalized

/-- The actual prize lottery, with all branches leading to the same prize merged. -/
noncomputable def BranchTable.lottery {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) : Convexity.StdSimplex ℝ X := p.distribution.map prize

/-- Evaluation of a lottery diagram at any utility, before collecting equal prizes. -/
noncomputable def BranchTable.value {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) : ℝ := ∑ i, p.mass i * U (prize i)

/-- Summing utility on the reduced prize distribution gives exactly the diagram's value. -/
theorem BranchTable.lottery_value {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) :
    (p.lottery prize).weights.sum (fun x t => t * U x) = p.value prize U := by
  classical
  unfold BranchTable.lottery
  rw [Convexity.StdSimplex.weights_map, Finsupp.sum_mapDomain_index (by simp)
    (by intro b x y; exact add_mul x y (U b))]
  simp [BranchTable.distribution, Finsupp.sum_fintype, BranchTable.value]

/-- A diagram can be evaluated directly through the chapter's expected-utility interface. -/
theorem expectedUtility_branchLottery {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) :
    ExpectedUtility U (p.lottery prize) = p.value prize U := p.lottery_value prize U

/-- The probability table for a sure prize. -/
def CertainBranch : BranchTable 1 := ⟨![1], by intro i; fin_cases i; norm_num,
  by norm_num [Fin.sum_univ_succ]⟩

/-- A two-branch lottery with an arbitrary admissible first probability. -/
noncomputable def TwoBranches (a : ℝ) (ha : a ∈ Set.Icc 0 1) : BranchTable 2 :=
  ⟨![a, 1 - a], by intro i; fin_cases i <;> simp [ha.1, ha.2], by simp [Fin.sum_univ_two]⟩

/-- The value of a sure prize is its utility. -/
theorem certainBranch_value {X : Type*} (x : X) (U : X → ℝ) :
    CertainBranch.value (fun _ => x) U = U x := by
  simp [BranchTable.value, CertainBranch]

/-- A two-branch diagram gives the usual binary expectation formula. -/
theorem twoBranches_value {X : Type*} (a : ℝ) (ha : a ∈ Set.Icc 0 1)
    (x y : X) (U : X → ℝ) :
    (TwoBranches a ha).value ![x, y] U = a * U x + (1 - a) * U y := by
  simp [TwoBranches, BranchTable.value, Fin.sum_univ_two]

/-- Three labeled branches with explicitly certified probabilities. -/
noncomputable def ThreeBranches (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : BranchTable 3 :=
  ⟨![a, b, c], by intro i; fin_cases i <;> assumption,
    by simpa [Fin.sum_univ_succ, add_assoc] using h⟩

/-- The evaluation rule for a three-branch diagram, including repeated prizes. -/
theorem threeBranches_value {X : Type*} (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : a + b + c = 1) (x y z : X) (U : X → ℝ) :
    (ThreeBranches a b c ha hb hc h).value ![x, y, z] U =
      a * U x + b * U y + c * U z := by
  simp [BranchTable.value, ThreeBranches, Fin.sum_univ_succ, add_assoc]

end Kreps.ChoiceUnderUncertainty
