/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.StoppedGambleLimits

/-!
# Limiting bankruptcy probability

Kreps I, Problem 6.14, p. 147. For the walk with increments plus two and minus
one, the positive root below one of the harmonic moment equation is
`(sqrt 7 - 1)/2`. Its stopped moment is constant. The surviving part of that
moment tends to zero, leaving the exact limit of the bankruptcy probability.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- The smaller positive solution of the walk's harmonic moment equation. -/
noncomputable def BankruptcyBase : ℝ := (Real.sqrt 7 - 1) / 2

/-- The harmonic root is positive and lies below the decaying test base 9/10. -/
theorem bankruptcyBase_bounds : 0 < BankruptcyBase ∧ BankruptcyBase < 9 / 10 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hn := Real.sqrt_nonneg 7
  unfold BankruptcyBase
  constructor <;> nlinarith

/-- The geometric moment with the harmonic root has exactly unit drift factor. -/
theorem bankruptcyBase_harmonic : WalkFactor BankruptcyBase = 1 := by
  have hq : 2 * BankruptcyBase ^ 2 + 2 * BankruptcyBase = 3 := by
    unfold BankruptcyBase
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
  have h₁ := congrArg (fun x : ℝ => x * BankruptcyBase) hq
  unfold WalkFactor
  field_simp [bankruptcyBase_bounds.1.ne']
  nlinarith only [hq, h₁]

/-- Indicator of zero terminal wealth. -/
def BankruptcyIndicator (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- The expected indicator is the actual point mass at zero in the terminal wealth law. -/
theorem bankruptcy_mass (n k : ℕ) : StoppedValue BankruptcyIndicator n k =
    (StoppedLaw n k).weights 0 := by
  unfold StoppedValue ExpectedUtility BankruptcyIndicator
  rw [Finsupp.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The harmonic stopped moment splits into the bankruptcy probability and the surviving moment. -/
theorem bankruptcy_probability_identity (n k : ℕ) :
    StoppedValue BankruptcyIndicator n k =
      BankruptcyBase ^ k - StoppedValue (AlivePower BankruptcyBase) n k := by
  have he : StoppedValue (fun j => BankruptcyBase ^ j) n k = BankruptcyBase ^ k :=
    le_antisymm (stopped_power_le bankruptcyBase_bounds.1 bankruptcyBase_harmonic.le n k)
      (stopped_power_ge bankruptcyBase_bounds.1 bankruptcyBase_harmonic.ge n k)
  have hp (j : ℕ) : 0 + 1 * BankruptcyIndicator j + 1 * AlivePower BankruptcyBase j =
      BankruptcyBase ^ j := by
    by_cases hj : j = 0 <;> simp [AlivePower, BankruptcyIndicator, hj]
  have hlin := stoppedValue_affine_two n k BankruptcyIndicator (AlivePower BankruptcyBase) 0 1 1
  rw [funext hp, he] at hlin
  linarith

/-- Every survival-weighted moment up to base 9/10 tends to zero. -/
theorem alivePower_tendsto {q : ℝ} (hq : 0 ≤ q) (hle : q ≤ 9 / 10) (k : ℕ) :
    Tendsto (fun n => StoppedValue (AlivePower q) n k) atTop (𝓝 0) := by
  let s : ℝ := 9 / 10
  have hs : 0 < s := by norm_num [s]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num [s, WalkFactor] : 0 ≤ WalkFactor s)
    (by norm_num [s, WalkFactor] : WalkFactor s < 1)
  have hl (n : ℕ) : 0 ≤ StoppedValue (AlivePower q) n k := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg ((StoppedLaw n k).nonneg i)
    unfold AlivePower
    split
    · exact le_rfl
    · exact pow_nonneg hq _
  apply squeeze_zero hl (fun n => le_trans ?_ (alivePower_bound hs n k))
    (by simpa only [zero_mul] using hp.mul_const (AlivePower s k))
  apply expectedUtility_mono
  intro i
  unfold AlivePower
  split
  · exact le_rfl
  · exact pow_le_pow_left₀ hq hle _

/-- The probability of hitting bankruptcy by the horizon converges to the exact ruin probability. -/
theorem bankruptcy_probability_limit (k : ℕ) :
    Tendsto (fun n => StoppedValue BankruptcyIndicator n k) atTop (𝓝 (BankruptcyBase ^ k)) := by
  simp_rw [bankruptcy_probability_identity]
  simpa only [sub_zero] using (alivePower_tendsto bankruptcyBase_bounds.1.le
    bankruptcyBase_bounds.2.le k).const_sub (BankruptcyBase ^ k)

end Kreps.UtilityForMoney
