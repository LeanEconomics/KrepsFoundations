/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.RepeatedGambles
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Repeating the gamble with absorption at bankruptcy

Kreps I, Problem 6.14, p. 147. In units of 500 dollars the walk goes up two
with probability 2/5 or down one with probability 3/5, starting at four.
The finite terminal law stops at zero. Geometric test functions bound both
the mass at zero and the mass at small positive wealth.
-/

namespace Kreps.UtilityForMoney

/-- Exact finite terminal wealth law, measured in 500-dollar units, stopped at bankruptcy. -/
noncomputable def StoppedLaw : ℕ → ℕ → SimpleLottery ℕ
  | 0, k => Convexity.StdSimplex.single k
  | _ + 1, 0 => Convexity.StdSimplex.single 0
  | n + 1, k + 1 => TrialBranch (StoppedLaw n (k + 3)) (StoppedLaw n k)

/-- Expected terminal utility at horizon `n` and initial wealth `k` units. -/
noncomputable def StoppedValue (U : ℕ → ℝ) (n k : ℕ) : ℝ := ExpectedUtility U (StoppedLaw n k)

/-- At zero horizon the initial wealth is retained. -/
theorem stoppedValue_initial (U : ℕ → ℝ) (k : ℕ) : StoppedValue U 0 k = U k :=
  expectedUtility_single U k

/-- Bankruptcy is absorbing at every subsequent horizon. -/
theorem stoppedValue_bankrupt (U : ℕ → ℝ) (n : ℕ) : StoppedValue U n 0 = U 0 := by
  cases n <;> exact expectedUtility_single U 0

/-- From positive wealth the next draw has the source's fixed two branch probabilities. -/
theorem stoppedValue_step (U : ℕ → ℝ) (n k : ℕ) :
    StoppedValue U (n + 1) (k + 1) =
      (2 * StoppedValue U n (k + 3) + 3 * StoppedValue U n k) / 5 :=
  trialBranch_value U _ _

/-- Expected-utility evaluation preserves pointwise inequalities. -/
theorem expectedUtility_mono {I : Type*} (p : SimpleLottery I) {f g : I → ℝ}
    (h : ∀ i, f i ≤ g i) : ExpectedUtility f p ≤ ExpectedUtility g p :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (p.nonneg i)

/-- The multiplier for the geometric test `s^k` at positive wealth. -/
noncomputable def WalkFactor (s : ℝ) : ℝ := (2 * s ^ 2 + 3 / s) / 5

/-- A single interior step multiplies the geometric test by its scalar factor. -/
theorem walk_geometric_step {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (2 * s ^ (k + 3) + 3 * s ^ k) / 5 = WalkFactor s * s ^ (k + 1) := by
  rw [pow_add, pow_succ]
  unfold WalkFactor
  field_simp
  ring

/-- A factor below one bounds the stopped geometric moment at every horizon. -/
theorem stopped_power_le {s : ℝ} (hs : 0 < s) (hc : WalkFactor s ≤ 1) (n k : ℕ) :
    StoppedValue (fun j => s ^ j) n k ≤ s ^ k := by
  induction n generalizing k with
  | zero => rw [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => rw [stoppedValue_bankrupt]
    | succ k =>
      rw [stoppedValue_step]
      calc
        _ ≤ (2 * s ^ (k + 3) + 3 * s ^ k) / 5 := by linarith [ih (k + 3), ih k]
        _ = _ := walk_geometric_step hs k
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg hs.le (k + 1))

/-- A factor above one reverses the stopped geometric-moment comparison. -/
theorem stopped_power_ge {s : ℝ} (hs : 0 < s) (hc : 1 ≤ WalkFactor s) (n k : ℕ) :
    s ^ k ≤ StoppedValue (fun j => s ^ j) n k := by
  induction n generalizing k with
  | zero => rw [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => rw [stoppedValue_bankrupt]
    | succ k =>
      rw [stoppedValue_step]
      calc
        _ ≤ WalkFactor s * s ^ (k + 1) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg hs.le (k + 1))
        _ = _ := (walk_geometric_step hs k).symm
        _ ≤ _ := by linarith [ih (k + 3), ih k]

/-- The geometric test restricted to the survival event. -/
noncomputable def AlivePower (s : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else s ^ k

/-- The survival-weighted geometric moment is at most the geometric power of the factor. -/
theorem alivePower_bound {s : ℝ} (hs : 0 < s) (n k : ℕ) :
    StoppedValue (AlivePower s) n k ≤ WalkFactor s ^ n * AlivePower s k := by
  have hfac : 0 ≤ WalkFactor s := by unfold WalkFactor; positivity
  induction n generalizing k with
  | zero => simp [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => simp [stoppedValue_bankrupt, AlivePower]
    | succ k =>
      rw [stoppedValue_step]
      have ha : AlivePower s k ≤ s ^ k := by
        unfold AlivePower
        split
        · positivity
        · exact le_rfl
      have hb : AlivePower s (k + 3) = s ^ (k + 3) := by simp [AlivePower]
      have hbase : AlivePower s (k + 1) = s ^ (k + 1) := by simp [AlivePower]
      have hk := mul_le_mul_of_nonneg_left ha (pow_nonneg hfac n)
      have h := walk_geometric_step hs k
      rw [pow_succ, hbase]
      calc
        _ ≤ WalkFactor s ^ n * ((2 * s ^ (k + 3) + 3 * s ^ k) / 5) := by
          have h₁ := ih (k + 3)
          rw [hb] at h₁
          linarith only [h₁, ih k, hk]
        _ = _ := by rw [h]; ring

/-- The two bounded example utilities strictly increase and have the finite upper bound one. -/
theorem bounded_walk_utility {s : ℝ} (hp : 0 < s) (hl : s < 1) :
    StrictMono (fun k : ℕ => 1 - s ^ k) ∧ ∀ k : ℕ, 1 - s ^ k < 1 :=
  ⟨fun _ _ h => sub_lt_sub_left (pow_lt_pow_right_of_lt_one₀ hp hl h) _,
    fun k => sub_lt_self _ (pow_pos hp k)⟩

/-- **Problem 6.14(b):** two bounded increasing utilities make opposite choices at every horizon. -/
theorem problem_6_14_bounded (n : ℕ) :
    1 - (9 / 10 : ℝ) ^ 4 < StoppedValue (fun k => 1 - (9 / 10 : ℝ) ^ k) (n + 1) 4 ∧
      StoppedValue (fun k => 1 - (1 / 2 : ℝ) ^ k) (n + 1) 4 < 1 - (1 / 2 : ℝ) ^ 4 := by
  have hlin (s : ℝ) : StoppedValue (fun k => 1 - s ^ k) (n + 1) 4 =
      1 - StoppedValue (fun k => s ^ k) (n + 1) 4 := by
    simpa [StoppedValue, sub_eq_add_neg, add_comm] using
      expectedUtility_affine_payoff (StoppedLaw (n + 1) 4) (fun k => s ^ k) (-1) 1
  rw [hlin, hlin, show 4 = 3 + 1 by decide, stoppedValue_step, stoppedValue_step]
  constructor
  · have h := stopped_power_le (by norm_num : (0 : ℝ) < 9 / 10)
      (by norm_num [WalkFactor]) n
    norm_num at *
    linarith [h 6, h 3]
  · have h := stopped_power_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num [WalkFactor]) n
    norm_num at *
    linarith [h 6, h 3]

end Kreps.UtilityForMoney
