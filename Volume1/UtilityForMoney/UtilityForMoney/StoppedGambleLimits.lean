/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.StoppedGambles

/-!
# Growing horizons under the bankruptcy rule

Kreps I, Problem 6.14(a), p. 147. A geometric moment bounds bankruptcy risk. A
second moment, killed at zero, makes the remaining probability of low positive
wealth vanish. This gives an eventual strict gain for every unbounded increasing
utility that is finite at zero, without assuming the utility increases at a
particular rate.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- The finite stopped lottery preserves constants plus two linear payoff terms. -/
theorem stoppedValue_affine_two (n k : ℕ) (f g : ℕ → ℝ) (A B C : ℝ) :
    StoppedValue (fun j => A + B * f j + C * g j) n k =
      A + B * StoppedValue f n k + C * StoppedValue g n k := by
  unfold StoppedValue
  rw [show (fun j => A + B * f j + C * g j) =
    fun j => 1 * (B * f j + C * g j) + A by funext j; ring, expectedUtility_affine_payoff,
    expectedUtility_linear_combination]
  ring

/-- A lower bound on utility in terms of the full and killed geometric moments. -/
theorem stopped_utility_lower (U : ℕ → ℝ) (hm : Monotone U) (M n k : ℕ) :
    let s : ℝ := 9 / 10
    let D := U M - U 0
    U 0 + D * (1 - s ^ k - (WalkFactor s ^ n * AlivePower s k) / s ^ M) ≤
      StoppedValue U n k := by
  intro s D
  have hs : 0 < s := by norm_num [s]
  have hs' : s ≤ 1 := by norm_num [s]
  have hc : WalkFactor s ≤ 1 := by norm_num [WalkFactor, s]
  have hd : 0 ≤ D := sub_nonneg.mpr (hm (Nat.zero_le M))
  have hM : 0 < s ^ M := pow_pos hs M
  have hlo (j : ℕ) : U 0 + D + (-D) * s ^ j + (-(D / s ^ M)) * AlivePower s j ≤ U j := by
    by_cases hj : j = 0
    · subst j
      simp [AlivePower]
    have ha : AlivePower s j = s ^ j := by simp [AlivePower, hj]
    rw [ha]
    have hdv := div_nonneg hd hM.le
    by_cases hcut : M ≤ j
    · have h₁ := mul_nonneg hd (pow_nonneg hs.le j)
      have h₂ := mul_nonneg hdv (pow_nonneg hs.le j)
      dsimp [D] at *
      linarith [hm hcut]
    · have hp := pow_le_pow_of_le_one hs.le hs' (le_of_not_ge hcut)
      have h₁ := mul_le_mul_of_nonneg_left hp hdv
      rw [div_mul_cancel₀ _ hM.ne'] at h₁
      linarith [hm (Nat.zero_le j), mul_nonneg hd (pow_nonneg hs.le j)]
  have he := expectedUtility_mono (StoppedLaw n k) hlo
  change StoppedValue _ n k ≤ StoppedValue U n k at he
  rw [stoppedValue_affine_two] at he
  have h₁ := mul_le_mul_of_nonneg_left (stopped_power_le hs hc n k) hd
  have h₂ := mul_le_mul_of_nonneg_left (alivePower_bound hs n k) (div_nonneg hd hM.le)
  simp only [div_eq_mul_inv] at he h₂ ⊢
  nlinarith only [he, h₁, h₂]

/-- **Problem 6.14(a):** every sufficiently long horizon improves unbounded increasing utility. -/
theorem problem_6_14_unbounded (U : ℕ → ℝ) (hm : StrictMono U) (hu : ∀ v : ℝ, ∃ M, v < U M)
    {k : ℕ} (hk : 0 < k) : ∀ᶠ n : ℕ in atTop, U k < StoppedValue U n k := by
  let s : ℝ := 9 / 10
  have hs : 0 < s := by norm_num [s]
  have hs' : s < 1 := by norm_num [s]
  have hsurv : 0 < 1 - s ^ k := sub_pos.mpr (pow_lt_one₀ hs.le hs' hk.ne')
  obtain ⟨M, hM⟩ := hu (U 0 + (U k - U 0) / (1 - s ^ k))
  let D := U M - U 0
  have ht : U k < U 0 + D * (1 - s ^ k) := by
    have he : (U k - U 0) / (1 - s ^ k) < D := by dsimp [D]; linarith
    linarith [(div_lt_iff₀ hsurv).mp he]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num [WalkFactor, s] : 0 ≤ WalkFactor s)
    (by norm_num [WalkFactor, s] : WalkFactor s < 1)
  have hlim : Tendsto (fun n : ℕ =>
      U 0 + D * (1 - s ^ k - (WalkFactor s ^ n * AlivePower s k) / s ^ M)) atTop
      (𝓝 (U 0 + D * (1 - s ^ k))) := by
    have he := ((hp.mul_const (AlivePower s k)).div_const (s ^ M)).const_sub (1 - s ^ k)
    simpa using (he.const_mul D).const_add (U 0)
  filter_upwards [hlim.eventually (isOpen_Ioi.mem_nhds ht)] with n hn
  exact hn.trans_le (stopped_utility_lower U hm.monotone M n k)

end Kreps.UtilityForMoney
