/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.StoppedRuinProbability

/-!
# A limiting criterion for bounded utility in the stopped gamble

Kreps I, final question of Problem 6.14, p. 147. A bounded increasing utility
tends to its supremum at high wealth. The limiting expected utility is the
bankruptcy value weighted by the ruin probability plus the supremum weighted
by survival. Strict comparison to current utility gives eventual acceptance
or rejection.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Expected bounded utility cannot exceed the upper utility level on surviving paths. -/
theorem stopped_bounded_upper (U : ℕ → ℝ) {L : ℝ} (hU : ∀ j, U j ≤ L) (n k : ℕ) :
    StoppedValue U n k ≤ L + (U 0 - L) * StoppedValue BankruptcyIndicator n k := by
  have hv (j : ℕ) : U j ≤ (U 0 - L) * BankruptcyIndicator j + L := by
    by_cases hz : j = 0
    · subst j
      simp [BankruptcyIndicator]
    · simpa [BankruptcyIndicator, hz] using hU j
  have he := expectedUtility_mono (StoppedLaw n k) hv
  rw [expectedUtility_affine_payoff] at he
  simpa only [StoppedValue, add_comm] using he

/-- A cutoff lower bound keeps the exact bankruptcy probability; only low positive wealth costs
an error term that vanishes with the horizon. -/
theorem stopped_bounded_lower (U : ℕ → ℝ) (hm : Monotone U) (M n k : ℕ) :
    let s : ℝ := 9 / 10
    U M + (U 0 - U M) * StoppedValue BankruptcyIndicator n k -
        (U M - U 0) / s ^ M * StoppedValue (AlivePower s) n k ≤ StoppedValue U n k := by
  intro s
  have hs : 0 < s := by norm_num [s]
  have hd := sub_nonneg.mpr (hm (Nat.zero_le M))
  have hp : 0 < s ^ M := pow_pos hs M
  have hv (j : ℕ) : U M + (U 0 - U M) * BankruptcyIndicator j +
      (-((U M - U 0) / s ^ M)) * AlivePower s j ≤ U j := by
    by_cases hz : j = 0
    · subst j
      simp [BankruptcyIndicator, AlivePower]
    simp [BankruptcyIndicator, AlivePower, hz]
    by_cases hcut : M ≤ j
    · have hp' := mul_nonneg (div_nonneg hd hp.le) (pow_nonneg hs.le j)
      linarith [hm hcut]
    · have he := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le
        (by norm_num [s] : s ≤ 1) (le_of_not_ge hcut)) (div_nonneg hd hp.le)
      rw [div_mul_cancel₀ _ hp.ne'] at he
      linarith [hm (Nat.zero_le j)]
  have he := expectedUtility_mono (StoppedLaw n k) hv
  change StoppedValue _ n k ≤ StoppedValue U n k at he
  rw [stoppedValue_affine_two, neg_mul] at he
  linarith

/-- The exact limiting expected utility under the stopped independent trials. -/
theorem stopped_bounded_limit (U : ℕ → ℝ) (hm : Monotone U) {L : ℝ}
    (hlim : Tendsto U atTop (𝓝 L)) (k : ℕ) :
    Tendsto (fun n => StoppedValue U n k) atTop (𝓝 (L + (U 0 - L) * BankruptcyBase ^ k)) := by
  have hupper (j : ℕ) : U j ≤ L := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_atTop.2 ⟨j, fun i hi => hm hi⟩)
  have hruin := bankruptcy_probability_limit k
  have hdecay := alivePower_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 10) le_rfl k
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hcut := hlim.add ((hlim.const_sub (U 0)).mul_const (BankruptcyBase ^ k))
    obtain ⟨M, hM⟩ := (hcut.eventually (isOpen_Ioi.mem_nhds ha)).exists
    change a < U M + (U 0 - U M) * BankruptcyBase ^ k at hM
    have hlow := ((hruin.const_mul (U 0 - U M)).const_add (U M)).sub
      (hdecay.const_mul ((U M - U 0) / (9 / 10 : ℝ) ^ M))
    simp only [mul_zero, sub_zero] at hlow
    filter_upwards [hlow.eventually (isOpen_Ioi.mem_nhds hM)] with n hn
    exact hn.trans_le (stopped_bounded_lower U hm M n k)
  · intro b hb
    have hhigh := (hruin.const_mul (U 0 - L)).const_add L
    filter_upwards [hhigh.eventually (isOpen_Iio.mem_nhds hb)] with n hn
    exact (stopped_bounded_upper U hupper n k).trans_lt hn

/-- **Problem 6.14, bounded-utility criterion:** strict comparison to the limiting value
decides the preference for all sufficiently long horizons. -/
theorem stopped_bounded_criterion (U : ℕ → ℝ) (hm : Monotone U) (hb : BddAbove (Set.range U))
    (k : ℕ) :
    let L := ⨆ j, U j
    let e := L + (U 0 - L) * BankruptcyBase ^ k
    (U k < e → ∀ᶠ n : ℕ in atTop, U k < StoppedValue U n k) ∧
    (e < U k → ∀ᶠ n : ℕ in atTop, StoppedValue U n k < U k) := by
  intro L e
  have h := stopped_bounded_limit U hm (tendsto_atTop_ciSup hm hb) k
  exact ⟨fun he => h.eventually (isOpen_Ioi.mem_nhds he),
    fun he => h.eventually (isOpen_Iio.mem_nhds he)⟩

end Kreps.UtilityForMoney
