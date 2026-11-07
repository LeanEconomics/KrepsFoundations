/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.CARACalibrationPreferences

/-!
# Ranking the offers in Problem 6.2 from constant risk premia

Kreps I, Problem 6.2, pp. 140–141. Equal risk premia preserve the certainty equivalents
of endpoint lotteries after a $200 wealth shift. Their indifferences pin down a single
positive affine transformation on the overlap. Iterating this transformation on the
finite prize grid gives the rankings from the stated $2400 certainty equivalent.
-/

namespace Kreps.UtilityForMoney

/-- Two opposite premium comparisons preserve every certainty equivalent on a convex interval. -/
theorem certaintyEquivalent_of_equal_premia {S : Set ℝ} (hS : Convex ℝ S) {U V : ℝ → ℝ}
    (hc : ContinuousOn V S) (huv : PremiumOrder S U V) (hvu : PremiumOrder S V U)
    (p : SimpleLottery S) {c : S} (h : IsCertaintyEquivalent (fun z : S => U z) p c) :
    IsCertaintyEquivalent (fun z : S => V z) p c := by
  obtain ⟨d, hd⟩ := proposition_6_5_exists hS hc p
  have hcd := huv p c d h hd
  have hdc := hvu p d c hd h
  have he : c = d := by
    apply Subtype.ext
    unfold RiskPremium at hcd hdc
    linarith
  exact he ▸ hd

/-- On the common prize interval a $200 wealth shift is a positive affine change of index. -/
theorem calibration_shift_affine {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ContinuousOn U CalibrationInterval) (hC : ConstantRiskAversion CalibrationInterval U) :
    ∃ q > 0, ∃ b, ∀ x ∈ Set.Icc (-1000 : ℝ) 4800, U (x + 200) = q * U x + b := by
  let S := Set.Icc (-1000 : ℝ) 4800
  have dom : ShiftDomain CalibrationInterval 0 200 = S := by
    ext x
    change ((-1000 ≤ x + 0 ∧ x + 0 ≤ 5000) ∧ -1000 ≤ x + 200 ∧ x + 200 ≤ 5000) ↔ _
    change _ ↔ -1000 ≤ x ∧ x ≤ 4800
    constructor
    · rintro ⟨⟨hl, _⟩, _, hh⟩
      constructor <;> linarith
    · rintro ⟨hl, hh⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have revdom : ShiftDomain CalibrationInterval 200 0 = S := by
    rw [← dom]
    ext x
    exact and_comm
  have forward := hC.1 0 200 (by norm_num)
  have backward := hC.2 0 200 (by norm_num)
  simp only [ShiftPremiumOrder, dom, revdom, add_zero] at forward backward
  have cont : ContinuousOn (fun z => U (z + 200)) S :=
    hc.comp (continuous_id.add_const 200).continuousOn (fun x hx => by
      have hh := hx.2
      have hl := hx.1
      exact ⟨by linarith, by linarith⟩)
  have endpoints : U (-1000) < U 4800 :=
    hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  have shifted : U (-800) < U 5000 :=
    hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  let q := (U 5000 - U (-800)) / (U 4800 - U (-1000))
  refine ⟨q, div_pos (sub_pos.mpr shifted) (sub_pos.mpr endpoints),
    U (-800) - q * U (-1000), ?_⟩
  intro x hx
  have hxc : x ∈ CalibrationInterval := ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hlo := hi.monotoneOn (by norm_num [CalibrationInterval]) hxc hx.1
  have hhi := hi.monotoneOn hxc (by norm_num [CalibrationInterval]) hx.2
  let a := (U x - U (-1000)) / (U 4800 - U (-1000))
  have ha : a ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr endpoints.le),
      (div_le_one (sub_pos.mpr endpoints)).mpr (by linarith)⟩
  let high : S := ⟨4800, by norm_num [S]⟩
  let low : S := ⟨-1000, by norm_num [S]⟩
  let c : S := ⟨x, hx⟩
  let p := BinaryLottery high low a ha
  have ce : IsCertaintyEquivalent (fun z : S => U z) p c := by
    unfold IsCertaintyEquivalent p
    rw [expectedUtility_binary]
    change U x = a * U 4800 + (1 - a) * U (-1000)
    dsimp [a]
    field_simp [(sub_pos.mpr endpoints).ne']
    ring
  have h := certaintyEquivalent_of_equal_premia (convex_Icc _ _) cont forward backward p ce
  unfold IsCertaintyEquivalent p at h
  rw [expectedUtility_binary] at h
  change U (x + 200) = a * U (4800 + 200) + (1 - a) * U (-1000 + 200) at h
  norm_num at h
  rw [h]
  dsimp [a, q]
  field_simp [(sub_pos.mpr endpoints).ne']
  ring

/-- The affine shift recursion and the reported indifference rank the three offers on the grid. -/
theorem calibrated_grid_ranking (G : ℕ → ℝ) {q b : ℝ} (hq : 0 < q)
    (step : ∀ n < 30, G (n + 1) = q * G n + b) (hi : G 0 < G 1)
    (he : (G 30 + G 5) / 2 = G 17) :
    G 15 < 2/5 * G 30 + 3/10 * G 5 + 3/10 * G 10 ∧
      2/5 * G 30 + 3/10 * G 5 + 3/10 * G 10 < 3/5 * G 30 + 2/5 * G 0 := by
  have hn : q ≠ 1 := by
    rintro rfl
    have lin (n : ℕ) (hn : n ≤ 30) : G n = G 0 + n * b := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [step n (by omega), ih (by omega), Nat.cast_succ]
        ring
    rw [lin 30 (by decide), lin 5 (by decide), lin 17 (by decide)] at he
    rw [lin 1 (by decide)] at hi
    norm_num at hi he
    linarith
  let A := b / (1 - q)
  let D := G 0 - A
  have fixed : q * A + b = A := by
    dsimp [A]
    field_simp [sub_ne_zero.mpr hn.symm]
    ring
  have grid (n : ℕ) (hn : n ≤ 30) : G n = A + D * q ^ n := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [step n (by omega), ih (by omega), pow_succ]
      linear_combination fixed
  have hD : D ≠ 0 := by
    intro hz
    rw [grid 0 (by decide), grid 1 (by decide), hz] at hi
    simp at hi
  let T := D * q ^ 5
  have hT : T ≠ 0 := mul_ne_zero hD (pow_ne_zero _ hq.ne')
  have above (n : ℕ) (h : n + 5 ≤ 30) : G (n + 5) = A + T * q ^ n := by
    rw [grid _ h, pow_add]
    dsimp [T]
    ring
  have zero : G 5 = A + T := by simpa using above 0 (by decide)
  have low : G 0 = A + T / q ^ 5 := by
    rw [grid 0 (by decide)]
    simp [T, hq.ne']
  rw [above 25 (by decide), zero, above 12 (by decide)] at he
  have product : T * (2 * q ^ 12 - 1 - q ^ 25) = 0 := by linarith
  have equation : 2 * q ^ 12 = 1 + q ^ 25 := by
    have h := (mul_eq_zero.mp product).resolve_left hT
    linarith
  have hlt : q < 1 := by
    by_contra! h
    have hgt := lt_of_le_of_ne h hn.symm
    have strict : q ^ 24 < q ^ 25 := by
      rw [show q ^ 25 = q ^ 24 * q by ring]
      exact lt_mul_of_one_lt_right (pow_pos hq _) hgt
    nlinarith only [sq_nonneg (q ^ 12 - 1), equation, strict]
  have hneg : T < 0 := by
    rw [grid 0 (by decide), grid 1 (by decide)] at hi
    simp only [pow_zero, mul_one, pow_one] at hi
    have negD : D < 0 := by
      by_contra! h
      nlinarith only [hi, mul_nonneg h (sub_nonneg.mpr hlt.le)]
    exact mul_neg_of_neg_of_pos negD (pow_pos hq _)
  obtain ⟨hBC, hCA⟩ := calibrated_disutility_rankings ⟨hq, hlt⟩ equation
  rw [above 10 (by decide), above 25 (by decide), zero, above 5 (by decide), low]
  constructor
  · linarith only [mul_lt_mul_of_neg_left hCA hneg]
  · have h := mul_lt_mul_of_neg_left hBC hneg
    simp only [div_eq_mul_inv] at h ⊢
    linarith only [h]

/-- **Problem 6.2:** constant risk premia and the given certainty equivalent imply B ≻ C ≻ A
for every continuous, strictly increasing monetary prize index on the specified interval. -/
theorem problem_6_2_of_constant_premia {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ContinuousOn U CalibrationInterval) (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  obtain ⟨q, hq, b, hshift⟩ := calibration_shift_affine hi hc hC
  let G (n : ℕ) := U (-1000 + 200 * (n : ℝ))
  have step (n : ℕ) (hn : n < 30) : G (n + 1) = q * G n + b := by
    have hn' : (n : ℝ) ≤ 29 := by exact_mod_cast (show n ≤ 29 by omega)
    have h := hshift (-1000 + 200 * n) ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by linarith⟩
    dsimp [G]
    rw [← h, Nat.cast_add, Nat.cast_one]
    ring_nf
  have inc : G 0 < G 1 := by
    norm_num [G]
    exact hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  have cal : (G 30 + G 5) / 2 = G 17 := by
    norm_num [G]
    exact he
  have ranked := calibrated_grid_ranking G hq step inc cal
  norm_num [G] at ranked
  exact ranked

end Kreps.UtilityForMoney
