/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EmpiricalCritiques

/-!
# State-contingent examples and probability calibration

Kreps I, pp. 79–86, 106, 108–109 and Problem 5.2, p. 118. The horse race,
advertising decisions and weather-dependent prizes use the printed outcomes.
The World Cup comparisons identify subjective odds by comparison with roulette.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The three states are a Secretariat win, a Kelso win and a dead heat. -/
noncomputable def RaceOdds : BranchTable 3 :=
  ThreeBranches (59 / 100) (36 / 100) (5 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The two bets and abstention in Figure 5.3. A wager is returned on a tie. -/
noncomputable def RaceBet : Fin 3 → Fin 3 → ℝ := ![![6 / 5, -2, 0], ![-2, 3, 0], fun _ => 0]

/-- Figure 5.1 also includes a constant act giving three dollars regardless of the race. -/
theorem race_sure_three (U : ℝ → ℝ) :
    ExpectedUtility U (RaceOdds.lottery (fun _ => 3)) = U 3 := by
  simp [BranchTable.lottery, ExpectedUtility]

/-- The pushforward of the common state odds yields exactly the three Figure 5.4 lotteries. -/
theorem race_bet_values (U : ℝ → ℝ) :
    ExpectedUtility U (RaceOdds.lottery (RaceBet 0)) =
      59 / 100 * U (6 / 5) + 36 / 100 * U (-2) + 5 / 100 * U 0 ∧
    ExpectedUtility U (RaceOdds.lottery (RaceBet 1)) =
      59 / 100 * U (-2) + 36 / 100 * U 3 + 5 / 100 * U 0 ∧
    ExpectedUtility U (RaceOdds.lottery (RaceBet 2)) = U 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [expectedUtility_branchLottery, BranchTable.value,
    RaceOdds, RaceBet, ThreeBranches, Fin.sum_univ_succ] <;> ring

/-- Figure 5.2 has two distinct bundle prizes with odds one third and two thirds. -/
theorem bundle_lottery_values (U : (ℝ × ℝ) → ℝ) :
    ExpectedUtility U ((TwoBranches (1 / 3) (by constructor <;> norm_num)).lottery
      ![(10, 2), (4, 4)]) = 1 / 3 * U (10, 2) + 2 / 3 * U (4, 4) := by
  rw [expectedUtility_branchLottery]
  norm_num [BranchTable.value, TwoBranches, Fin.sum_univ_two]

/-- Changing the common dead-heat payout from minus one to two preserves the ranking. -/
theorem race_sureThing {r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop} (h : SureThing r) :
    r ![5, -2, -1] ![2, 2, -1] ↔ r ![5, -2, 2] ![2, 2, 2] := by
  apply h ({0, 1} : Set (Fin 3))
  · intro s hs
    fin_cases s <;> norm_num at *
  · intro s hs
    fin_cases s <;> norm_num at *

/-- A constructed meal utility: shrimp pairs with fruit and melon with cake on p. 82. -/
def MealContextUtility (m : Fin 3 → Bool) : ℝ := if m 0 = m 2 then 1 else 0

/-- The printed shrimp/steak versus melon/veal ranking reverses with the common dessert. -/
theorem meal_dessert_reversal :
    MealContextUtility ![true, true, true] > MealContextUtility ![false, false, true] ∧
    MealContextUtility ![true, true, false] < MealContextUtility ![false, false, false] := by
  norm_num [MealContextUtility]

/-- In the two-state sales model the advertising expense lowers profits in each state. -/
theorem advertising_two_states (U : Fin 2 → ℝ → ℝ) (hu : ∀ s, StrictMono (U s)) :
    StateAdditiveValue U ![-2000, 2000] < StateAdditiveValue U ![-1000, 3000] := by
  simp only [StateAdditiveValue, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_lt_add (hu 0 (by norm_num)) (hu 1 (by norm_num))

/-- The responsive state in the repaired sales model raises net profit by three thousand. -/
theorem advertising_three_states (p : BranchTable 3) :
    p.value ![-2000, 2000, 2000] id - p.value ![-1000, -1000, 3000] id =
      4000 * p.mass 1 - 1000 := by
  have h := p.normalized
  simp [Fin.sum_univ_succ] at h
  simp [BranchTable.value, Fin.sum_univ_succ]
  linarith

/-- Risk-neutral advertising is profitable precisely above one-quarter responsive probability. -/
theorem advertising_threshold (p : BranchTable 3) :
    p.value ![-1000, -1000, 3000] id < p.value ![-2000, 2000, 2000] id ↔ 1 / 4 < p.mass 1 := by
  constructor <;> intro h <;> linarith [advertising_three_states p]

/-- With equally likely rain and sun, state-independent utility ties the two prize swaps. -/
theorem umbrella_stateIndependent {X : Type*} (umbrella lotion : X) (U : X → ℝ) :
    SubjectiveActValue (fun _ : Fin 2 => 1 / 2) U ![umbrella, lotion] =
      SubjectiveActValue (fun _ : Fin 2 => 1 / 2) U ![lotion, umbrella] := by
  simp [SubjectiveActValue, Fin.sum_univ_two, add_comm]

/-- Opposite state-dependent rankings of the goods strictly favor the weather-matched act. -/
theorem umbrella_stateDependent {X : Type*} (umbrella lotion : X) (U : Fin 2 → X → ℝ)
    (hrain : U 0 lotion < U 0 umbrella) (hsun : U 1 umbrella < U 1 lotion) :
    StateAdditiveValue U ![lotion, umbrella] < StateAdditiveValue U ![umbrella, lotion] := by
  simpa [StateAdditiveValue, Fin.sum_univ_two] using add_lt_add hrain hsun

/-- A World Cup ticket pays one hundred dollars exactly on the specified winning region. -/
noncomputable def WorldCupTicket (i : Fin 3) (s : Fin 3) : ℝ := if s = i then 100 else 0

/-- A regional ticket has the value of a roulette at that region's subjective probability. -/
theorem worldCup_ticket_value (p : BranchTable 3) (U : ℝ → ℝ) (i : Fin 3) :
    p.value (WorldCupTicket i) U = p.mass i * U 100 + (1 - p.mass i) * U 0 := by
  have h := p.normalized
  simp [Fin.sum_univ_succ] at h
  fin_cases i <;> norm_num [BranchTable.value, WorldCupTicket, Fin.sum_univ_succ] <;>
    linear_combination (U 0) * h

/-- Figure 5.8's two strict comparisons calibrate the American and European probabilities. -/
theorem worldCup_thresholds (p : BranchTable 3) (U : ℝ → ℝ) (hu : U 0 < U 100) :
    (p.value (WorldCupTicket 1) U > ExpectedUtility U
        (BinaryCash (48 / 100) (by constructor <;> norm_num) 100 0) ∧
      ExpectedUtility U (BinaryCash (48 / 100) (by constructor <;> norm_num) 100 0) >
        p.value (WorldCupTicket 0) U) ↔ p.mass 1 > 48 / 100 ∧ 48 / 100 > p.mass 0 := by
  rw [worldCup_ticket_value, worldCup_ticket_value, binaryCash_expectedUtility]
  have h (a b : ℝ) :
      a * U 100 + (1 - a) * U 0 < b * U 100 + (1 - b) * U 0 ↔ a < b := by
    calc
      _ ↔ a * (U 100 - U 0) < b * (U 100 - U 0) := by constructor <;> intro h <;> linarith
      _ ↔ _ := mul_lt_mul_iff_left₀ (sub_pos.mpr hu)
  exact and_congr (h _ _) (h _ _)

/-- Indifference to a calibrated roulette recovers the winning-region probability exactly. -/
theorem worldCup_indifference (p : BranchTable 3) (U : ℝ → ℝ) (hu : U 0 < U 100)
    (i : Fin 3) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    p.value (WorldCupTicket i) U = ExpectedUtility U (BinaryCash a ha 100 0) ↔ p.mass i = a := by
  rw [worldCup_ticket_value, binaryCash_expectedUtility]
  constructor
  · intro h
    have hz : (p.mass i - a) * (U 100 - U 0) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hu.ne'))
  · rintro h
    rw [h]

/-- In Problem 5.2, assigning arbitrary positive state weights just rescales state utilities. -/
theorem weighted_stateUtilities_recover {S X : Type*} [Fintype S] (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (U : S → X → ℝ) (h : StateAct S X) :
    (∑ s, p s * (U s (h s) / p s)) = StateAdditiveValue U h := by
  unfold StateAdditiveValue
  apply Finset.sum_congr rfl
  intro s _
  field_simp [(hp s).ne']

/-- **Problem 5.2:** weighted state-dependent and additive state utility are equivalent. -/
theorem problem_5_2 {S X : Type*} [Fintype S] [Nonempty S]
    (r : StateAct S X → StateAct S X → Prop) :
    (∃ U : S → X → ℝ, Represents (StateAdditiveValue U) r) ↔
    ∃ (p : S → ℝ) (V : S → X → ℝ), (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
      Represents (fun h => ∑ s, p s * V s (h s)) r := by
  constructor
  · rintro ⟨U, hU⟩
    let p : S → ℝ := fun _ => (Fintype.card S : ℝ)⁻¹
    have hp : ∀ s, 0 < p s := fun s => inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
    refine ⟨p, fun s x => U s x / p s, fun s => (hp s).le, ?_, ?_⟩
    · simp [p, Fintype.card_ne_zero]
    · intro a b
      simpa only [weighted_stateUtilities_recover p hp] using hU a b
  · rintro ⟨p, V, _, _, h⟩
    exact ⟨fun s x => p s * V s x, h⟩

/-- Independently specified objective lotteries need not come from common horse-race odds. -/
theorem race_odds_not_imposed :
    ¬∃ p : BranchTable 3, p.lottery (RaceBet 0) = PureLottery (6 / 5) ∧
      p.lottery (RaceBet 1) = PureLottery 3 := by
  rintro ⟨p, h₁, h₂⟩
  have a := congrArg (ExpectedUtility (fun x : ℝ => if x = 6 / 5 then 1 else 0)) h₁
  have b := congrArg (ExpectedUtility (fun x : ℝ => if x = 3 then 1 else 0)) h₂
  norm_num [expectedUtility_branchLottery, expectedUtility_pure, BranchTable.value,
    RaceBet, Fin.sum_univ_succ] at a b
  have ht := p.normalized
  simp [Fin.sum_univ_succ] at ht
  linarith [p.nonnegative 2]

end Kreps.ChoiceUnderUncertainty
