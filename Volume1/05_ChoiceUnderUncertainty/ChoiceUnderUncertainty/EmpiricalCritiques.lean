/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.FiniteLotteryTables
import ChoiceUnderUncertainty.ActSeparability
import Mathlib.Analysis.Real.Sqrt

/-!
# Framing, Allais, Ellsberg, portfolio effects and timing

Kreps I, Section 5.5, pp. 110–116. These results check the mathematical
implications of each experiment. A reported frequency of human choices is
empirical evidence. The portfolio comparison uses a constructed illustration.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- A binary cash lottery paying `x` and `y` at the specified odds. -/
noncomputable def BinaryCash (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (x y : ℝ) : SimpleLottery ℝ :=
  (TwoBranches a ha).lottery ![x, y]

/-- Value of the two cash prizes for an arbitrary numerical utility. -/
theorem binaryCash_expectedUtility (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (x y : ℝ) (U : ℝ → ℝ) :
    ExpectedUtility U (BinaryCash a ha x y) = a * U x + (1 - a) * U y := by
  rw [BinaryCash, expectedUtility_branchLottery]
  exact twoBranches_value a ha x y U

/-- Both the sure and the risky choices on p. 111 give exactly the same terminal cash laws. -/
theorem framing_cash_laws :
    PureLottery (400 : ℝ) = PureLottery (600 - 200 : ℝ) ∧
    BinaryCash (2 / 3) (by constructor <;> norm_num) 600 0 =
      BinaryCash (2 / 3) (by constructor <;> norm_num) (600 - 0) (600 - 600) := by
  norm_num

/-- Preferences on terminal monetary laws cannot reverse the two equivalent presentations. -/
theorem framing_no_strict_reversal (r : SimpleLottery ℝ → SimpleLottery ℝ → Prop) :
    ¬(Strict r (PureLottery 400) (BinaryCash (2 / 3) (by constructor <;> norm_num) 600 0) ∧
      Strict r (BinaryCash (2 / 3) (by constructor <;> norm_num) (600 - 0) (600 - 600))
        (PureLottery (600 - 200))) := by
  rw [← framing_cash_laws.1, ← framing_cash_laws.2]
  exact fun h => h.1.2 h.2.1

/-- The four Figure 5.9 lotteries in order `A`, `B`, `A'`, `B'`. -/
noncomputable def AllaisLotteries : Fin 4 → SimpleLottery ℝ :=
  ![(ThreeBranches (33 / 100) (66 / 100) (1 / 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).lottery ![27500, 24000, 0],
    PureLottery 24000, BinaryCash (33 / 100) (by constructor <;> norm_num) 27500 0,
    BinaryCash (34 / 100) (by constructor <;> norm_num) 24000 0]

/-- The two Allais comparisons have exactly the same expected-utility difference. -/
theorem allais_difference (U : ℝ → ℝ) :
    ExpectedUtility U (AllaisLotteries 0) - ExpectedUtility U (AllaisLotteries 1) =
    ExpectedUtility U (AllaisLotteries 2) - ExpectedUtility U (AllaisLotteries 3) := by
  simp [AllaisLotteries, expectedUtility_branchLottery, threeBranches_value, expectedUtility_pure,
    binaryCash_expectedUtility]
  ring

/-- The reported strict pair `B > A` and `A' > B'` excludes every expected utility. -/
theorem allais_no_expectedUtility : ¬∃ U : ℝ → ℝ,
    ExpectedUtility U (AllaisLotteries 1) > ExpectedUtility U (AllaisLotteries 0) ∧
    ExpectedUtility U (AllaisLotteries 2) > ExpectedUtility U (AllaisLotteries 3) := by
  rintro ⟨U, h, h'⟩
  linarith [allais_difference U]

/-- The Ellsberg acts on the red, blue and green states, in order `A`, `B`, `A'`, `B'`. -/
def EllsbergBets : Fin 4 → Fin 3 → ℝ :=
  ![![100, 0, 0], ![0, 100, 0], ![100, 0, 100], ![0, 100, 100]]

/-- For every possible blue count from zero to 200, this is the corresponding urn law. -/
noncomputable def EllsbergUrn (blue : ℕ) (h : blue ≤ 200) : BranchTable 3 :=
  ThreeBranches (1 / 3) (blue / 300) ((200 - (blue : ℝ)) / 300) (by norm_num)
    (by positivity) (by
      have h' : (blue : ℝ) ≤ 200 := by exact_mod_cast h
      linarith) (by ring)

/-- The known probabilities are one third for red and two thirds for blue or green. -/
theorem ellsberg_known_odds (blue : ℕ) (h : blue ≤ 200) :
    (EllsbergUrn blue h).mass 0 = 1 / 3 ∧
    (EllsbergUrn blue h).mass 1 + (EllsbergUrn blue h).mass 2 = 2 / 3 := by
  constructor <;> simp [EllsbergUrn, ThreeBranches]
  ring

/-- The two Ellsberg gaps coincide for arbitrary subjective probabilities and prize utility. -/
theorem ellsberg_difference (p : Fin 3 → ℝ) (U : ℝ → ℝ) :
    SubjectiveActValue p U (EllsbergBets 0) - SubjectiveActValue p U (EllsbergBets 1) =
    SubjectiveActValue p U (EllsbergBets 2) - SubjectiveActValue p U (EllsbergBets 3) := by
  simp [SubjectiveActValue, EllsbergBets, Fin.sum_univ_succ]
  ring

/-- The reported strict reversal excludes subjective expected utility for every assignment. -/
theorem ellsberg_no_subjectiveUtility : ¬∃ (p : Fin 3 → ℝ) (U : ℝ → ℝ),
    SubjectiveActValue p U (EllsbergBets 0) > SubjectiveActValue p U (EllsbergBets 1) ∧
    SubjectiveActValue p U (EllsbergBets 3) > SubjectiveActValue p U (EllsbergBets 2) := by
  rintro ⟨p, U, h, h'⟩
  linarith [ellsberg_difference p U]

/-- The Ellsberg reversal violates Savage's Sure-Thing Principle directly on acts. -/
theorem ellsberg_not_sureThing {r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop}
    (h : Strict r (EllsbergBets 0) (EllsbergBets 1))
    (h' : Strict r (EllsbergBets 3) (EllsbergBets 2)) : ¬SureThing r := by
  intro hS
  apply h'.2
  apply (hS {0, 1} (EllsbergBets 0) (EllsbergBets 2) (EllsbergBets 1) (EllsbergBets 3)
    (by intro s hs; fin_cases s <;> norm_num [EllsbergBets] at *)
    (by intro s hs; fin_cases s <;> norm_num [EllsbergBets] at *)).mp h.1

/-- Identical investment payoffs can be valued differently when combined with existing wealth. -/
theorem portfolio_dependence_example :
    ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) 0 100) =
      ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) 100 0) ∧
    ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) (0 + 100)
      (100 + 0)) > ExpectedUtility Real.sqrt
        (BinaryCash (1 / 2) (by constructor <;> norm_num) (0 + 0) (100 + 100)) := by
  have h : Real.sqrt 200 < 20 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  norm_num [binaryCash_expectedUtility]
  linarith

/-- The narrow terminal-prize model values each p. 115 timing variant by this same comparison. -/
theorem delayedCoin_value_iff (U : ℝ → ℝ) :
    ExpectedUtility U (PureLottery 20000) ≤ ExpectedUtility U
        (BinaryCash (1 / 2) (by constructor <;> norm_num) 100000 0) ↔
      2 * U 20000 ≤ U 100000 + U 0 := by
  rw [expectedUtility_pure, binaryCash_expectedUtility]
  constructor <;> intro h <;> linarith

/-- Coin offer with draw, disclosure and payment dates (months) and monetary consequences. -/
structure TimedCoinOffer where
  /-- Month of the actual coin toss. -/
  draw : ℕ
  /-- Month in which the consumer learns its outcome. -/
  disclosure : ℕ
  /-- Month in which the terminal amount is paid. -/
  payment : ℕ
  /-- Payoff after heads. -/
  heads : ℝ
  /-- Payoff after tails. -/
  tails : ℝ

/-- The three timing arrangements on p. 115 differ in when the fair toss occurs or is disclosed. -/
def PrintedCoinOffers : Fin 3 → TimedCoinOffer :=
  ![⟨0, 0, 12, 100000, 0⟩, ⟨12, 12, 12, 100000, 0⟩, ⟨0, 12, 12, 100000, 0⟩]

/-- All three contracts give the identical terminal law and comparison against the sure payment. -/
theorem printedCoinOffers_compare (i : Fin 3) (U : ℝ → ℝ) :
    let c := PrintedCoinOffers i
    ExpectedUtility U (PureLottery 20000) ≤ ExpectedUtility U
        (BinaryCash (1 / 2) (by constructor <;> norm_num) c.heads c.tails) ↔
      2 * U 20000 ≤ U 100000 + U 0 := by
  fin_cases i <;> exact delayedCoin_value_iff U

end Kreps.ChoiceUnderUncertainty
