/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.UtilityEquivalence
import ChoicePreferenceUtility.PartialPreference
import ChoicePreferenceUtility.OrthantRepresentation

/-!
# Mathematical content of the chapter's commentary

Kreps I, pp. 2, 18-23. These are mathematical statements about budget menus,
ordinal transformations,
the equality of the two vaccination frames, a menu reversal, and rejected sets.
Empirical claims about responses and normative discussions are not mathematical
hypotheses of these results; their source coverage is recorded separately.
-/

namespace Kreps.ChoicePreferenceUtility

/-- The strictly positive price vectors in the consumer example on p. 2. -/
def StrictlyPositiveOrthant (k : ℕ) := {p : Fin k → ℝ // ∀ j, 0 < p j}

/-- The affordable bundles at a price vector and income, as defined on p. 2. -/
def BudgetMenu {k : ℕ} (p : StrictlyPositiveOrthant k) (income : ℝ) :
    Set (NonnegativeOrthant k) := {x | ∑ j, p.val j * x.val j ≤ income}

/-- Nonnegative income makes this an admissible nonempty menu: the zero bundle is affordable. -/
theorem budgetMenu_nonempty {k : ℕ} (p : StrictlyPositiveOrthant k) {income : ℝ}
    (hincome : 0 ≤ income) : (BudgetMenu p income).Nonempty := by
  refine ⟨⟨0, le_rfl⟩, ?_⟩
  change (∑ j, p.val j * 0) ≤ income
  simpa using hincome

/-- The three-good illustrative bundle: three bread, zero cheese, and half a salami. -/
noncomputable def BreadCheeseSalamiBundle : NonnegativeOrthant 3 :=
  ⟨fun j => if j = 0 then 3 else if j = 1 then 0 else 1 / 2,
    fun j => by dsimp; split_ifs <;> norm_num⟩

/-- A strictly increasing transformation with different slopes above and below one. -/
noncomputable def OrdinalWarp (t : ℝ) : ℝ := if t ≤ 1 then 3 * t else t + 2

/-- The example transformation preserves every strict utility comparison. -/
theorem ordinalWarp_strictMono : StrictMono OrdinalWarp := by
  intro x y hxy
  unfold OrdinalWarp
  split_ifs <;> linarith

/-- Three alternatives with utility levels three, one and zero. -/
def OrdinalExampleUtility (x : Fin 3) : ℝ := if x = 0 then 3 else if x = 1 then 1 else 0

/-- The point made on p. 18: comparison of utility differences is not ordinally invariant. -/
theorem ordinal_difference_reversal :
    Represents (OrdinalWarp ∘ OrdinalExampleUtility) (UtilityPref OrdinalExampleUtility) ∧
      OrdinalExampleUtility 0 - OrdinalExampleUtility 1 >
        OrdinalExampleUtility 1 - OrdinalExampleUtility 2 ∧
      OrdinalWarp (OrdinalExampleUtility 0) - OrdinalWarp (OrdinalExampleUtility 1) <
        OrdinalWarp (OrdinalExampleUtility 1) - OrdinalWarp (OrdinalExampleUtility 2) := by
  refine ⟨proposition_1_20 (fun _ _ => Iff.rfl) ordinalWarp_strictMono, ?_⟩
  norm_num [OrdinalExampleUtility, OrdinalWarp]

/-- The sign relative to zero also has no invariant meaning for ordinal utility. -/
theorem ordinal_zero_not_invariant :
    Represents (fun x => OrdinalExampleUtility x - 2) (UtilityPref OrdinalExampleUtility) ∧
      0 < OrdinalExampleUtility 1 ∧ OrdinalExampleUtility 1 - 2 < 0 := by
  refine ⟨proposition_1_20 (fun _ _ => Iff.rfl) (show StrictMono (fun t : ℝ => t - 2) from
    fun _ _ h => sub_lt_sub_right h 2), ?_⟩
  norm_num [OrdinalExampleUtility]

/-- Probabilities of the two states in the framing example. -/
def FluProbability (b : Bool) : ℚ := if b then 2 / 3 else 1 / 3

/-- The common state probabilities are nonnegative and sum to one. -/
theorem fluProbability_valid :
    (∀ b, 0 ≤ FluProbability b) ∧ FluProbability false + FluProbability true = 1 := by
  constructor
  · intro b
    cases b <;> norm_num [FluProbability]
  · norm_num [FluProbability]

/-- Program A, expressed as lives saved. -/
def SavedProgramA (_ : Bool) : ℕ := 400

/-- Program B, expressed as lives saved in the two states. -/
def SavedProgramB (b : Bool) : ℕ := if b then 600 else 0

/-- Program X, expressed as deaths. -/
def DeathProgramX (_ : Bool) : ℕ := 200

/-- Program Y, expressed as deaths in the same two states. -/
def DeathProgramY (b : Bool) : ℕ := if b then 0 else 600

/-- Put a deaths description into the common lives-saved outcome space. -/
def LivesSavedFromDeaths (d : Bool → ℕ) (b : Bool) : ℕ := 600 - d b

/-- Programs A and X have exactly the same outcome in each state. -/
theorem framing_A_eq_X : SavedProgramA = LivesSavedFromDeaths DeathProgramX := by
  funext b
  norm_num [SavedProgramA, LivesSavedFromDeaths, DeathProgramX]

/-- Programs B and Y have exactly the same state-contingent outcomes and probabilities. -/
theorem framing_B_eq_Y : SavedProgramB = LivesSavedFromDeaths DeathProgramY := by
  funext b
  cases b <;> norm_num [SavedProgramB, LivesSavedFromDeaths, DeathProgramY]

/-- Opposite strict rankings of these identical outcomes cannot come from one weak relation. -/
theorem framing_reversal_impossible (r : (Bool → ℕ) → (Bool → ℕ) → Prop) :
    ¬(Strict r SavedProgramA SavedProgramB ∧
      Strict r (LivesSavedFromDeaths DeathProgramY) (LivesSavedFromDeaths DeathProgramX)) := by
  rw [← framing_A_eq_X, ← framing_B_eq_Y]
  exact fun h => h.1.2 h.2.1

/-- The apple/cherry/peach example on pp. 2, 20 directly violates coherence. -/
theorem added_option_reversal_not_coherent {X : Type*} {c : ChoiceRule X} {x y z : X}
    (hx : x ∈ c {x, y}) (hy : y ∉ c {x, y}) (hy' : y ∈ c {x, y, z}) : ¬Coherent c := by
  intro hc
  exact hc {x, y} {x, y, z} x (by simp) y (by simp) hx hy hy'

/-- The rejected-set function described on p. 21. -/
def RejectedSet {X : Type*} (s : X → X → Prop) (A : Set X) : Set X :=
  {y | y ∈ A ∧ ∃ x ∈ A, s x y}

/-- Rejection concerns only alternatives actually in the menu. -/
theorem rejectedSet_subset {X : Type*} (s : X → X → Prop) (A : Set X) :
    RejectedSet s A ⊆ A := fun _ h => h.1

/-- The four responses on p. 21 are exhaustive, including the explicit inability to compare. -/
theorem partial_response_exhaustive {X : Type*} (s i : X → X → Prop) (x y : X) :
    s x y ∨ s y x ∨ i x y ∨ (¬s x y ∧ ¬s y x ∧ ¬i x y) := by
  tauto

/-- Under the partial-preference conditions, the three positive responses cannot conflict. -/
theorem partial_positive_responses_exclusive {X : Type*} {s i : X → X → Prop}
    (h : PartialPreferenceAxioms s i) (x y : X) :
    (s x y → ¬s y x ∧ ¬i x y) ∧ (s y x → ¬i x y) :=
  ⟨fun hxy => ⟨h.strict_asymm x y hxy, (problem_1_17a h hxy).2⟩,
    fun hyx => (problem_1_17a h hyx).1⟩

end Kreps.ChoicePreferenceUtility
