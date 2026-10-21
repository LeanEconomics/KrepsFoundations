/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.CompactChoice
import ChoicePreferenceUtility.OrthantRepresentation
import ChoicePreferenceUtility.Lexicographic

/-!
# Infinite menus: nonattainment and deliberately empty choice

Kreps I, Section 1.6, pp. 15-16, and the necessity question in Problem 1.13.
The sum of two goods has no maximum on the square with its upper edges removed.
Separately, emptying a compact infinite menu preserves finite nonemptiness,
coherence and continuity of revealed preference, demonstrating the need for
Assumption 1.16 in Proposition 1.19.
-/

namespace Kreps.ChoicePreferenceUtility

/-- The semi-open unit square from p. 15, inside the nonnegative orthant. -/
def SemiOpenSquare : Set (NonnegativeOrthant 2) := {x | x.val 0 < 1 ∧ x.val 1 < 1}

/-- Sum utility for the two commodities. -/
def SumUtility (x : NonnegativeOrthant 2) : ℝ := x.val 0 + x.val 1

/-- The nonattainment example on p. 15: every candidate has a strictly better feasible bundle. -/
theorem semiOpenSquare_improvement {x : NonnegativeOrthant 2} (hx : x ∈ SemiOpenSquare) :
    ∃ y ∈ SemiOpenSquare, SumUtility x < SumUtility y := by
  let y : NonnegativeOrthant 2 :=
    ⟨fun i => if i = 0 then (x.val 0 + 1) / 2 else x.val i, by
      intro i
      change 0 ≤ if i = 0 then (x.val 0 + 1) / 2 else x.val i
      split_ifs
      · have h0 := x.property 0
        dsimp at h0
        linarith
      · exact x.property i⟩
  have hx0 : x.val 0 < 1 := hx.1
  have hx1 : x.val 1 < 1 := hx.2
  refine ⟨y, ?_, ?_⟩
  · constructor
    · dsimp [y]
      linarith
    · simpa [y] using hx1
  · dsimp [SumUtility, y]
    norm_num
    linarith

/-- Utility maximization on this nonempty infinite menu yields empty choice. -/
theorem semiOpenSquare_empty_choice : UtilityChoice SumUtility SemiOpenSquare = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy, hbetter⟩ := semiOpenSquare_improvement hx.1
  exact (not_le_of_gt hbetter) (hx.2 y hy)

/-- Emptying one infinite menu does not change the pairwise relation of constant utility. -/
theorem empty_constant_revealed {X : Type*} (A : Set X) (hA : A.Infinite) :
    Revealed (EmptyMenus (UtilityChoice (fun _ : X => (0 : ℝ))) {A}) = fun _ _ => True := by
  funext x y
  apply propext
  have hp : ({x, y} : Set X) ≠ A := by
    intro heq
    apply hA
    rw [← heq]
    simp
  simp [Revealed, EmptyMenus, hp, UtilityChoice, PrefChoice, UtilityPref]

/-- All standard conditions except Assumption 1.16 survive emptying the selected infinite menu. -/
theorem empty_constant_choice_properties {X : Type*} [TopologicalSpace X]
    (A : Set X) (hA : A.Infinite) :
    let c := EmptyMenus (UtilityChoice (fun _ : X => (0 : ℝ))) {A}
    Feasible c ∧ FiniteNonempty c ∧ Coherent c ∧ ContinuousPreference (Revealed c) ∧
      c A = ∅ ∧ ¬Assumption116 c := by
  dsimp only
  have hf := emptyMenus_feasible (prefChoice_feasible (UtilityPref (fun _ : X => (0 : ℝ)))) {A}
  have hE : ∀ B ∈ ({A} : Set (Set X)), ¬B.Finite := by
    intro B hB
    have hBA := Set.mem_singleton_iff.mp hB
    subst B
    exact hA
  have hn := emptyMenus_finiteNonempty (proposition_1_3b (fun _ : X => (0 : ℝ))).1 hE
  have hco := emptyMenus_coherent (proposition_1_3b (fun _ : X => (0 : ℝ))).2 {A}
  have hempty : EmptyMenus (UtilityChoice (fun _ : X => (0 : ℝ))) {A} A = ∅ := by
    simp [EmptyMenus]
  refine ⟨hf, hn, hco, ?_, hempty, ?_⟩
  · rw [empty_constant_revealed A hA]
    simp [ContinuousPreference, Strict]
  · intro ha
    obtain ⟨x, hx⟩ := hA.nonempty
    have hne := ha A x hx (by
      rw [empty_constant_revealed A hA]
      intro y _
      trivial)
    rw [hempty] at hne
    exact Set.not_nonempty_empty hne

/-- Embed the unit interval as a compact menu of one-good bundles. -/
def OrthantSegment (t : UnitSegment) : NonnegativeOrthant 1 :=
  ⟨fun _ => t.val, fun _ => t.property.1⟩

/-- The embedding is continuous. -/
theorem orthantSegment_continuous : Continuous OrthantSegment :=
  (continuous_pi fun _ => continuous_subtype_val).subtype_mk _

/-- The embedded menu is compact. -/
theorem orthantSegment_compact : IsCompact (Set.range OrthantSegment) := by
  let : CompactSpace UnitSegment := isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_range orthantSegment_continuous

/-- The embedded menu is infinite, by uncountability of the real interval. -/
theorem orthantSegment_infinite : (Set.range OrthantSegment).Infinite := by
  intro hfin
  let : Countable (Set.range OrthantSegment) := hfin.countable.to_subtype
  let f : UnitSegment → Set.range OrthantSegment := fun t => ⟨OrthantSegment t, ⟨t, rfl⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun p : Set.range OrthantSegment => p.val.val 0) h
  have hcount : Countable UnitSegment := hf.countable
  have hset : (Set.Icc (0 : ℝ) 1).Countable := hcount
  have hbad := Cardinal.Real.Icc_countable_iff.mp hset
  norm_num at hbad

/-- **Problem 1.13**: Assumption 1.16 is necessary even on the one-good nonnegative orthant. -/
theorem problem_1_13_necessity :
    ∃ (c : ChoiceRule (NonnegativeOrthant 1)) (A : Set (NonnegativeOrthant 1)),
      Feasible c ∧ FiniteNonempty c ∧ Coherent c ∧ ContinuousPreference (Revealed c) ∧
        IsCompact A ∧ A.Nonempty ∧ c A = ∅ ∧ ¬Assumption116 c := by
  refine ⟨EmptyMenus (UtilityChoice (fun _ => (0 : ℝ))) {Set.range OrthantSegment},
    Set.range OrthantSegment, ?_⟩
  obtain ⟨hf, hn, hco, hc, he, ha⟩ :=
    empty_constant_choice_properties (Set.range OrthantSegment) orthantSegment_infinite
  exact ⟨hf, hn, hco, hc, orthantSegment_compact, orthantSegment_infinite.nonempty, he, ha⟩

end Kreps.ChoicePreferenceUtility
