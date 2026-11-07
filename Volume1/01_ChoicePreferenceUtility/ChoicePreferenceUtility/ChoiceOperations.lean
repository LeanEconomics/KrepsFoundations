/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.FiniteUtility

/-!
# Joint choice, joint preference, and Sen's conditions

Kreps I, Problems 1.2-1.5, pp. 24-25. Unions preserve nonemptiness and completeness,
but can destroy coherence and transitivity. The joint pairwise relation still equals
the union of the individual revealed relations; its greatest elements can strictly
include joint choice. Sen's two conditions together characterize coherence.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*}

/-- Accept any alternative chosen by either decision maker. -/
def UnionChoice (c d : ChoiceRule X) : ChoiceRule X := fun A => c A ∪ d A

/-- Accept either individual's weak comparison. -/
def UnionPreference (r s : X → X → Prop) (x y : X) : Prop := r x y ∨ s x y

/-- The union of two feasible choice rules is feasible. -/
theorem unionChoice_feasible {c d : ChoiceRule X} (hc : Feasible c) (hd : Feasible d) :
    Feasible (UnionChoice c d) := by
  intro A x hx
  exact hx.elim (fun h => hc A h) (fun h => hd A h)

/-- **Problem 1.2**, nonemptiness: one nonempty constituent already suffices. -/
theorem problem_1_2_nonempty {c : ChoiceRule X} (hc : FiniteNonempty c) (d : ChoiceRule X) :
    FiniteNonempty (UnionChoice c d) := by
  intro A hfin hne
  obtain ⟨x, hx⟩ := hc A hfin hne
  exact ⟨x, Or.inl hx⟩

/-- **Problem 1.3**, completeness: one complete constituent already suffices. -/
theorem problem_1_3_complete {r : X → X → Prop} (hr : Complete r) (s : X → X → Prop) :
    Complete (UnionPreference r s) := by
  intro x y
  exact (hr x y).elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))

/-- **Problem 1.4**: the pairwise revealed relation of joint choice is the union relation. -/
theorem problem_1_4_revealed (c d : ChoiceRule X) :
    Revealed (UnionChoice c d) = UnionPreference (Revealed c) (Revealed d) := rfl

/-- **Problem 1.4**: individual greatest elements are also joint-relation greatest elements. -/
theorem problem_1_4_subset (r s : X → X → Prop) (A : Set X) :
    UnionChoice (PrefChoice r) (PrefChoice s) A ⊆ PrefChoice (UnionPreference r s) A := by
  rintro x (hx | hx)
  · exact ⟨hx.1, fun y hy => Or.inl (hx.2 y hy)⟩
  · exact ⟨hx.1, fun y hy => Or.inr (hx.2 y hy)⟩

/-- Larry ranks alternative one above two above zero. -/
def LarryUtility (x : Fin 3) : ℝ := if x = 1 then 2 else if x = 2 then 1 else 0

/-- Moe ranks alternative two above zero above one. -/
def MoeUtility (x : Fin 3) : ℝ := if x = 2 then 2 else if x = 0 then 1 else 0

/-- The full-menu joint choice contains one and two, but excludes zero. -/
theorem jointChoice_full :
    UnionChoice (UtilityChoice LarryUtility) (UtilityChoice MoeUtility) Set.univ = {1, 2} := by
  ext x
  fin_cases x <;>
    norm_num [UnionChoice, UtilityChoice, PrefChoice, UtilityPref,
      LarryUtility, MoeUtility, Fin.forall_fin_succ]

/-- The smaller menu now selects zero as well as one. -/
theorem jointChoice_pair :
    UnionChoice (UtilityChoice LarryUtility) (UtilityChoice MoeUtility) {0, 1} = {0, 1} := by
  ext x
  fin_cases x <;>
    norm_num [UnionChoice, UtilityChoice, PrefChoice, UtilityPref,
      LarryUtility, MoeUtility]

/-- **Problem 1.2**, coherence fails despite both individuals maximizing utility. -/
theorem problem_1_2_not_coherent :
    ¬Coherent (UnionChoice (UtilityChoice LarryUtility) (UtilityChoice MoeUtility)) := by
  intro hc
  apply hc Set.univ {0, 1} 1 (by simp) 0 (by simp)
  · rw [jointChoice_full]
    simp
  · rw [jointChoice_full]
    simp
  · rw [jointChoice_pair]
    simp

/-- **Problem 1.3**, joint weak preference can fail transitivity. -/
theorem problem_1_3_not_transitive :
    ¬TransitivePref (UnionPreference (UtilityPref LarryUtility) (UtilityPref MoeUtility)) := by
  intro ht
  have hab : UnionPreference (UtilityPref LarryUtility) (UtilityPref MoeUtility) 0 1 := by
    norm_num [UnionPreference, UtilityPref, LarryUtility, MoeUtility]
  have hbc : UnionPreference (UtilityPref LarryUtility) (UtilityPref MoeUtility) 1 2 := by
    norm_num [UnionPreference, UtilityPref, LarryUtility, MoeUtility]
  have hac := ht 0 1 2 hab hbc
  norm_num [UnionPreference, UtilityPref, LarryUtility, MoeUtility] at hac

/-- **Problem 1.4**: the reverse inclusion fails, even for individually rational preferences. -/
theorem problem_1_4_strict_subset :
    let r : Fin 3 → Fin 3 → Prop := UtilityPref (fun x => (x.val : ℝ))
    let s : Fin 3 → Fin 3 → Prop := UtilityPref (fun x => -(x.val : ℝ))
    UnionChoice (PrefChoice r) (PrefChoice s) Set.univ ⊂
      PrefChoice (UnionPreference r s) Set.univ := by
  dsimp only
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨problem_1_4_subset _ _ _, ?_⟩
  intro heq
  have hmem : (1 : Fin 3) ∈ PrefChoice
      (UnionPreference (UtilityPref (fun x : Fin 3 => (x.val : ℝ)))
        (UtilityPref (fun x : Fin 3 => -(x.val : ℝ)))) Set.univ := by
    refine ⟨Set.mem_univ _, fun y _ => ?_⟩
    rcases le_total (y.val : ℝ) ((1 : Fin 3).val : ℝ) with h | h
    · exact Or.inl h
    · exact Or.inr (neg_le_neg h)
  rw [← heq] at hmem
  rcases hmem with h | h
  · have hh := h.2 2 (Set.mem_univ _)
    norm_num [UtilityPref] at hh
  · have hh := h.2 0 (Set.mem_univ _)
    norm_num [UtilityPref] at hh

/-- Sen's contraction condition, alpha. -/
def SenAlpha (c : ChoiceRule X) : Prop :=
  ∀ A B, B ⊆ A → ∀ x ∈ c A, x ∈ B → x ∈ c B

/-- Sen's condition beta, in the formulation used on p. 25. -/
def SenBeta (c : ChoiceRule X) : Prop :=
  ∀ A B, B ⊆ A → ∀ x ∈ B, x ∈ c A → c B ⊆ c A

/-- Preference maximization satisfies contraction, even for an arbitrary relation. -/
theorem prefChoice_senAlpha (r : X → X → Prop) : SenAlpha (PrefChoice r) := by
  intro A B hsub x hx hxB
  exact ⟨hxB, fun y hy => hx.2 y (hsub hy)⟩

/-- Transitivity gives Sen's condition beta for preference maximization. -/
theorem prefChoice_senBeta {r : X → X → Prop} (ht : TransitivePref r) :
    SenBeta (PrefChoice r) := by
  intro A B hsub x hxB hxA y hyB
  exact ⟨hsub hyB.1, fun z hz => ht y x z (hyB.2 x hxB) (hxA.2 z hz)⟩

/-- Alpha and beta imply coherence, without a finiteness assumption. -/
theorem coherent_of_sen {c : ChoiceRule X} (ha : SenAlpha c) (hb : SenBeta c) :
    Coherent c := by
  intro A B x hx y hy hxA hyA hyB
  have hyI : y ∈ c (A ∩ B) := ha B (A ∩ B) Set.inter_subset_right y hyB hy
  exact hyA (hb A (A ∩ B) Set.inter_subset_left x hx hxA hyI)

/-- **Problem 1.5**: on a finite domain, the two Sen conditions characterize coherence. -/
theorem problem_1_5 [Finite X] {c : ChoiceRule X} (hf : Feasible c) (hn : FiniteNonempty c) :
    Coherent c ↔ SenAlpha c ∧ SenBeta c := by
  constructor
  · intro hc
    have ht := revealed_transitive hf hn hc
    rw [finite_choice_eq_revealed hf hn hc]
    exact ⟨prefChoice_senAlpha _, prefChoice_senBeta ht⟩
  · exact fun h => coherent_of_sen h.1 h.2

end Kreps.ChoicePreferenceUtility
