/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.UtilityEquivalence

/-!
Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Utility transformation counterexamples

Kreps I, Problem 1.14c-d, p. 27. The jump at one prevents a globally strictly
increasing transformation. A bounded utility representing an unbounded one forces
an infinite value in any monotone extension to the entire real line.
-/

namespace Kreps.PreferenceProperties

/-- The piecewise utility in **Problem 1.14c**, including its stated value at one. -/
noncomputable def JumpUtility (x : ℝ) : ℝ := if x ≤ 1 then x else x + 1

/-- The jump preserves the usual strict order. -/
theorem jumpUtility_strictMono : StrictMono JumpUtility := by
  intro x y hxy
  unfold JumpUtility
  split_ifs <;> linarith

/-- On the nonnegative half-line, the jump utility represents the same preference as identity. -/
theorem jumpUtility_represents :
    Represents (fun x : Set.Ici (0 : ℝ) => JumpUtility x.val)
      (UtilityPref (fun x : Set.Ici (0 : ℝ) => x.val)) := by
  intro x y
  exact jumpUtility_strictMono.le_iff_le.symm

/-- **Problem 1.14c**: no everywhere strictly increasing transformation can undo the jump. -/
theorem problem_1_14c :
    ¬∃ f : ℝ → ℝ, StrictMono f ∧
      ∀ x : Set.Ici (0 : ℝ), x.val = f (JumpUtility x.val) := by
  rintro ⟨f, hf, heq⟩
  have h1 : f 1 = 1 := by
    simpa [JumpUtility] using (heq ⟨1, by norm_num⟩).symm
  have h2 : 1 < f 2 := by
    rw [← h1]
    exact hf (by norm_num)
  let t : ℝ := (1 + f 2) / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have hft : f (t + 1) = t := by
    simpa [JumpUtility, not_le.mpr ht] using
      (heq ⟨t, by change 0 ≤ t; linarith⟩).symm
  have hcontra : f 2 < t := by
    rw [← hft]
    exact hf (by linarith)
  dsimp [t] at hcontra
  linarith

/-- A bounded representation of the usual order on the nonnegative half-line. -/
noncomputable def FractionUtility (x : Set.Ici (0 : ℝ)) : ℝ := x.val / (x.val + 1)

/-- All values lie below the finite endpoint one. -/
theorem fractionUtility_lt_one (x : Set.Ici (0 : ℝ)) : FractionUtility x < 1 := by
  have hx : 0 ≤ x.val := x.property
  change x.val / (x.val + 1) < 1
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- The bounded utility has no negative values. -/
theorem fractionUtility_nonneg (x : Set.Ici (0 : ℝ)) : 0 ≤ FractionUtility x := by
  exact div_nonneg x.property (by have hx : 0 ≤ x.val := x.property; linarith)

/-- Bounded and unbounded utilities represent exactly the same relation. -/
theorem fractionUtility_represents :
    Represents FractionUtility (UtilityPref (fun x : Set.Ici (0 : ℝ) => x.val)) := by
  intro x y
  have hx : 0 ≤ x.val := x.property
  have hy : 0 ≤ y.val := y.property
  change y.val ≤ x.val ↔ y.val / (y.val + 1) ≤ x.val / (x.val + 1)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- The monotone extension really can require positive infinity at a finite argument. -/
theorem problem_1_14d_top :
    ExtendedUtilityTransform FractionUtility (fun x : Set.Ici (0 : ℝ) => x.val) 1 = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro y
  let x : Set.Ici (0 : ℝ) := ⟨max (y + 1) 0, le_max_right (y + 1) (0 : ℝ)⟩
  have hyx : y < x.val := by
    dsimp [x]
    have hm := le_max_left (y + 1) 0
    linarith
  exact (EReal.coe_lt_coe hyx).trans_le
    (le_sSup (show (x.val : EReal) ∈ {a : EReal | ∃ z : Set.Ici (0 : ℝ),
      FractionUtility z ≤ 1 ∧ a = (z.val : EReal)} from
        ⟨x, (fractionUtility_lt_one x).le, rfl⟩))

/-- Empty lower sections produce negative infinity in the book's supremum formula. -/
theorem problem_1_14d_bot :
    ExtendedUtilityTransform FractionUtility (fun x : Set.Ici (0 : ℝ) => x.val) (-1) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro a ⟨x, hx, _⟩
    have hnonneg := fractionUtility_nonneg x
    linarith
  · exact bot_le

/-- The positive-infinity example cannot be replaced by a real-valued monotone extension. -/
theorem problem_1_14d_no_real_extension :
    ¬∃ f : ℝ → ℝ, Monotone f ∧ ∀ x : Set.Ici (0 : ℝ), f (FractionUtility x) = x.val := by
  rintro ⟨f, hf, heq⟩
  let x : Set.Ici (0 : ℝ) := ⟨max (f 1 + 1) 0, le_max_right (f 1 + 1) (0 : ℝ)⟩
  have hle := hf (fractionUtility_lt_one x).le
  rw [heq x] at hle
  have hm := le_max_left (f 1 + 1) 0
  dsimp [x] at hle
  linarith

end Kreps.PreferenceProperties
