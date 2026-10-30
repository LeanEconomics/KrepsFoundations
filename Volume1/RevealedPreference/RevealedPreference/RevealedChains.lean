/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Max

/-!
# Revealed comparison chains and GARP

Kreps I, Definition 4.2, p. 70. A cost matrix entry is expenditure on one observed
bundle at another observation's prices minus that observation's income. Weak
edges have nonpositive cost; strict edges have negative cost. A strict revealed
chain has at least one strict edge and any finite number of weak edges on either
side. The empty weak chain is harmless on feasible data, whose diagonal is already
a direct weak comparison. No budget-exhaustion condition is built into GARP.
-/

namespace Kreps.RevealedPreference

variable {I : Type*}

/-- Direct weak revealed preference in a cost-minus-income matrix. -/
def DirectWeak (C : I → I → ℝ) (i j : I) : Prop := C i j ≤ 0

/-- Direct strict revealed preference uses a strict budget slack. -/
def DirectStrict (C : I → I → ℝ) (i j : I) : Prop := C i j < 0

/-- A finite chain of weak direct comparisons, including the reflexive chain. -/
def RevealedWeak (C : I → I → ℝ) : I → I → Prop :=
  Relation.ReflTransGen (DirectWeak C)

/-- A weak chain with at least one direct strict step. -/
def RevealedStrict (C : I → I → ℝ) (i j : I) : Prop :=
  ∃ a b, RevealedWeak C i a ∧ DirectStrict C a b ∧ RevealedWeak C b j

/-- **Definition 4.2c:** no revealed strict cycle occurs. -/
def MatrixGARP (C : I → I → ℝ) : Prop := ∀ i, ¬RevealedStrict C i i

/-- A direct weak comparison is a one-step revealed weak chain. -/
theorem directWeak_revealedWeak {C : I → I → ℝ} {i j : I}
    (h : DirectWeak C i j) : RevealedWeak C i j := Relation.ReflTransGen.single h

/-- A direct strict comparison is a revealed strict chain with no intervening edges. -/
theorem directStrict_revealedStrict {C : I → I → ℝ} {i j : I}
    (h : DirectStrict C i j) : RevealedStrict C i j :=
  ⟨i, j, .refl, h, .refl⟩

/-- Every strict revealed chain is also a weak revealed chain. -/
theorem revealedStrict_weak {C : I → I → ℝ} {i j : I}
    (h : RevealedStrict C i j) : RevealedWeak C i j := by
  obtain ⟨a, b, hia, hab, hbj⟩ := h
  exact hia.trans ((directWeak_revealedWeak hab.le).trans hbj)

/-- Prefixing a weak chain preserves the strict edge later in the chain. -/
theorem revealedWeak_strict_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedWeak C i j) (hjl : RevealedStrict C j l) : RevealedStrict C i l := by
  obtain ⟨a, b, hja, hab, hbl⟩ := hjl
  exact ⟨a, b, hij.trans hja, hab, hbl⟩

/-- Appending a weak chain preserves an earlier strict edge. -/
theorem revealedStrict_weak_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedStrict C i j) (hjl : RevealedWeak C j l) : RevealedStrict C i l := by
  obtain ⟨a, b, hia, hab, hbj⟩ := hij
  exact ⟨a, b, hia, hab, hbj.trans hjl⟩

/-- Two strict revealed chains concatenate to a strict chain. -/
theorem revealedStrict_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedStrict C i j) (hjl : RevealedStrict C j l) : RevealedStrict C i l :=
  revealedStrict_weak_trans hij (revealedStrict_weak hjl)

/-- GARP forbids a weak chain returning against a strict revealed chain. -/
theorem matrixGARP_no_reverse {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedWeak C i j) : ¬RevealedStrict C j i :=
  fun hji => hG i (revealedWeak_strict_trans hij hji)

/-- The usual GARP criterion compares a weak chain with the cost of its closing edge. -/
theorem matrixGARP_iff_return_cost (C : I → I → ℝ) :
    MatrixGARP C ↔ ∀ i j, RevealedWeak C i j → 0 ≤ C j i := by
  constructor
  · intro hG i j hij
    exact le_of_not_gt (fun hji => matrixGARP_no_reverse hG hij
      (directStrict_revealedStrict hji))
  · intro h i hi
    obtain ⟨a, b, hia, hab, hbi⟩ := hi
    exact (not_lt_of_ge (h b a (hbi.trans hia))) hab

/-- GARP and feasibility force budget exhaustion, rather than assuming it. -/
theorem matrixGARP_diagonal_zero {C : I → I → ℝ} (hG : MatrixGARP C)
    (hf : ∀ i, C i i ≤ 0) (i : I) : C i i = 0 := by
  exact le_antisymm (hf i) ((matrixGARP_iff_return_cost C).mp hG i i .refl)

/-- A choice with positive budget slack violates GARP by a one-edge self-cycle. -/
theorem negative_diagonal_not_matrixGARP {C : I → I → ℝ} {i : I} (hi : C i i < 0) :
    ¬MatrixGARP C := fun hG => hG i (directStrict_revealedStrict hi)

/-- A numeric certificate increasing weakly along revealed comparisons excludes all cycles. -/
theorem matrixGARP_of_scores {C : I → I → ℝ} (v : I → ℝ)
    (hw : ∀ i j, DirectWeak C i j → v j ≤ v i)
    (hs : ∀ i j, DirectStrict C i j → v j < v i) : MatrixGARP C := by
  have hchain {i j : I} (h : RevealedWeak C i j) : v j ≤ v i := by
    induction h with
    | refl => exact le_rfl
    | @tail j l _ hjl ih => exact (hw j l hjl).trans ih
  intro i hi
  obtain ⟨a, b, hia, hab, hbi⟩ := hi
  have hlt : v i < v i := (hchain hbi).trans_lt ((hs a b hab).trans_le (hchain hia))
  exact lt_irrefl _ hlt

end Kreps.RevealedPreference
