/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixContinuousFunctions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Appendix 2: bounds and extrema

Definition A2.19 and Propositions A2.20–A2.21, pp. 448–450. Real suprema and
infima have explicit nonemptiness and boundedness hypotheses. Extended-real
suprema and infima implement the book's infinite and empty-set conventions.
-/

namespace Kreps.PreferenceProperties

/-- **Definition A2.19(a):** upper and lower bounds on a real set. -/
theorem definition_A2_19a (S : Set ℝ) :
    (BddAbove S ↔ ∃ M, ∀ x ∈ S, x ≤ M) ∧
      (BddBelow S ↔ ∃ m, ∀ x ∈ S, m ≤ x) := ⟨Iff.rfl, Iff.rfl⟩

/-- **Definition A2.19(b):** the real supremum is the least upper bound. -/
theorem definition_A2_19b {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    IsLUB S (sSup S) := isLUB_csSup hne hb

/-- **Definition A2.19(c):** the real infimum is the greatest lower bound. -/
theorem definition_A2_19c {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) :
    IsGLB S (sInf S) := isGLB_csInf hne hb

/-- **Definition A2.19(d):** a supremum belonging to the set is its maximum. -/
theorem definition_A2_19d_max {S : Set ℝ} (hb : BddAbove S) (hmem : sSup S ∈ S) :
    IsGreatest S (sSup S) := ⟨hmem, fun _ hx => le_csSup hb hx⟩

/-- **Definition A2.19(d):** an infimum belonging to the set is its minimum. -/
theorem definition_A2_19d_min {S : Set ℝ} (hb : BddBelow S) (hmem : sInf S ∈ S) :
    IsLeast S (sInf S) := ⟨hmem, fun _ hx => csInf_le hb hx⟩

/-- A nonempty bounded-above real set has the same supremum after embedding into extended reals. -/
theorem appendix2_extended_sup_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun x : ℝ => (x : EReal)) '' S) = ((sSup S : ℝ) : EReal) := by
  apply (isLUB_sSup _).unique
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe (le_csSup hb hx)
  · intro z hz
    induction z using EReal.rec with
    | bot =>
      obtain ⟨x, hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe x)) (hz ⟨x, hx, rfl⟩))
    | coe r =>
      exact EReal.coe_le_coe (csSup_le hne fun x hx =>
        EReal.coe_le_coe_iff.mp (hz ⟨x, hx, rfl⟩))
    | top => exact le_top

/-- The corresponding finite infimum agrees with the extended-real infimum. -/
theorem appendix2_extended_inf_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) = ((sInf S : ℝ) : EReal) := by
  apply (isGLB_sInf _).unique
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe (csInf_le hb hx)
  · intro z hz
    induction z using EReal.rec with
    | bot => exact bot_le
    | coe r =>
      exact EReal.coe_le_coe (le_csInf hne fun x hx =>
        EReal.coe_le_coe_iff.mp (hz ⟨x, hx, rfl⟩))
    | top =>
      obtain ⟨x, hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.coe_lt_top x)) (hz ⟨x, hx, rfl⟩))

/-- **Definition A2.19(b):** unboundedness above gives positive infinity. -/
theorem appendix2_extended_sup_unbounded {S : Set ℝ} (hS : ¬BddAbove S) :
    sSup ((fun x : ℝ => (x : EReal)) '' S) = ⊤ := by
  by_contra h
  apply hS
  refine ⟨(sSup ((fun x : ℝ => (x : EReal)) '' S)).toReal, fun x hx => ?_⟩
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.mp ((le_sSup hx').trans (EReal.le_coe_toReal h))

/-- **Definition A2.19(c):** unboundedness below gives negative infinity. -/
theorem appendix2_extended_inf_unbounded {S : Set ℝ} (hS : ¬BddBelow S) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) = ⊥ := by
  by_contra h
  apply hS
  refine ⟨(sInf ((fun x : ℝ => (x : EReal)) '' S)).toReal, fun x hx => ?_⟩
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.mp ((EReal.coe_toReal_le h).trans (sInf_le hx'))

/-- **Proposition A2.20(a):** the extended infimum is at most the supremum for a nonempty set. -/
theorem proposition_A2_20a {S : Set ℝ} (hne : S.Nonempty) :
    sInf ((fun x : ℝ => (x : EReal)) '' S) ≤
      sSup ((fun x : ℝ => (x : EReal)) '' S) := by
  obtain ⟨x, hx⟩ := hne
  have hx' : (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' S := ⟨x, hx, rfl⟩
  exact (sInf_le hx').trans (le_sSup hx')

/-- **Proposition A2.20(b):** boundedness gives finite extended extrema on a nonempty real set. -/
theorem proposition_A2_20b {S : Set ℝ} (hne : S.Nonempty) :
    (BddAbove S → ∃ r : ℝ, sSup ((fun x : ℝ => (x : EReal)) '' S) = r) ∧
      (BddBelow S → ∃ r : ℝ, sInf ((fun x : ℝ => (x : EReal)) '' S) = r) :=
  ⟨fun h => ⟨sSup S, appendix2_extended_sup_finite hne h⟩,
    fun h => ⟨sInf S, appendix2_extended_inf_finite hne h⟩⟩

/-- **Proposition A2.20(c):** a nonempty compact real set has a maximum and a minimum. -/
theorem proposition_A2_20c {S : Set ℝ} (hne : S.Nonempty) (hS : IsCompact S) :
    IsGreatest S (sSup S) ∧ IsLeast S (sInf S) :=
  ⟨hS.isGreatest_sSup hne, hS.isLeast_sInf hne⟩

/-- The explicit empty-set conventions immediately following Proposition A2.20. -/
theorem appendix2_empty_extrema :
    sSup (∅ : Set EReal) = ⊥ ∧ sInf (∅ : Set EReal) = ⊤ := ⟨sSup_empty, sInf_empty⟩

/-- **Proposition A2.21:** a continuous function attains its finite supremum on a compact set. -/
theorem proposition_A2_21 {X : Type*} [TopologicalSpace X] {S : Set X} {f : X → ℝ}
    (hS : IsCompact S) (hne : S.Nonempty) (hf : ContinuousOn f S) :
    BddAbove (f '' S) ∧ ∃ x ∈ S, f x = sSup (f '' S) ∧ ∀ y ∈ S, f y ≤ f x := by
  obtain ⟨x, hx, heq, hmax⟩ := hS.exists_sSup_image_eq_and_ge hne hf
  exact ⟨hS.bddAbove_image hf, x, hx, heq.symm, hmax⟩

end Kreps.PreferenceProperties
