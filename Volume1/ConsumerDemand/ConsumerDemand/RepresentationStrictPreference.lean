/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationBasic

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

Local prerequisite copy from Chapter 1, commit dfb548d. Only the project namespace
and imports are changed; mathematical statements and proofs are preserved.

# Strict preference and indifference

Kreps I, §1.4, Propositions 1.9-1.10, pp. 9-10, and Problem 1.9, p. 26.
The two presentations of rational preference are equivalent: complete, transitive
weak preference, or asymmetric, negatively transitive strict preference.
-/

namespace Kreps.ConsumerDemand.Representation

variable {X : Type*} {r : X → X → Prop}

/-- A strict preference cannot run both ways. -/
def AsymmetricPref (s : X → X → Prop) : Prop := ∀ x y, s x y → ¬s y x

/-- The book's disjunctive formulation of negative transitivity. -/
def NegativelyTransitive (s : X → X → Prop) : Prop :=
  ∀ x y z, s x y → s z y ∨ s x z

/-- Recover weak preference by denying the reversed strict preference. -/
def WeakFromStrict (s : X → X → Prop) (x y : X) : Prop := ¬s y x

/-- Recover indifference when neither strict comparison holds. -/
def IndifferenceFromStrict (s : X → X → Prop) (x y : X) : Prop :=
  ¬s x y ∧ ¬s y x

/-- **Proposition 1.9a**, p. 9. -/
theorem proposition_1_9a (hc : Complete r) (x y : X) : Strict r x y ↔ ¬r y x :=
  ⟨And.right, fun h => ⟨(hc x y).resolve_right h, h⟩⟩

/-- **Proposition 1.9b**, p. 9. No completeness assumption is needed. -/
theorem proposition_1_9b (r : X → X → Prop) : AsymmetricPref (Strict r) :=
  fun _ _ hxy hyx => hxy.2 hyx.1

/-- First half of **Proposition 1.9g**, p. 9. -/
theorem strict_weak_trans (ht : TransitivePref r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨ht x y z hxy.1 hyz, fun hzx => hxy.2 (ht y z x hyz hzx)⟩

/-- Second half of **Proposition 1.9g**, p. 9. -/
theorem weak_strict_trans (ht : TransitivePref r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨ht x y z hxy hyz.1, fun hzx => hyz.2 (ht z x y hzx hxy)⟩

/-- **Proposition 1.9c**, p. 9. -/
theorem proposition_1_9c (hr : Rational r) : NegativelyTransitive (Strict r) := by
  intro x y z hxy
  by_cases hzy : Strict r z y
  · exact Or.inl hzy
  · right
    have hyz : r y z := by
      by_contra h
      exact hzy ((proposition_1_9a hr.1 z y).mpr h)
    exact strict_weak_trans hr.2 hxy hyz

/-- **Proposition 1.9d**, p. 9: reflexivity of indifference. -/
theorem proposition_1_9d (hc : Complete r) (x : X) : Indifferent r x x :=
  ⟨complete_refl hc x, complete_refl hc x⟩

/-- **Proposition 1.9e**, p. 9: symmetry of indifference. -/
theorem proposition_1_9e {x y : X} (hxy : Indifferent r x y) : Indifferent r y x :=
  ⟨hxy.2, hxy.1⟩

/-- **Proposition 1.9f**, p. 9: transitivity of indifference. -/
theorem proposition_1_9f (ht : TransitivePref r) {x y z : X}
    (hxy : Indifferent r x y) (hyz : Indifferent r y z) : Indifferent r x z :=
  ⟨ht x y z hxy.1 hyz.1, ht z y x hyz.2 hxy.2⟩

/-- **Proposition 1.9g**, p. 9: both mixed transitivity statements. -/
theorem proposition_1_9g (ht : TransitivePref r) (x y z : X) :
    (Strict r x y → r y z → Strict r x z) ∧
      (r x y → Strict r y z → Strict r x z) :=
  ⟨fun hxy hyz => strict_weak_trans ht hxy hyz,
    fun hxy hyz => weak_strict_trans ht hxy hyz⟩

/-- **Proposition 1.9h**, p. 9: transitivity of strict preference. -/
theorem proposition_1_9h (ht : TransitivePref r) : TransitivePref (Strict r) :=
  fun _ _ _ hxy hyz => strict_weak_trans ht hxy hyz.1

/-- **Proposition 1.10**, p. 10: reconstruction, including both recovered relations. -/
theorem proposition_1_10 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    by_cases h : s y x
    · exact Or.inr (ha y x h)
    · exact Or.inl h
  · intro x y z hxy hyz hzx
    exact (hn z x y hzx).elim hxy hyz
  · funext x y
    apply propext
    change (¬s y x ∧ ¬¬s x y) ↔ s x y
    exact ⟨fun h => not_not.mp h.2, fun h => ⟨ha x y h, not_not.mpr h⟩⟩
  · funext x y
    exact propext and_comm

/-- **Problem 1.9**, p. 26: the reconstructed weak relation is complete and transitive. -/
theorem problem_1_9 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s :=
  proposition_1_10 ha hn

end Kreps.ConsumerDemand.Representation
