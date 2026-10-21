/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.RevealedPreference
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Extension.Linear

/-!
# SGARP and rationalization

Kreps I, Definition 1.22 and Proposition 1.23 inside Problem 1.16c, p. 28.
The observed strict relation includes the feasible-menu condition explained in
`RevealedPreference` and `docs/corrections.md`. Choice observations are feasible and
nonempty. We prove the theorem for an arbitrary indexed family, hence in particular
the finite family in the book. The construction closes weak revealed preference,
identifies mutually reachable alternatives, and linearly extends the quotient order.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X I : Type*} {menus chosen : I → Set X}

/-- **Definition 1.22**: no finite weak chain is contradicted by a strict revealed comparison. -/
def SGARP (menus chosen : I → Set X) : Prop :=
  ∀ x y, Relation.ReflTransGen (ObservedWeak menus chosen) x y →
    ¬ObservedStrict menus chosen y x

/-- All observed chosen sets, including every tie and rejection, are exactly rationalized. -/
def RationalizesData (r : X → X → Prop) (menus chosen : I → Set X) : Prop :=
  ∀ i, chosen i = PrefChoice r (menus i)

/-- Directly revealed weak preference is respected by any rationalization. -/
theorem observedWeak_of_rationalizes {r : X → X → Prop}
    (he : RationalizesData r menus chosen) {x y : X} (h : ObservedWeak menus chosen x y) :
    r x y := by
  obtain ⟨i, hx, hy⟩ := h
  rw [he i] at hx
  exact hx.2 y hy

/-- Directly revealed strict preference is respected by any transitive rationalization. -/
theorem observedStrict_of_rationalizes {r : X → X → Prop} (ht : TransitivePref r)
    (he : RationalizesData r menus chosen) {x y : X} (h : ObservedStrict menus chosen x y) :
    Strict r x y := by
  obtain ⟨i, hx, hy, hyn⟩ := h
  rw [he i] at hx hyn
  refine ⟨hx.2 y hy, fun hyx => ?_⟩
  exact hyn ⟨hy, fun z hz => ht y x z hyx (hx.2 z hz)⟩

/-- A rationalizing preference respects every finite weak revealed chain. -/
theorem revealedChain_of_rationalizes {r : X → X → Prop} (hr : Rational r)
    (he : RationalizesData r menus chosen) {x y : X}
    (h : Relation.ReflTransGen (ObservedWeak menus chosen) x y) : r x y := by
  induction h with
  | refl => exact complete_refl hr.1 _
  | @tail y z _ hyz ih => exact hr.2 _ _ _ ih (observedWeak_of_rationalizes he hyz)

/-- Necessity in **Proposition 1.23**. -/
theorem sgarp_of_rationalizes {r : X → X → Prop} (hr : Rational r)
    (he : RationalizesData r menus chosen) : SGARP menus chosen := by
  intro x y hchain hstrict
  exact (observedStrict_of_rationalizes hr.2 he hstrict).2
    (revealedChain_of_rationalizes hr he hchain)

/-- Sufficiency in **Proposition 1.23**, via linear extension of the revealed preorder quotient. -/
theorem rationalizes_of_sgarp (hf : ∀ i, chosen i ⊆ menus i)
    (hn : ∀ i, (chosen i).Nonempty) (hg : SGARP menus chosen) :
    ∃ r : X → X → Prop, Rational r ∧ RationalizesData r menus chosen := by
  classical
  let : Preorder X := {
    le := fun x y => Relation.ReflTransGen (ObservedWeak menus chosen) y x
    le_refl := fun _ => Relation.ReflTransGen.refl
    le_trans := fun _ _ _ hxy hyz => hyz.trans hxy }
  let Q := Antisymmetrization X (· ≤ ·)
  let f : X → LinearExtension Q := fun x => toLinearExtension (toAntisymmetrization (· ≤ ·) x)
  have hfmono : Monotone f := toLinearExtension.monotone.comp toAntisymmetrization_mono
  have hflift : StrictMono (toLinearExtension (α := Q)) :=
    toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
  have hfstrict {x y : X} (hxy : x < y) : f x < f y :=
    hflift (toAntisymmetrization_lt_toAntisymmetrization_iff.mpr hxy)
  let r : X → X → Prop := fun x y => f y ≤ f x
  have hr : Rational r := ⟨fun x y => le_total (f y) (f x),
    fun _ _ _ hxy hyz => hyz.trans hxy⟩
  refine ⟨r, hr, fun i => ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hf i hx, fun y hy => ?_⟩
    exact hfmono (Relation.ReflTransGen.single ⟨i, hx, hy⟩)
  · rintro ⟨hx, hmax⟩
    by_contra hnot
    obtain ⟨z, hz⟩ := hn i
    have hzx : ObservedStrict menus chosen z x := ⟨i, hz, hx, hnot⟩
    have hlt : x < z := by
      apply lt_iff_le_not_ge.mpr
      exact ⟨Relation.ReflTransGen.single ⟨i, hz, hx⟩, fun hrev => hg x z hrev hzx⟩
    exact (not_le_of_gt (hfstrict hlt)) (hmax z (hf i hz))

/-- **Proposition 1.23**, both directions, with the necessary observation conventions explicit. -/
theorem proposition_1_23 (hf : ∀ i, chosen i ⊆ menus i) (hn : ∀ i, (chosen i).Nonempty) :
    SGARP menus chosen ↔
      ∃ r : X → X → Prop, Rational r ∧ RationalizesData r menus chosen :=
  ⟨rationalizes_of_sgarp hf hn, fun ⟨_, hr, he⟩ => sgarp_of_rationalizes hr he⟩

/-- Empty singleton observations show that SGARP alone cannot replace nonemptiness. -/
theorem empty_observation_not_rationalizable :
    SGARP (fun _ : Unit => (Set.univ : Set Unit)) (fun _ => ∅) ∧
      ¬∃ r : Unit → Unit → Prop, Rational r ∧
        RationalizesData r (fun _ : Unit => Set.univ) (fun _ => ∅) := by
  constructor
  · intro x y _ h
    obtain ⟨i, hi, _⟩ := h
    exact hi
  · rintro ⟨r, hr, he⟩
    have hmem : () ∈ PrefChoice r Set.univ :=
      ⟨Set.mem_univ _, fun y _ => by cases y; exact complete_refl hr.1 ()⟩
    rw [← he ()] at hmem
    exact hmem

end Kreps.ChoicePreferenceUtility
