/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.HorseLotteries
import Mathlib.MeasureTheory.SetAlgebra

/-!
# Simple acts on an algebra of state events

Kreps I, Problem 5.6, pp. 119–122. An act factors through a finite partition
whose cells belong to the given algebra. Intersections supply common refinements.
This works for arbitrary state and prize types and allows empty partition cells.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity MeasureTheory

variable {S X Y Z : Type*} {A : Set (Set S)}

/-- A finite partition representation with an algebra event for each cell. -/
def IsEventSimple (A : Set (Set S)) (h : S → X) : Prop :=
  ∃ (n : ℕ) (cell : S → Fin n) (outcome : Fin n → X),
    (∀ i, {s | cell s = i} ∈ A) ∧ ∀ s, h s = outcome (cell s)

/-- A partition indexed by any finite type can be renumbered by consecutive natural numbers. -/
theorem isEventSimple_of_partition {I : Type*} [Finite I] (cell : S → I) (outcome : I → X)
    (hc : ∀ i, {s | cell s = i} ∈ A) : IsEventSimple A (fun s => outcome (cell s)) := by
  classical
  let _ := Fintype.ofFinite I
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun s => e (cell s), fun i => outcome (e.symm i), ?_, ?_⟩
  · intro i
    convert hc (e.symm i) using 1
    ext s
    exact e.eq_symm_apply.symm
  · intro s
    simp

/-- A constant act has the one-cell partition. -/
theorem isEventSimple_const (hA : IsSetAlgebra A) (x : X) : IsEventSimple A (fun _ => x) := by
  apply isEventSimple_of_partition (fun _ : S => ()) (fun _ => x)
  intro i
  simpa using hA.univ_mem

/-- A pointwise binary operation on simple acts uses the intersection of their partition cells. -/
theorem isEventSimple_map₂ (hA : IsSetAlgebra A) {h : S → X} {g : S → Y}
    (hh : IsEventSimple A h) (hg : IsEventSimple A g) (f : X → Y → Z) :
    IsEventSimple A (fun s => f (h s) (g s)) := by
  obtain ⟨n, c, v, hc, hv⟩ := hh
  obtain ⟨m, d, w, hd, hw⟩ := hg
  have hcell (i : Fin n × Fin m) :
      {s | (c s, d s) = i} = {s | c s = i.1} ∩ {s | d s = i.2} := by
    ext s
    simp [Prod.ext_iff]
  have H := isEventSimple_of_partition (fun s => (c s, d s)) (fun i => f (v i.1) (w i.2))
    (fun i => hcell i ▸ hA.inter_mem (hc i.1) (hd i.2))
  simpa only [hv, hw] using H

/-- Indicators of algebra events are simple functions. -/
theorem isEventSimple_indicator (hA : IsSetAlgebra A) {E : Set S} (hE : E ∈ A) :
    IsEventSimple A (fun s => @decide (s ∈ E) (Classical.propDecidable _)) := by
  classical
  have hc (i : Bool) : {s | decide (s ∈ E) = i} ∈ A := by
    cases i
    · convert hA.compl_mem hE using 1
      ext s
      simp
    · simpa using hE
  simpa using isEventSimple_of_partition (fun s => decide (s ∈ E)) id hc

/-- Pasting any two simple acts across an algebra event produces another simple act. -/
theorem isEventSimple_paste (hA : IsSetAlgebra A) {E : Set S} (hE : E ∈ A)
    {h g : S → X} (hh : IsEventSimple A h) (hg : IsEventSimple A g) :
    IsEventSimple A (fun s => @ite X (s ∈ E) (Classical.propDecidable _) (h s) (g s)) := by
  classical
  have H := isEventSimple_map₂ hA (isEventSimple_indicator hA hE)
    (isEventSimple_map₂ hA hh hg Prod.mk) (fun b (q : X × X) => if b then q.1 else q.2)
  simpa using H

/-- The space of doubly simple acts: finite algebra partitions and finitely supported prizes. -/
abbrev EventAct (A : Set (Set S)) (X : Type*) := {h : S → SimpleLottery X // IsEventSimple A h}

/-- Any algebra-simple act can be mixed state by state with any other such act. -/
theorem eventAct_isConvex (hA : IsSetAlgebra A) :
    IsConvexSet ℝ {h : S → SimpleLottery X | IsEventSimple A h} := by
  apply IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab h hh g hg
  have H := isEventSimple_map₂ hA hh hg (convexCombPair a b ha hb hab)
  change IsEventSimple A (convexCombPair a b ha hb hab h g)
  simpa only [← Pi.convexCombPair_apply] using H

/-- The actual mixture-space structure on the source's doubly simple acts. -/
noncomputable abbrev eventActConvexSpace (hA : IsSetAlgebra A) :
    ConvexSpace ℝ (EventAct A X) := .subtype _ (eventAct_isConvex hA)

/-- A roulette lottery offered independently of the state. -/
noncomputable def EventConstant (hA : IsSetAlgebra A) (q : SimpleLottery X) : EventAct A X :=
  ⟨fun _ => q, isEventSimple_const hA q⟩

/-- Replace the reference lottery on an arbitrary event by the corresponding part of an act. -/
noncomputable def EventCut (hA : IsSetAlgebra A) (base : SimpleLottery X)
    (E : Set S) (hE : E ∈ A) (h : EventAct A X) : EventAct A X := by
  classical
  exact ⟨fun s => if s ∈ E then h.val s else base,
    isEventSimple_paste hA hE h.property (isEventSimple_const hA base)⟩

/-- Membership in an event chooses the act's value, with baseline on its complement. -/
theorem eventCut_apply (hA : IsSetAlgebra A) (base : SimpleLottery X)
    (E : Set S) (hE : E ∈ A) (h : EventAct A X) (s : S) [Decidable (s ∈ E)] :
    (EventCut hA base E hE h).val s = if s ∈ E then h.val s else base := by
  classical
  by_cases hs : s ∈ E <;> simp [EventCut, hs]

/-- The convex-space instance mixes the actual conditional roulette lotteries pointwise. -/
theorem eventAct_mix_apply (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) (s : S) :
    letI := eventActConvexSpace (X := X) hA
    (Mix a h g).val s = Mix a (h.val s) (g.val s) := by
  let _ := eventActConvexSpace (X := X) hA
  calc
    _ = Mix a h.val g.val s := congrFun (subtypeVal_convexCombPair _
      (eventAct_isConvex hA) a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
      (by ring) h g) s
    _ = _ := mix_act_apply a h.val g.val s

end Kreps.ChoiceUnderUncertainty
