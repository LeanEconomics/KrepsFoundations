/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.EventSimpleActs
import ChoiceUnderUncertainty.MixtureRepresentation

/-!
# Event contributions of affine utility on simple acts

Kreps I, Problem 5.6(a–c), pp. 120–121. A midpoint identity splits the value
increment on disjoint events. Induction gives the formula for every finite
partition, including further refinements within cells. Preferences satisfy
Savage's Sure-Thing Principle on the given algebra.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- Statewise mixture of two doubly simple acts on the fixed algebra. -/
noncomputable def EventMix (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) :
    EventAct A X := @Mix _ (eventActConvexSpace hA) a h g

/-- The mixture at a state is its ordinary roulette mixture. -/
theorem eventMix_apply (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) (s : S) :
    (EventMix hA a h g).val s = Mix a (h.val s) (g.val s) := eventAct_mix_apply hA a h g s

/-- Binary mixture affinity on the actual simple-act domain. -/
def EventAffine (hA : IsSetAlgebra A) (F : EventAct A X → ℝ) : Prop :=
  ∀ a h g, F (EventMix hA a h g) = a.val * F h + (1 - a.val) * F g

/-- **Problem 5.6(a):** primitive mixture axioms give a representing affine functional. -/
theorem problem_5_6a (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop) :
    @MixtureAxioms _ (eventActConvexSpace hA) r ↔ ∃ F, Represents F r ∧ EventAffine hA F :=
  @proposition_5_4 _ (eventActConvexSpace hA) r

/-- The value contributed on an event relative to the constant reference act. -/
noncomputable def EventContribution (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (h : EventAct A X) : ℝ :=
  F (EventCut hA base E hE h) - F (EventConstant hA base)

/-- Equal events have equal contributions, independently of the proofs of admissibility. -/
theorem eventContribution_congr_event (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) {E D : Set S} (hE : E ∈ A) (hD : D ∈ A) (h : EventAct A X)
    (he : E = D) : EventContribution hA F b E hE h = EventContribution hA F b D hD h := by
  subst D
  rfl

/-- An empty event makes no change to the reference act. -/
theorem eventContribution_empty (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) (h : EventAct A X) :
    EventContribution hA F b ∅ hA.empty_mem h = 0 := by
  have he : EventCut hA b ∅ hA.empty_mem h = EventConstant hA b := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply, EventConstant]
  simp [EventContribution, he]

/-- On the universal event the contribution is the act's entire value increment. -/
theorem eventContribution_univ (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) (h : EventAct A X) :
    EventContribution hA F b Set.univ hA.univ_mem h = F h - F (EventConstant hA b) := by
  have he : EventCut hA b Set.univ hA.univ_mem h = h := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply]
  simp [EventContribution, he]

/-- Contributions agree whenever the underlying acts agree on the event. -/
theorem eventContribution_congr_act (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) {E : Set S} (hE : E ∈ A) (h g : EventAct A X)
    (he : ∀ s ∈ E, h.val s = g.val s) :
    EventContribution hA F b E hE h = EventContribution hA F b E hE g := by
  classical
  have hc : EventCut hA b E hE h = EventCut hA b E hE g := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E
    · simp [eventCut_apply, hs, he s hs]
    · simp [eventCut_apply, hs]
  simp only [EventContribution, hc]

/-- Affine utility adds increments on arbitrary disjoint algebra events. -/
theorem eventContribution_union (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (b : SimpleLottery X) {E D : Set S}
    (hE : E ∈ A) (hD : D ∈ A) (hd : Disjoint E D) (h : EventAct A X) :
    EventContribution hA F b (E ∪ D) (hA.union_mem hE hD) h =
      EventContribution hA F b E hE h + EventContribution hA F b D hD h := by
  classical
  let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
  have hsym (x y : SimpleLottery X) : Mix a x y = Mix a y x := by
    have hc : Complement a = a := by ext; norm_num [Complement, a]
    rw [mix_swap a x y, hc]
  have he : EventMix hA a (EventCut hA b E hE h) (EventCut hA b D hD h) =
      EventMix hA a (EventCut hA b (E ∪ D) (hA.union_mem hE hD) h) (EventConstant hA b) := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E
    · have ht : s ∉ D := Set.disjoint_left.mp hd hs
      simp [eventMix_apply, eventCut_apply, EventConstant, hs, ht]
    · by_cases ht : s ∈ D <;> simp [eventMix_apply, eventCut_apply, EventConstant, hs, ht, hsym]
  have h₁ := ha a (EventCut hA b E hE h) (EventCut hA b D hD h)
  have h₂ := ha a (EventCut hA b (E ∪ D) (hA.union_mem hE hD) h) (EventConstant hA b)
  rw [he] at h₁
  dsimp only [a] at h₁ h₂
  unfold EventContribution
  linarith

/-- The union of a finite family of partition cells is an algebra event. -/
theorem partitionUnion_mem {I : Type*} (hA : IsSetAlgebra A) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (T : Finset I) : {s | c s ∈ T} ∈ A := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hA.empty_mem
  | @insert i T _ ih =>
    convert hA.union_mem (hc i) ih using 1
    ext s
    simp

/-- The contribution on any finite union of cells is the sum of the cell contributions. -/
theorem eventContribution_partitionUnion {I : Type*} (hA : IsSetAlgebra A)
    {F : EventAct A X → ℝ} (ha : EventAffine hA F) (b : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (T : Finset I) (h : EventAct A X) :
    EventContribution hA F b {s | c s ∈ T} (partitionUnion_mem hA c hc T) h =
      ∑ i ∈ T, EventContribution hA F b {s | c s = i} (hc i) h := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, eventContribution_congr_event hA F b _ hA.empty_mem h (by ext; simp),
      eventContribution_empty]
  | @insert i T hi ih =>
    have he : {s | c s ∈ insert i T} = {s | c s = i} ∪ {s | c s ∈ T} := by ext; simp
    have hd : Disjoint {s | c s = i} {s | c s ∈ T} := by
      apply Set.disjoint_left.mpr
      intro s hs ht
      exact hi (hs ▸ ht)
    rw [eventContribution_congr_event hA F b _ (hA.union_mem (hc i)
      (partitionUnion_mem hA c hc T)) h he,
      eventContribution_union hA ha b (hc i) (partitionUnion_mem hA c hc T) hd,
      ih, Finset.sum_insert hi]

/-- **Problem 5.6(b):** finite-partition additivity also covers every further cell refinement. -/
theorem problem_5_6b {I : Type*} [Fintype I] (hA : IsSetAlgebra A)
    {F : EventAct A X → ℝ} (ha : EventAffine hA F) (b : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (h : EventAct A X) :
    F h - F (EventConstant hA b) = ∑ i, EventContribution hA F b {s | c s = i} (hc i) h := by
  have he : {s | c s ∈ (Finset.univ : Finset I)} = Set.univ := by ext; simp
  rw [← eventContribution_univ hA F b h,
    ← eventContribution_congr_event hA F b (partitionUnion_mem hA c hc Finset.univ) _ h he]
  exact eventContribution_partitionUnion hA ha b c hc _ h

/-- Splitting at an event and its complement exactly decomposes the value increment. -/
theorem eventContribution_complement (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (b : SimpleLottery X) {E : Set S} (hE : E ∈ A) (h : EventAct A X) :
    F h - F (EventConstant hA b) = EventContribution hA F b E hE h +
      EventContribution hA F b Eᶜ (hA.compl_mem hE) h := by
  rw [← eventContribution_union hA ha b hE (hA.compl_mem hE) disjoint_compl_right,
    eventContribution_congr_event hA F b _ hA.univ_mem h (Set.union_compl_self E),
    eventContribution_univ]

/-- **Problem 5.6(c):** replacement of common off-event consequences preserves the ranking. -/
theorem problem_5_6c (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (b : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) (f g f' g' : EventAct A X)
    (hin : ∀ s ∈ E, f.val s = f'.val s ∧ g.val s = g'.val s)
    (hout : ∀ s ∉ E, f.val s = g.val s ∧ f'.val s = g'.val s) : r f g ↔ r f' g' := by
  obtain ⟨F, hFr, hFa⟩ := (problem_5_6a hA r).mp hr
  have a := eventContribution_complement hA hFa b hE f
  have c := eventContribution_complement hA hFa b hE g
  have a' := eventContribution_complement hA hFa b hE f'
  have c' := eventContribution_complement hA hFa b hE g'
  have di := eventContribution_congr_act hA F b hE f f' (fun s hs => (hin s hs).1)
  have dj := eventContribution_congr_act hA F b hE g g' (fun s hs => (hin s hs).2)
  have ei := eventContribution_congr_act hA F b (hA.compl_mem hE) f g (fun s hs => (hout s hs).1)
  have ej := eventContribution_congr_act hA F b (hA.compl_mem hE) f' g' (fun s hs => (hout s hs).2)
  rw [hFr, hFr]
  constructor <;> intro h <;> linarith

end Kreps.ChoiceUnderUncertainty
