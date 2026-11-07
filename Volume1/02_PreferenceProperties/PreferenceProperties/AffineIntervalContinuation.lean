/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AffineIntervalAtlas

/-!
# Continuation of affine interval coordinates

Compatible coordinates can be glued across overlapping intervals. Taking all continuations of
a seed chart gives a maximal domain; local charts extend it through any boundary point inside
the underlying interval. The construction uses agreement on overlaps rather than a maximality
principle.
-/

namespace Kreps.PreferenceProperties

open Set
open scoped Topology

/-- Compatibility is unchanged when a coordinate is replaced by an equal one on its domain. -/
theorem PositiveAffineIntervalAtlas.Compatible.congr {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f g : ℝ → ℝ}
    (h : a.Compatible f D) (he : EqOn g f D) : a.Compatible g D := by
  intro i x hx
  obtain ⟨U, hU, hxU, hsub, A, B, hA, hEq⟩ := h i x hx
  exact ⟨U, hU, hxU, hsub, A, B, hA, fun y hy => (he (hsub hy).1).trans (hEq y hy)⟩

/-- Locally compatible coordinates remain compatible on the union of their domains. -/
theorem PositiveAffineIntervalAtlas.Compatible.union {ι : Type*} {S D E : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ}
    (hD : a.Compatible f D) (hE : a.Compatible f E) : a.Compatible f (D ∪ E) := by
  intro i x hx
  rcases hx.1 with hxD | hxE
  · obtain ⟨U, hU, hxU, hsub, A, B, hA, he⟩ := hD i x ⟨hxD, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨Or.inl (hsub hy).1, (hsub hy).2⟩, A, B, hA, he⟩
  · obtain ⟨U, hU, hxU, hsub, A, B, hA, he⟩ := hE i x ⟨hxE, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨Or.inr (hsub hy).1, (hsub hy).2⟩, A, B, hA, he⟩

/-- A positive affine rescaling preserves compatibility with the atlas. -/
theorem PositiveAffineIntervalAtlas.Compatible.positive_affine {ι : Type*} {S D : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {f : ℝ → ℝ}
    (h : a.Compatible f D) {A B : ℝ} (hA : 0 < A) :
    a.Compatible (fun x => A * f x + B) D := by
  intro i x hx
  obtain ⟨U, hU, hxU, hsub, C, F, hC, he⟩ := h i x hx
  refine ⟨U, hU, hxU, hsub, A * C, A * F + B, mul_pos hA hC, ?_⟩
  intro y hy
  change A * f y + B = _
  rw [he y hy]
  ring

/-- A continuation extends over every chart whose domain meets it. -/
theorem AffineIntervalSection.extend {ι : Type*} {S : Set ℝ}
    {a : PositiveAffineIntervalAtlas ι S} {seed : ι}
    (p : AffineIntervalSection a seed) (i : ι)
    (hne : (p.domain ∩ a.domain i).Nonempty) :
    ∃ q : AffineIntervalSection a seed, q.domain = p.domain ∪ a.domain i ∧
      EqOn q.value p.value p.domain := by
  classical
  obtain ⟨A, B, hA, he⟩ := p.compatible.affine p.interval i
  let g : ℝ → ℝ := fun x => A * a.coord i x + B
  let f : ℝ → ℝ := p.domain.piecewise p.value g
  have hfD : EqOn f p.value p.domain := fun x hx => by simp [f, hx]
  have hfU : EqOn f g (a.domain i) := by
    intro x hx
    by_cases hxD : x ∈ p.domain
    · simpa [f, hxD, g] using he x ⟨hxD, hx⟩
    · simp [f, hxD]
  have hg : ContinuousOn g (a.domain i) :=
    (continuousOn_const.mul (a.continuous i)).add continuousOn_const
  have hgm : StrictMonoOn g (a.domain i) := by
    intro x hx y hy hxy
    dsimp [g]
    nlinarith [a.increasing i hx hy hxy]
  have hfDc := p.continuous.congr hfD
  have hfUc := hg.congr hfU
  have hfDm : StrictMonoOn f p.domain := by
    intro x hx y hy hxy
    rw [hfD hx, hfD hy]
    exact p.increasing hx hy hxy
  have hfUm : StrictMonoOn f (a.domain i) := by
    intro x hx y hy hxy
    rw [hfU hx, hfU hy]
    exact hgm hx hy hxy
  obtain ⟨x, hxD, hxU⟩ := hne
  let q : AffineIntervalSection a seed := {
    domain := p.domain ∪ a.domain i
    isOpen := p.isOpen.union (a.isOpen i)
    interval := (p.interval.isPreconnected.union x hxD hxU
      (a.interval i).isPreconnected).ordConnected
    subset := union_subset p.subset (a.subset i)
    value := f
    continuous := hfDc.union_of_isOpen hfUc p.isOpen (a.isOpen i)
    increasing := strictMonoOn_union_intervals p.interval (a.interval i)
      ⟨x, hxD, hxU⟩ hfDm hfUm
    compatible := (p.compatible.congr hfD).union
      (((a.compatible_chart i).positive_affine hA).congr hfU)
    seed_subset := fun _ hx => Or.inl (p.seed_subset hx)
    seed_eq := fun y hy => (hfD (p.seed_subset hy)).trans (p.seed_eq y hy) }
  exact ⟨q, rfl, hfD⟩

/-- Seed-normalized continuations reach every point of the underlying interval. -/
theorem PositiveAffineIntervalAtlas.sections_cover {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∀ x ∈ S, ∃ p : AffineIntervalSection a seed, x ∈ p.domain := by
  let U : Set ℝ := ⋃ p : AffineIntervalSection a seed, p.domain
  have hU : IsOpen U := isOpen_iUnion fun p => p.isOpen
  have hSU : (S ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, a.subset seed hx, mem_iUnion.mpr ⟨a.seedSection seed, hx⟩⟩
  have hclosed : closure U ∩ S ⊆ U := by
    intro x hx
    obtain ⟨i, hxi⟩ := a.cover x hx.2
    obtain ⟨y, hyi, hyU⟩ := mem_closure_iff.mp hx.1 (a.domain i) (a.isOpen i) hxi
    obtain ⟨p, hyp⟩ := mem_iUnion.mp hyU
    obtain ⟨q, hq, _⟩ := p.extend i ⟨y, hyp, hyi⟩
    exact mem_iUnion.mpr ⟨q, hq ▸ Or.inr hxi⟩
  have hfull := hS.isPreconnected.subset_of_closure_inter_subset hU hSU hclosed
  exact fun x hx => mem_iUnion.mp (hfull hx)

/-- An oriented affine atlas on an open real interval has a global seed-normalized coordinate. -/
theorem PositiveAffineIntervalAtlas.exists_global_section {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∃ p : AffineIntervalSection a seed, p.domain = S := by
  classical
  choose p hp using fun x : S => a.sections_cover hS seed hne x x.property
  let f : ℝ → ℝ := fun x => if hx : x ∈ S then (p ⟨x, hx⟩).value x else 0
  have he (q : AffineIntervalSection a seed) : EqOn f q.value q.domain := by
    intro x hx
    have hxS := q.subset hx
    simp only [f, dite_eq_left hxS]
    exact AffineIntervalSection.unique hne (p ⟨x, hxS⟩) q ⟨hp ⟨x, hxS⟩, hx⟩
  have hm (q : AffineIntervalSection a seed) : StrictMonoOn f q.domain := by
    intro x hx y hy hxy
    rw [he q hx, he q hy]
    exact q.increasing hx hy hxy
  have hSo : IsOpen S := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨i, hxi⟩ := a.cover x hx
    exact ⟨a.domain i, a.subset i, a.isOpen i, hxi⟩
  have hc : ContinuousOn f S := by
    apply continuousOn_of_locally_continuousOn
    intro x hx
    exact ⟨(p ⟨x, hx⟩).domain, (p ⟨x, hx⟩).isOpen, hp ⟨x, hx⟩,
      ((p ⟨x, hx⟩).continuous.congr (he (p ⟨x, hx⟩))).mono inter_subset_right⟩
  have hmono : StrictMonoOn f S := by
    obtain ⟨z, hz⟩ := hne
    intro x hx y hy hxy
    let q := p ⟨x, hx⟩
    let r := p ⟨y, hy⟩
    exact strictMonoOn_union_intervals q.interval r.interval
      ⟨z, q.seed_subset hz, r.seed_subset hz⟩ (hm q) (hm r)
      (Or.inl (hp ⟨x, hx⟩)) (Or.inr (hp ⟨y, hy⟩)) hxy
  have hcomp : a.Compatible f S := by
    intro i x hx
    let q := p ⟨x, hx.1⟩
    obtain ⟨U, hU, hxU, hsub, A, B, hA, hEq⟩ := q.compatible i x ⟨hp ⟨x, hx.1⟩, hx.2⟩
    exact ⟨U, hU, hxU, fun _ hy => ⟨q.subset (hsub hy).1, (hsub hy).2⟩,
      A, B, hA, fun y hy => (he q (hsub hy).1).trans (hEq y hy)⟩
  refine ⟨{
    domain := S
    isOpen := hSo
    interval := hS
    subset := Subset.rfl
    value := f
    continuous := hc
    increasing := hmono
    compatible := hcomp
    seed_subset := a.subset seed
    seed_eq := fun x hx => he (a.seedSection seed) hx }, rfl⟩

/-- A global scale is continuous and increasing, with explicit positive affine chart changes. -/
theorem PositiveAffineIntervalAtlas.globalize {ι : Type*} {S : Set ℝ}
    (a : PositiveAffineIntervalAtlas ι S) (hS : S.OrdConnected) (seed : ι)
    (hne : (a.domain seed).Nonempty) :
    ∃ f : ℝ → ℝ, ContinuousOn f S ∧ StrictMonoOn f S ∧
      (∀ x ∈ a.domain seed, f x = a.coord seed x) ∧
      ∀ i, ∃ A B : ℝ, 0 < A ∧ ∀ x ∈ a.domain i, f x = A * a.coord i x + B := by
  obtain ⟨p, hp⟩ := a.exists_global_section hS seed hne
  refine ⟨p.value, ?_, ?_, p.seed_eq, fun i => ?_⟩
  · simpa only [hp] using p.continuous
  · simpa only [hp] using p.increasing
  · obtain ⟨A, B, hA, he⟩ := p.compatible.affine p.interval i
    refine ⟨A, B, hA, fun x hx => he x ⟨?_, hx⟩⟩
    simpa only [hp] using a.subset i hx

end Kreps.PreferenceProperties
