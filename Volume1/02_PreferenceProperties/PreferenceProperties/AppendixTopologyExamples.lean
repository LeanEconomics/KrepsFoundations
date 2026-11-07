/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixContinuousFunctions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Appendix 2: relative topology and examples

The half-open interval and infinite-intersection examples on p. 442, the
relative-topology exercises on p. 443, and the Lipschitz footnote on pp. 447–448.
-/

namespace Kreps.PreferenceProperties

/-- The interval `(0,1]` is neither open nor closed. -/
theorem appendix2_half_open_interval :
    ¬IsOpen (Set.Ioc (0 : ℝ) 1) ∧ ¬IsClosed (Set.Ioc (0 : ℝ) 1) := by
  constructor
  · intro h
    have he := h.interior_eq
    rw [interior_Ioc] at he
    have hmem : (1 : ℝ) ∈ Set.Ioo 0 1 := he.symm ▸ (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 1)
    exact (lt_irrefl (1 : ℝ)) hmem.2
  · intro h
    have he := h.closure_eq
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at he
    have hmem : (0 : ℝ) ∈ Set.Ioc 0 1 := he ▸ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    exact (lt_irrefl (0 : ℝ)) hmem.1

/-- An arbitrary intersection of open neighborhoods may fail to be open. -/
theorem appendix2_infinite_open_intersection :
    (∀ ε > 0, IsOpen (Metric.ball (0 : ℝ) ε)) ∧
      ¬IsOpen (⋂ ε > 0, Metric.ball (0 : ℝ) ε) := by
  refine ⟨fun _ _ => Metric.isOpen_ball, ?_⟩
  rw [Metric.biInter_gt_ball, Metric.closedBall_zero]
  exact not_isOpen_singleton 0

/-- A relatively open subset of an open domain is open in the ambient space. -/
theorem appendix2_relative_open_ambient {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsOpen S) {A : Set S} (hA : IsOpen A) : IsOpen (Subtype.val '' A) :=
  hS.isOpenMap_subtype_val A hA

/-- A relatively closed subset of a closed domain is closed in the ambient space. -/
theorem appendix2_relative_closed_ambient {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsClosed S) {A : Set S} (hA : IsClosed A) : IsClosed (Subtype.val '' A) :=
  hS.isClosedMap_subtype_val A hA

/-- Relative closure is ambient closure intersected with the domain, expressed by preimage. -/
theorem appendix2_relative_closure {X : Type*} [TopologicalSpace X] {S : Set X}
    (A : Set S) : closure A = Subtype.val ⁻¹' closure (Subtype.val '' A) :=
  Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image A

/-- The footnote's linear epsilon–delta rule is exactly a bound at the base point. -/
theorem appendix2_pointwise_lipschitz_rule {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) (x : X)
    {C : ℝ} (hC : 0 < C) :
    (∀ y, dist (f y) (f x) ≤ C * dist y x) ↔
      ∀ ε > 0, ∀ y, dist y x < ε / C → dist (f y) (f x) < ε := by
  constructor
  · intro h ε _ y hy
    have hd := (lt_div_iff₀ hC).mp hy
    have hf := h y
    nlinarith
  · intro h y
    by_contra hn
    have hlt : C * dist y x < dist (f y) (f x) := lt_of_not_ge hn
    have hpos : 0 < (dist (f y) (f x) + C * dist y x) / 2 := by
      nlinarith [dist_nonneg (x := y) (y := x)]
    have hd : dist y x < ((dist (f y) (f x) + C * dist y x) / 2) / C := by
      apply (lt_div_iff₀ hC).mpr
      nlinarith
    have hf := h _ hpos y hd
    nlinarith

/-- A positive pointwise Lipschitz constant implies continuity at that point. -/
theorem appendix2_pointwise_lipschitz_continuousAt {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {x : X}
    {C : ℝ} (hC : 0 < C) (hf : ∀ y, dist (f y) (f x) ≤ C * dist y x) :
    ContinuousAt f x := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  exact ⟨ε / C, div_pos hε hC, fun _ hy =>
    (appendix2_pointwise_lipschitz_rule f x hC).mp hf ε hε _ hy⟩

end Kreps.PreferenceProperties
