/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Joint continuity of increasing aggregators

An increasing real-valued function on a finite product of densely ordered
spaces is jointly continuous if it is continuous in each coordinate. The
proof builds a finite product neighborhood inside each strict level set.
Endpoints of the coordinate intervals are allowed.
-/

namespace Kreps.PreferenceProperties

open Filter Set
open scoped Topology

/-- A continuous strict lower level has a nearby lower bound whose upper ray is a neighborhood. -/
theorem continuous_lower_level_bound {A : Type*} [LinearOrder A] [DenselyOrdered A]
    [TopologicalSpace A] [OrderTopology A] {f : A → ℝ} (hf : Continuous f)
    {x : A} {a : ℝ} (ha : a < f x) :
    ∃ y, y ≤ x ∧ a < f y ∧ Ici y ∈ 𝓝 x := by
  by_cases hx : ∃ z, z < x
  · obtain ⟨l, hl, hs⟩ := exists_Ioc_subset_of_mem_nhds
      (hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ha)) hx
    obtain ⟨y, hly, hyx⟩ := exists_between hl
    exact ⟨y, hyx.le, hs ⟨hly, hyx.le⟩, Ici_mem_nhds hyx⟩
  · refine ⟨x, le_rfl, ha, ?_⟩
    have he : Ici x = univ := by
      ext y
      simp only [mem_Ici, mem_univ, iff_true]
      exact le_of_not_gt (fun hy => hx ⟨y, hy⟩)
    rw [he]
    exact univ_mem

variable {I : Type*} [DecidableEq I] {A : I → Type*}
variable [∀ i, LinearOrder (A i)] [∀ i, DenselyOrdered (A i)]
variable [∀ i, TopologicalSpace (A i)] [∀ i, OrderTopology (A i)]

/-- Lower bounds for finitely many coordinates can be chosen inside a strict lower level. -/
theorem finite_coordinate_lower_bound {F : (∀ i, A i) → ℝ}
    (hc : ∀ p i, Continuous (fun t => F (Function.update p i t)))
    (s : Finset I) (p : ∀ i, A i) {a : ℝ} (ha : a < F p) :
    ∃ q, q ≤ p ∧ a < F q ∧ (∀ i ∈ s, Ici (q i) ∈ 𝓝 (p i)) ∧
      ∀ i ∉ s, q i = p i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨p, le_rfl, ha, by simp, by simp⟩
  | @insert i s his ih =>
    obtain ⟨q, hqp, haq, hqn, hqe⟩ := ih
    have hiq : q i = p i := hqe i his
    have haq' : a < F (Function.update q i (q i)) := by
      simpa only [Function.update_eq_self] using haq
    obtain ⟨t, hti, hat, htn⟩ := continuous_lower_level_bound (hc q i) haq'
    refine ⟨Function.update q i t, ?_, hat, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hti.trans (hqp i)
      · simpa only [Function.update_of_ne hji] using hqp j
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        simpa only [Function.update_self, hiq] using htn
      · have hji : j ≠ i := fun h => his (h ▸ hjs)
        simpa only [Function.update_of_ne hji] using hqn j hjs
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i s)
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
      simpa only [Function.update_of_ne hji] using hqe j hjs

/-- A separately continuous increasing finite-product function has open strict lower levels. -/
theorem finiteProductMonotone_isOpen_lt [Finite I] {F : (∀ i, A i) → ℝ}
    (hm : Monotone F) (hc : ∀ p i, Continuous (fun t => F (Function.update p i t)))
    (a : ℝ) : IsOpen {p | a < F p} := by
  classical
  let : Fintype I := Fintype.ofFinite I
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨q, _, haq, hqn, _⟩ := finite_coordinate_lower_bound hc Finset.univ p hp
  have hn (i : I) : ∀ᶠ x in 𝓝 p, q i ≤ x i :=
    (continuous_apply i).continuousAt.preimage_mem_nhds (hqn i (Finset.mem_univ i))
  filter_upwards [Filter.eventually_all.mpr hn] with x hx
  exact haq.trans_le (hm hx)

/-- Coordinate continuity and monotonicity imply joint continuity on a finite interval product. -/
theorem finiteProductMonotone_continuous [Finite I] {F : (∀ i, A i) → ℝ}
    (hm : Monotone F) (hc : ∀ p i, Continuous (fun t => F (Function.update p i t))) :
    Continuous F := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  refine ⟨finiteProductMonotone_isOpen_lt hm hc a, ?_⟩
  have hn : Monotone (fun p : ∀ i, (A i)ᵒᵈ => -F p) := by
    intro p q hpq
    exact neg_le_neg (hm hpq)
  have ho := finiteProductMonotone_isOpen_lt hn (fun p i => (hc p i).neg) (-a)
  have hdual : Continuous (fun p : ∀ i, A i => (fun i => p i : ∀ i, (A i)ᵒᵈ)) :=
    continuous_pi (fun i => continuous_apply i)
  convert ho.preimage hdual using 1
  ext p
  change F p < a ↔ -a < -F p
  exact neg_lt_neg_iff.symm

end Kreps.PreferenceProperties
