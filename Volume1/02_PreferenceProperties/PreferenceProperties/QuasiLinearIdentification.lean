/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.HomotheticIdentification
import PreferenceProperties.QuasiLinear

/-!
# The region identified by a quasi-linear indifference curve

Kreps I, Problem 2.13, p. 48. With nonnegative money, an indifference curve need
not intersect every goods fiber. It identifies all comparisons between bundles
whose goods occur somewhere on that curve, at arbitrary nonnegative money levels.
The curve's projection is exactly a subutility sublevel set.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r s : (X × ℝ≥0) → (X × ℝ≥0) → Prop}

/-- Goods bundles that appear on the specified indifference curve at some feasible balance. -/
def CurveGoods (r : (X × ℝ≥0) → (X × ℝ≥0) → Prop) (p : X × ℝ≥0) : Set X :=
  {x | ∃ m : ℝ≥0, Indifferent r (x, m) p}

/-- A quasi-linear indifference curve is the graph of the compensating money balance. -/
theorem quasiLinear_class_iff {u : X → ℝ} (hu : Represents (QuasiLinearUtility u) r)
    (p q : X × ℝ≥0) :
    Indifferent r q p ↔ (q.2 : ℝ) = QuasiLinearUtility u p - u q.1 := by
  rw [indifferent_iff_utility_eq hu]
  unfold QuasiLinearUtility
  constructor <;> intro h <;> linarith

/-- Nonnegative money restricts the curve's goods projection to a subutility sublevel set. -/
theorem curveGoods_iff_subutility_le {u : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (p : X × ℝ≥0) (x : X) :
    x ∈ CurveGoods r p ↔ u x ≤ QuasiLinearUtility u p := by
  constructor
  · rintro ⟨m, hm⟩
    have he := (quasiLinear_class_iff hu p (x, m)).mp hm
    have hn : 0 ≤ (m : ℝ) := m.property
    change (m : ℝ) = QuasiLinearUtility u p - u x at he
    linarith
  · intro hx
    let m : ℝ≥0 := .mk (QuasiLinearUtility u p - u x) (sub_nonneg.mpr hx)
    exact ⟨m, (quasiLinear_class_iff hu p (x, m)).mpr rfl⟩

/-- Equal curves calibrate both subutilities up to one constant on their goods projection. -/
theorem quasiLinear_class_offset {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    {x : X} (hx : x ∈ CurveGoods r p) : v x - u x = v p.1 - u p.1 := by
  obtain ⟨m, hm⟩ := hx
  have hs : Indifferent s (x, m) p := (Set.ext_iff.mp hclass (x, m)).mp hm
  have he := (indifferent_iff_utility_eq hu (x, m) p).mp hm
  have hf := (indifferent_iff_utility_eq hv (x, m) p).mp hs
  change u x + (m : ℝ) = u p.1 + p.2 at he
  change v x + (m : ℝ) = v p.1 + p.2 at hf
  linarith

/-- **Problem 2.13:** the curve identifies all money levels over its goods projection. -/
theorem problem_2_13_quasiLinear_identified {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    {x y : X} (hx : x ∈ CurveGoods r p) (hy : y ∈ CurveGoods r p) (m n : ℝ≥0) :
    r (x, m) (y, n) ↔ s (x, m) (y, n) := by
  have hdx := quasiLinear_class_offset hu hv p hclass hx
  have hdy := quasiLinear_class_offset hu hv p hclass hy
  rw [hu, hv]
  change u y + (n : ℝ) ≤ u x + m ↔ v y + (n : ℝ) ≤ v x + m
  constructor <;> intro h <;> linarith

/-- If the curve intersects every goods fiber, it identifies the entire quasi-linear preference. -/
theorem quasiLinear_identified_of_full_projection {u v : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (hv : Represents (QuasiLinearUtility v) s)
    (p : X × ℝ≥0) (hclass : IndifferenceClass r p = IndifferenceClass s p)
    (hfull : ∀ x, x ∈ CurveGoods r p) : r = s := by
  funext a b
  exact propext (problem_2_13_quasiLinear_identified hu hv p hclass (hfull a.1) (hfull b.1)
    a.2 b.2)

/-- Goods outside the projection give bundles strictly above the curve at every feasible balance. -/
theorem quasiLinear_outside_projection {u : X → ℝ}
    (hu : Represents (QuasiLinearUtility u) r) (p : X × ℝ≥0)
    {x : X} (hx : x ∉ CurveGoods r p) (m : ℝ≥0) : Strict r (x, m) p := by
  have hg : QuasiLinearUtility u p < u x :=
    lt_of_not_ge (fun h => hx ((curveGoods_iff_subutility_le hu p x).mpr h))
  apply (strict_iff_utility_lt hu _ _).mpr
  change QuasiLinearUtility u p < u x + (m : ℝ)
  exact hg.trans_le (le_add_of_nonneg_right m.property)

/-- Continuous subutility gives continuous quasi-linear utility on goods and nonnegative money. -/
theorem quasiLinearUtility_continuous [TopologicalSpace X] {u : X → ℝ}
    (hu : Continuous u) : Continuous (QuasiLinearUtility u) :=
  (hu.comp continuous_fst).add (NNReal.continuous_coe.comp continuous_snd)

/-- Strictly increasing subutility gives strict monotonicity in the product order. -/
theorem quasiLinearUtility_strictMono [PartialOrder X] {u : X → ℝ}
    (hu : StrictMono u) : StrictMono (QuasiLinearUtility u) := by
  intro a b hab
  have hg : u a.1 ≤ u b.1 := hu.monotone hab.le.1
  have hm : (a.2 : ℝ) ≤ b.2 := NNReal.coe_le_coe.mpr hab.le.2
  by_contra hn
  have hn' : u b.1 + (b.2 : ℝ) ≤ u a.1 + a.2 := le_of_not_gt hn
  have hge : u a.1 = u b.1 := by linarith
  have hme : (a.2 : ℝ) = b.2 := by linarith
  have hgoods : a.1 = b.1 := by
    by_contra hne
    exact (ne_of_lt (hu (lt_of_le_of_ne hab.le.1 hne))) hge
  exact hab.ne (Prod.ext hgoods (NNReal.coe_injective hme))

end Kreps.PreferenceProperties
