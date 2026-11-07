/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoicePreferenceUtility.StrictPreference
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Countable

/-!
# Countable utility representation

Kreps I, §1.5, Propositions 1.11-1.12, pp. 10-12. Positive summable weights on a
countable separating subset give a utility representation. Conversely, rational
interval witnesses, together with attained minima above rational cutoffs, provide a
countable separating subset of any represented preference. This is the book's
countability argument with the gap case expressed without infimum notation.
-/

namespace Kreps.ChoicePreferenceUtility

variable {X : Type*} {r : X → X → Prop}

/-- The separating-subset condition in **Proposition 1.12**, p. 11. -/
def OrderSeparating (r : X → X → Prop) (D : Set X) : Prop :=
  ∀ x y, Strict r x y → ∃ z ∈ D, r x z ∧ Strict r z y

/-- Every countable type has strictly positive summable real weights. -/
theorem exists_positive_summable (Y : Type*) [Countable Y] :
    ∃ w : Y → ℝ, (∀ y, 0 < w y) ∧ Summable w := by
  let := Encodable.ofCountable Y
  exact ⟨fun y => (1 / 2 : ℝ) ^ Encodable.encode y,
    fun _ => pow_pos (by norm_num) _, summable_geometric_two_encode⟩

/-- Sum the weights of separating alternatives no better than `x`. -/
noncomputable def WeightedUtility (r : X → X → Prop) (D : Set X)
    (w : D → ℝ) (x : X) : ℝ := ∑' z : D, {z : D | r x z}.indicator w z

/-- Termwise comparison of weighted no-better-than sets. -/
theorem weightedTerm_le {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (ht : TransitivePref r) {x y : X} (hxy : r x y) (z : D) :
    {z : D | r y z}.indicator w z ≤ {z : D | r x z}.indicator w z := by
  classical
  change (if r y z then w z else 0) ≤ if r x z then w z else 0
  by_cases hy : r y z
  · have hx := ht x y z hxy hy
    simp [hy, hx]
  · simp only [hy, ite_false]
    split_ifs
    · exact (hw z).le
    · exact le_rfl

/-- Weak preference increases the weighted sum. -/
theorem weightedUtility_mono {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (ht : TransitivePref r) {x y : X} (hxy : r x y) :
    WeightedUtility r D w y ≤ WeightedUtility r D w x :=
  Summable.tsum_le_tsum (weightedTerm_le hw ht hxy)
    (hs.indicator _) (hs.indicator _)

/-- A separating witness makes the increase in utility strict. -/
theorem weightedUtility_strict {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (ht : TransitivePref r) (hD : OrderSeparating r D)
    {x y : X} (hxy : Strict r x y) :
    WeightedUtility r D w y < WeightedUtility r D w x := by
  classical
  obtain ⟨z, hzD, hxz, hzy⟩ := hD x y hxy
  let zi : D := ⟨z, hzD⟩
  have hzi : {z : D | r y z}.indicator w zi < {z : D | r x z}.indicator w zi := by
    change (if r y z then w zi else 0) < if r x z then w zi else 0
    simp only [hzy.2, ite_false, hxz, ite_true]
    exact hw zi
  exact Summable.tsum_lt_tsum (weightedTerm_le hw ht hxy.1) hzi
    (hs.indicator _) (hs.indicator _)

/-- A positive weighted sum on a separating set represents rational preferences. -/
theorem weightedUtility_represents {D : Set X} {w : D → ℝ} (hw : ∀ z, 0 < w z)
    (hs : Summable w) (hr : Rational r) (hD : OrderSeparating r D) :
    Represents (WeightedUtility r D w) r := by
  intro x y
  constructor
  · exact weightedUtility_mono hw hs hr.2
  · intro h
    by_contra hxy
    have hstrict : Strict r y x := ⟨(hr.1 x y).resolve_left hxy, hxy⟩
    exact (not_lt_of_ge h) (weightedUtility_strict hw hs hr.2 hD hstrict)

/-- The sufficient direction of **Proposition 1.12**, p. 11. -/
theorem represents_of_countable_separating (hr : Rational r) {D : Set X}
    (hc : D.Countable) (hD : OrderSeparating r D) : ∃ u : X → ℝ, Represents u r := by
  let : Countable D := hc.to_subtype
  obtain ⟨w, hw, hs⟩ := exists_positive_summable D
  exact ⟨WeightedUtility r D w, weightedUtility_represents hw hs hr hD⟩

/-- **Proposition 1.11**, pp. 10-11: every rational countable preference is representable. -/
theorem proposition_1_11 [Countable X] (hr : Rational r) :
    ∃ u : X → ℝ, Represents u r := by
  apply represents_of_countable_separating hr (Set.to_countable Set.univ)
  exact fun x y hxy => ⟨x, Set.mem_univ x, complete_refl hr.1 x, hxy⟩

/-- A representing utility also represents the strict comparison by strict inequality. -/
theorem strict_iff_utility_lt {u : X → ℝ} (hu : Represents u r) (x y : X) :
    Strict r x y ↔ u y < u x := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hle => h.2 ((hu y x).mpr hle))
  · intro h
    exact ⟨(hu x y).mpr h.le, fun hyx => (not_le_of_gt h) ((hu y x).mp hyx)⟩

/-- The necessary direction of **Proposition 1.12**, p. 12, including gaps in the range. -/
theorem countable_separating_of_represents {u : X → ℝ} (hu : Represents u r) :
    ∃ D : Set X, D.Countable ∧ OrderSeparating r D := by
  classical
  let I := {p : ℚ × ℚ // ∃ z : X, (p.1 : ℝ) < u z ∧ u z < (p.2 : ℝ)}
  let f : I → X := fun i => Classical.choose i.property
  have hf (i : I) : (i.val.1 : ℝ) < u (f i) ∧ u (f i) < (i.val.2 : ℝ) :=
    Classical.choose_spec i.property
  let J := {q : ℚ // ∃ z : X, (q : ℝ) < u z ∧ ∀ y, (q : ℝ) < u y → u z ≤ u y}
  let g : J → X := fun j => Classical.choose j.property
  have hg (j : J) : (j.val : ℝ) < u (g j) ∧
      ∀ y, (j.val : ℝ) < u y → u (g j) ≤ u y :=
    Classical.choose_spec j.property
  refine ⟨Set.range f ∪ Set.range g,
    (Set.countable_range f).union (Set.countable_range g), ?_⟩
  intro x y hxy
  have hlt := (strict_iff_utility_lt hu x y).mp hxy
  obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt
  by_cases hgap : ∃ z : X, (q : ℝ) < u z ∧ u z < u x
  · obtain ⟨z, hqz, hzx⟩ := hgap
    obtain ⟨t, hzt, htx⟩ := exists_rat_btwn hzx
    let i : I := ⟨(q, t), z, hqz, hzt⟩
    refine ⟨f i, Or.inl ⟨i, rfl⟩, (hu x (f i)).mpr ?_,
      (strict_iff_utility_lt hu (f i) y).mpr ?_⟩
    · exact ((hf i).2.trans htx).le
    · exact hyq.trans (hf i).1
  · have hmin : ∀ z : X, (q : ℝ) < u z → u x ≤ u z := by
      intro z hqz
      exact le_of_not_gt (fun hzx => hgap ⟨z, hqz, hzx⟩)
    let j : J := ⟨q, x, hqx, hmin⟩
    refine ⟨g j, Or.inr ⟨j, rfl⟩, (hu x (g j)).mpr ((hg j).2 x hqx),
      (strict_iff_utility_lt hu (g j) y).mpr ?_⟩
    exact hyq.trans (hg j).1

/-- **Proposition 1.12**, pp. 11-12: the full countable-subset criterion. -/
theorem proposition_1_12 (hr : Rational r) :
    (∃ u : X → ℝ, Represents u r) ↔ ∃ D : Set X, D.Countable ∧ OrderSeparating r D := by
  constructor
  · rintro ⟨u, hu⟩
    exact countable_separating_of_represents hu
  · rintro ⟨D, hc, hD⟩
    exact represents_of_countable_separating hr hc hD

end Kreps.ChoicePreferenceUtility
