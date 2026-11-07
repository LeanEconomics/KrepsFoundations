/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousUtility

/-!
# Every indifference class meets the diagonal

Kreps I, the diagonal construction in Steps 2-3, pp. 37-38. The book brackets
a bundle between the diagonal bundles formed from its minimum and maximum
coordinates. Lemma 2.10 supplies an indifferent diagonal bundle. Positive dimension
is explicit because those coordinate extrema require a nonempty set of goods.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ}

/-- The diagonal bundle with the same nonnegative amount of every commodity. -/
def Diagonal (a : Set.Ici (0 : ℝ)) : NonnegativeOrthant k :=
  ⟨fun _ => a.val, fun _ => a.property⟩

/-- The diagonal parametrization is continuous. -/
theorem diagonal_continuous : Continuous (Diagonal (k := k)) :=
  (continuous_pi fun _ => continuous_subtype_val).subtype_mk _

/-- The smallest coordinate, in the positive-dimensional setting of the construction. -/
noncomputable def MinCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x.val

/-- The largest coordinate. -/
noncomputable def MaxCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x.val

/-- A nonnegative bundle has nonnegative minimum coordinate. -/
theorem minCoordinate_nonneg (hk : 0 < k) (x : NonnegativeOrthant k) :
    0 ≤ MinCoordinate hk x := by
  unfold MinCoordinate
  exact Finset.le_inf' _ _ (fun j _ => x.property j)

/-- Each coordinate lies above the minimum. -/
theorem minCoordinate_le (hk : 0 < k) (x : NonnegativeOrthant k) (j : Fin k) :
    MinCoordinate hk x ≤ x.val j := Finset.inf'_le _ (Finset.mem_univ j)

/-- Each coordinate lies below the maximum. -/
theorem le_maxCoordinate (hk : 0 < k) (x : NonnegativeOrthant k) (j : Fin k) :
    x.val j ≤ MaxCoordinate hk x := Finset.le_sup' _ (Finset.mem_univ j)

/-- A nonnegative bundle has nonnegative maximum coordinate. -/
theorem maxCoordinate_nonneg (hk : 0 < k) (x : NonnegativeOrthant k) :
    0 ≤ MaxCoordinate hk x :=
  (x.property ⟨0, hk⟩).trans (le_maxCoordinate hk x ⟨0, hk⟩)

/-- Step 2: every bundle is indifferent to a point on the diagonal. -/
theorem diagonal_indifference_exists (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    ∃ a : Set.Ici (0 : ℝ), Indifferent r (Diagonal a) x := by
  let lo := MinCoordinate hk x
  let hi := MaxCoordinate hk x
  have hlo : 0 ≤ lo := minCoordinate_nonneg hk x
  have hhi : 0 ≤ hi := maxCoordinate_nonneg hk x
  let f (t : UnitSegment) : NonnegativeOrthant k :=
    ⟨fun _ => t.val * lo + (1 - t.val) * hi,
      fun _ => add_nonneg (mul_nonneg t.property.1 hlo)
        (mul_nonneg (sub_nonneg.mpr t.property.2) hhi)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const)
  have h0 : r (f ⟨0, by norm_num⟩) x := by
    apply hm
    intro j
    simpa [f] using le_maxCoordinate hk x j
  have h1 : r x (f ⟨1, by norm_num⟩) := by
    apply hm
    intro j
    simpa [f] using minCoordinate_le hk x j
  obtain ⟨t, ht⟩ := lemma_2_10 hr hc f hf x h0 h1
  exact ⟨⟨t.val * lo + (1 - t.val) * hi,
    add_nonneg (mul_nonneg t.property.1 hlo)
      (mul_nonneg (sub_nonneg.mpr t.property.2) hhi)⟩, ht⟩

/-- Step 3: the diagonal's numerical coordinate represents its preference order. -/
theorem diagonal_weak_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : MonotonePreference r) (hs : StrictAllIncreasePreference r)
    (a b : Set.Ici (0 : ℝ)) : r (Diagonal a) (Diagonal b) ↔ b.val ≤ a.val := by
  constructor
  · intro hab
    by_contra hnot
    exact (hs (Diagonal b) (Diagonal a) (fun _ => lt_of_not_ge hnot)).2 hab
  · intro hba
    exact hm _ _ (fun _ => hba)

/-- Equal diagonal ranks mean equal coordinates, including the boundary at zero. -/
theorem diagonal_indifferent_iff
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : MonotonePreference r) (hs : StrictAllIncreasePreference r)
    (a b : Set.Ici (0 : ℝ)) : Indifferent r (Diagonal a) (Diagonal b) ↔ a = b := by
  change (r (Diagonal a) (Diagonal b) ∧ r (Diagonal b) (Diagonal a)) ↔ a = b
  rw [diagonal_weak_iff hm hs, diagonal_weak_iff hm hs]
  exact ⟨fun h => Subtype.ext (le_antisymm h.2 h.1), fun h => by cases h; exact ⟨le_rfl, le_rfl⟩⟩

end Kreps.PreferenceProperties
