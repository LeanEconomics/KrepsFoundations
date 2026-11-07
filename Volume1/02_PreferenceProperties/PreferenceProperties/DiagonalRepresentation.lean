/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.DiagonalBounds

/-!
# The diagonal continuous representation

Kreps I, Steps 3-5 of the construction on pp. 37-38. Each bundle has a unique
indifferent diagonal coordinate. That coordinate represents the preference and
is continuous. The continuity proof uses open strict contours and the exact
nonnegative range, including its zero endpoint. The extra monotonicity assumptions
remain explicit; this module does not claim the general converse of Proposition 2.9.
-/

namespace Kreps.PreferenceProperties

variable {k : ℕ} {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- Step 4: two indifferent diagonal representatives of a bundle have the same coordinate. -/
theorem diagonal_indifference_unique (hr : Rational r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) {x : NonnegativeOrthant k}
    {a b : Set.Ici (0 : ℝ)} (ha : Indifferent r (Diagonal a) x)
    (hb : Indifferent r (Diagonal b) x) : a = b := by
  apply (diagonal_indifferent_iff hm hs a b).mp
  exact ⟨hr.2 _ x _ ha.1 hb.2, hr.2 _ x _ hb.1 ha.2⟩

/-- The existence and uniqueness needed to define the diagonal utility. -/
theorem diagonal_indifference_existsUnique (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) (x : NonnegativeOrthant k) :
    ∃! a : Set.Ici (0 : ℝ), Indifferent r (Diagonal a) x := by
  obtain ⟨a, ha⟩ := diagonal_indifference_exists hk hr hc hm x
  exact ⟨a, ha, fun b hb => diagonal_indifference_unique hr hm hs hb ha⟩

/-- Select the diagonal coordinate; the uniqueness theorem makes it canonical under strictness. -/
noncomputable def DiagonalCoordinate (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (x : NonnegativeOrthant k) : Set.Ici (0 : ℝ) :=
  Classical.choose (diagonal_indifference_exists hk hr hc hm x)

/-- The selected coordinate has precisely the required indifference property. -/
theorem diagonalCoordinate_spec (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    Indifferent r (Diagonal (DiagonalCoordinate hk hr hc hm x)) x :=
  Classical.choose_spec (diagonal_indifference_exists hk hr hc hm x)

/-- Step 4's real-valued utility: the location of the indifferent diagonal bundle. -/
noncomputable def DiagonalUtility (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (x : NonnegativeOrthant k) : ℝ := (DiagonalCoordinate hk hr hc hm x).val

/-- The diagonal scale is nonnegative even when some goods have zero consumption. -/
theorem diagonalUtility_nonneg (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r) (x : NonnegativeOrthant k) :
    0 ≤ DiagonalUtility hk hr hc hm x := (DiagonalCoordinate hk hr hc hm x).property

/-- Step 5's ordinal representation assertion. -/
theorem diagonalUtility_represents (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) : Represents (DiagonalUtility hk hr hc hm) r := by
  intro x y
  have hx := diagonalCoordinate_spec hk hr hc hm x
  have hy := diagonalCoordinate_spec hk hr hc hm y
  constructor
  · intro hxy
    have hdiag := hr.2 _ x _ hx.1 (hr.2 x y _ hxy hy.2)
    exact (diagonal_weak_iff hm hs _ _).mp hdiag
  · intro hxy
    have hdiag := (diagonal_weak_iff hm hs
      (DiagonalCoordinate hk hr hc hm x) (DiagonalCoordinate hk hr hc hm y)).mpr hxy
    exact hr.2 x _ y hx.2 (hr.2 _ _ y hdiag hy.1)

/-- On the diagonal itself, utility is exactly the common commodity quantity. -/
theorem diagonalUtility_diagonal (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) (a : Set.Ici (0 : ℝ)) :
    DiagonalUtility hk hr hc hm (Diagonal a) = a.val := by
  have he := (diagonal_indifferent_iff hm hs _ a).mp
    (diagonalCoordinate_spec hk hr hc hm (Diagonal a))
  exact congrArg Subtype.val he

/-- An exact nonnegative utility range converts continuous strict contours into continuity. -/
theorem continuous_of_full_nonnegative_range {X : Type*} [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r)
    (hc : ContinuousPreference r) (hn : ∀ x, 0 ≤ u x)
    (hfull : ∀ a : ℝ, 0 ≤ a → ∃ x, u x = a) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  by_cases ha : 0 ≤ a
  · obtain ⟨z, hz⟩ := hfull a ha
    have hgt : u ⁻¹' Set.Ioi a = StrictlyBetterThan r z := by
      ext x
      change a < u x ↔ Strict r x z
      rw [strict_iff_utility_lt hu, hz]
    have hlt : u ⁻¹' Set.Iio a = StrictlyWorseThan r z := by
      ext x
      change u x < a ↔ Strict r z x
      rw [strict_iff_utility_lt hu, hz]
    exact ⟨hgt ▸ (ho z).1, hlt ▸ (ho z).2⟩
  · have hgt : u ⁻¹' Set.Ioi a = Set.univ := by
      ext x
      change (a < u x) ↔ True
      exact iff_true_intro (lt_of_lt_of_le (lt_of_not_ge ha) (hn x))
    have hlt : u ⁻¹' Set.Iio a = ∅ := by
      ext x
      change (u x < a) ↔ False
      exact iff_false_intro (not_lt_of_ge ((le_of_lt (lt_of_not_ge ha)).trans (hn x)))
    exact ⟨hgt ▸ isOpen_univ, hlt ▸ isOpen_empty⟩

/-- Step 5's continuity assertion, including the zero endpoint of the diagonal. -/
theorem diagonalUtility_continuous (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) : Continuous (DiagonalUtility hk hr hc hm) := by
  apply continuous_of_full_nonnegative_range (diagonalUtility_represents hk hr hc hm hs) hc
    (diagonalUtility_nonneg hk hr hc hm)
  intro a ha
  exact ⟨Diagonal ⟨a, ha⟩, diagonalUtility_diagonal hk hr hc hm hs ⟨a, ha⟩⟩

/-- **Proposition 2.9 with the extra assumptions**, proved by all five diagonal steps. -/
theorem proposition_2_9_monotone (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hm : MonotonePreference r)
    (hs : StrictAllIncreasePreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  ⟨DiagonalUtility hk hr hc hm, diagonalUtility_represents hk hr hc hm hs,
    diagonalUtility_continuous hk hr hc hm hs⟩

/-- Footnote 6, p. 36: weak monotonicity follows from the other assumptions. -/
theorem continuous_representation_strictAllIncrease (hk : 0 < k) (hr : Rational r)
    (hc : ContinuousPreference r) (hs : StrictAllIncreasePreference r) :
    ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  proposition_2_9_monotone hk hr hc (continuous_strictAllIncrease_monotone hr hc hs) hs

end Kreps.PreferenceProperties
