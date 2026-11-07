/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.OrthantRepresentation

/-!
# Convex preferences and convex choice sets

Kreps I, Definition 2.4 and Propositions 2.5-2.6, p. 33; Problem 2.4, p. 46.
The statements are proved on any convex real-vector-space domain. Specializing the
domain to the nonnegative orthant gives the book's setting. Subtype mixtures retain
domain membership, and convexity of a menu is proved equivalent to Mathlib's ambient
set convexity. In particular, no nonemptiness of the maximizing set is assumed.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- A convex combination stays in its convex consumption domain. -/
def Mix (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- Weight zero selects the second bundle. -/
theorem mix_zero (hS : Convex ℝ S) (x y : S) (ha : (0 : ℝ) ∈ Set.Icc 0 1) :
    Mix hS x y 0 ha = y := by
  apply Subtype.ext
  simp [Mix]

/-- Weight one selects the first bundle. -/
theorem mix_one (hS : Convex ℝ S) (x y : S) (ha : (1 : ℝ) ∈ Set.Icc 0 1) :
    Mix hS x y 1 ha = x := by
  apply Subtype.ext
  simp [Mix]

/-- Mixing a bundle with itself leaves it unchanged. -/
theorem mix_self (hS : Convex ℝ S) (x : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Mix hS x x a ha = x := by
  apply Subtype.ext
  simp [Mix, ← add_smul]

/-- Reversing the endpoints replaces the weight by its complement. -/
theorem mix_swap (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Mix hS x y a ha =
      Mix hS y x (1 - a) ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩ := by
  apply Subtype.ext
  simp [Mix, add_comm]

/-- Convexity of a menu inside its convex domain. -/
def ConvexMenu (hS : Convex ℝ S) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a, ∀ ha : a ∈ Set.Icc 0 1, Mix hS x y a ha ∈ A

/-- The menu definition is exactly convexity of its image in the ambient vector space. -/
theorem convexMenu_iff (hS : Convex ℝ S) (A : Set S) :
    ConvexMenu hS A ↔ Convex ℝ (Subtype.val '' A) := by
  constructor
  · intro h x hx y hy a b ha hb hab
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    refine ⟨Mix hS x y a ha', h x hx y hy a ha', ?_⟩
    change a • x.val + (1 - a) • y.val = a • x.val + b • y.val
    rw [show 1 - a = b by linarith]
  · intro h x hx y hy a ha
    have hm := h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha.1
      (sub_nonneg.mpr ha.2) (show a + (1 - a) = 1 by ring)
    obtain ⟨z, hz, he⟩ := hm
    have hz' : z = Mix hS x y a ha := Subtype.ext he
    exact hz' ▸ hz

/-- **Definition 2.4a:** mixtures are weakly preferred to the worse endpoint. -/
def ConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- **Definition 2.4b:** interior mixtures of distinct comparable endpoints strictly improve. -/
def StrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- **Definition 2.4c:** convexity plus strict improvement when the endpoints differ in rank. -/
def SemiStrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ConvexPreference hS r ∧ ∀ x y, Strict r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- Strict convexity includes weak convexity, including endpoint and equal-bundle cases. -/
theorem strictlyConvex_convex {hS : Convex ℝ S} {r : S → S → Prop} (hc : Complete r)
    (hs : StrictlyConvexPreference hS r) : ConvexPreference hS r := by
  intro x y hxy a ha
  by_cases he : x = y
  · subst y
    rw [mix_self]
    exact complete_refl hc x
  by_cases h0 : a = 0
  · subst a
    rw [mix_zero]
    exact complete_refl hc y
  by_cases h1 : a = 1
  · subst a
    rw [mix_one]
    exact hxy
  exact (hs x y he hxy a ⟨lt_of_le_of_ne ha.1 (Ne.symm h0),
    lt_of_le_of_ne ha.2 h1⟩).1

/-- Strict convexity implies semi-strict convexity. -/
theorem strictlyConvex_semiStrict {hS : Convex ℝ S} {r : S → S → Prop} (hc : Complete r)
    (hs : StrictlyConvexPreference hS r) : SemiStrictlyConvexPreference hS r := by
  refine ⟨strictlyConvex_convex hc hs, fun x y hxy a ha => ?_⟩
  apply hs x y _ hxy.1 a ha
  intro he
  subst y
  exact hxy.2 hxy.1

/-- The upper-contour characterization, stated internally to the consumption domain. -/
theorem convexPreference_iff_contours {hS : Convex ℝ S} {r : S → S → Prop}
    (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, ConvexMenu hS (NoWorseThan r z) := by
  constructor
  · intro hc z x hx y hy a ha
    rcases hr.1 x y with hxy | hyx
    · exact hr.2 _ y z (hc x y hxy a ha) hy
    · change r (Mix hS x y a ha) z
      rw [mix_swap]
      exact hr.2 _ x z (hc y x hyx (1 - a)
        ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩) hx
  · intro h x y hxy a ha
    exact h y x hxy y (complete_refl hr.1 y) a ha

/-- **Proposition 2.5:** every NWT set is convex in the ambient vector space. -/
theorem proposition_2_5 {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, Convex ℝ (Subtype.val '' NoWorseThan r z) := by
  rw [convexPreference_iff_contours hr]
  exact forall_congr' fun z => convexMenu_iff hS (NoWorseThan r z)

/-- **Proposition 2.6**, convexity of the best set, which is allowed to be empty. -/
theorem proposition_2_6_convex {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r)
    (hc : ConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    ConvexMenu hS (PrefChoice r A) := by
  intro x hx y hy a ha
  refine ⟨hA x hx.1 y hy.1 a ha, fun z hz => ?_⟩
  exact hr.2 _ y z (hc x y (hx.2 y hy.1) a ha) (hy.2 z hz)

/-- **Proposition 2.6**, strict convexity gives at most one best bundle. -/
theorem proposition_2_6_unique {hS : Convex ℝ S} {r : S → S → Prop}
    (hs : StrictlyConvexPreference hS r) {A : Set S} (hA : ConvexMenu hS A) :
    (PrefChoice r A).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := hs x y hne (hx.2 y hy.1) (1 / 2) (by constructor <;> norm_num)
  exact hm.2 (hy.2 _ (hA x hx.1 y hy.1 (1 / 2) (by constructor <;> norm_num)))

/-- **Problem 2.4** is precisely the upper-contour equivalence. -/
theorem problem_2_4 {hS : Convex ℝ S} {r : S → S → Prop} (hr : Rational r) :
    ConvexPreference hS r ↔ ∀ z, Convex ℝ (Subtype.val '' NoWorseThan r z) :=
  proposition_2_5 hr

end Kreps.PreferenceProperties
