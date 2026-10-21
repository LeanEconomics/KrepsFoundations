/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConcaveUtility

/-!
# Appendix 3: quasi-concavity and maximizers

Kreps I, Definition A3.18 and Propositions A3.19–A3.22, pp. 464–465.
The utility definitions are shared with Chapter 2. Maximizers are expressed using
universal comparisons, which handles empty sets and unbounded utilities without
assigning a real-valued supremum to an unbounded set.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition A3.18d:** a mixture does not exceed the larger endpoint utility. -/
def QuasiConvexUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, u (Mix hS x y a ha) ≤ max (u x) (u y)

/-- **Definition A3.18e:** distinct ordered endpoints give a strict decrease. -/
def StrictlyQuasiConvexUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) < u x

/-- **Proposition A3.19:** quasi-concavity is convexity of every upper contour. -/
theorem proposition_A3_19 (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConcaveUtility hS (fun x => f x.val) ↔ ∀ r, Convex ℝ {x ∈ S | r ≤ f x} :=
  quasiConcaveUtility_iff_quasiconcaveOn hS f

/-- **Proposition A3.19**, footnote: quasi-convexity is convexity of every lower contour. -/
theorem proposition_A3_19_quasiConvex (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConvexUtility hS (fun x => f x.val) ↔ ∀ r, Convex ℝ {x ∈ S | f x ≤ r} := by
  change QuasiConvexUtility hS (fun x => f x.val) ↔ QuasiconvexOn ℝ S f
  rw [quasiconvexOn_iff_le_max]
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- **Proposition A3.20:** every nondecreasing transformation preserves quasi-concavity. -/
theorem proposition_A3_20 {hS : Convex ℝ S} {u : S → ℝ} {g : ℝ → ℝ}
    (hu : QuasiConcaveUtility hS u) (hg : Monotone g) :
    QuasiConcaveUtility hS (g ∘ u) := by
  intro x y a ha
  change min (g (u x)) (g (u y)) ≤ g (u (Mix hS x y a ha))
  rw [← hg.map_min]
  exact hg (hu x y a ha)

/-- **Proposition A3.20:** strictly increasing transformations preserve strict quasi-concavity. -/
theorem proposition_A3_20_strict {hS : Convex ℝ S} {u : S → ℝ} {g : ℝ → ℝ}
    (hu : StrictlyQuasiConcaveUtility hS u) (hg : StrictMono g) :
    StrictlyQuasiConcaveUtility hS (g ∘ u) := by
  intro x y hne hyx a ha
  exact hg (hu x y hne (hg.le_iff_le.mp hyx) a ha)

/-- **Proposition A3.21:** the maximizers on a convex menu form a convex set. -/
theorem proposition_A3_21 {hS : Convex ℝ S} {u : S → ℝ}
    (hu : QuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    ConvexMenu hS (UtilityChoice u A) := by
  intro x hx y hy a ha
  refine ⟨hA x hx.1 y hy.1 a ha, fun z hz => ?_⟩
  exact (le_min (hx.2 z hz) (hy.2 z hz)).trans (hu x y a ha)

/-- **Proposition A3.21:** strict quasi-concavity gives at most one maximizer. -/
theorem proposition_A3_21_unique {hS : Convex ℝ S} {u : S → ℝ}
    (hu : StrictlyQuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    (UtilityChoice u A).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := hu x y hne (hx.2 y hy.1) (1 / 2) (by constructor <;> norm_num)
  exact (not_lt_of_ge (hy.2 _
    (hA x hx.1 y hy.1 (1 / 2) (by constructor <;> norm_num)))) hm

/-- The maximizer convexity assertion in the ambient-vector-space formulation. -/
theorem proposition_A3_21_ambient {hS : Convex ℝ S} {u : S → ℝ}
    (hu : QuasiConcaveUtility hS u) {A : Set S} (hA : ConvexMenu hS A) :
    Convex ℝ (Subtype.val '' UtilityChoice u A) :=
  (convexMenu_iff hS _).mp (proposition_A3_21 hu hA)

/-- **Proposition A3.22:** concavity implies semi-strict quasi-concavity. -/
theorem proposition_A3_22_concave {hS : Convex ℝ S} {u : S → ℝ}
    (hu : ConcaveUtility hS u) : SemiStrictlyQuasiConcaveUtility hS u :=
  concaveUtility_semiStrict hu

/-- **Proposition A3.22:** strict concavity implies strict quasi-concavity. -/
theorem proposition_A3_22_strict {hS : Convex ℝ S} {u : S → ℝ}
    (hu : StrictlyConcaveUtility hS u) : StrictlyQuasiConcaveUtility hS u :=
  strictlyConcaveUtility_strictQuasi hu

end Kreps.PreferenceProperties
