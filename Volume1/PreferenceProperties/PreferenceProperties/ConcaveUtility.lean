/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConvexPreference
import PreferenceProperties.UtilityEquivalence
import Mathlib.Analysis.Convex.Quasiconvex

/-!
# Concavity, quasi-concavity and representation

Kreps I, Definition 2.7 and Proposition 2.8, pp. 34-35. Functions are defined on
the convex consumption domain, without arbitrary values outside it. The bridge
theorems identify these domain-internal definitions with Mathlib's `ConcaveOn`,
`StrictConcaveOn` and `QuasiconcaveOn` for ambient functions restricted to the domain.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- **Definition 2.7a:** Jensen's concavity inequality. -/
def ConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1,
    a * u x + (1 - a) * u y ≤ u (Mix hS x y a ha)

/-- **Definition 2.7b:** strict Jensen inequality for distinct endpoints and interior weights. -/
def StrictlyConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    a * u x + (1 - a) * u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- **Definition 2.7c:** a mixture is no worse than the lower-valued endpoint. -/
def QuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, min (u x) (u y) ≤ u (Mix hS x y a ha)

/-- **Definition 2.7d:** quasi-concavity and strict improvement over a strictly worse endpoint. -/
def SemiStrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  QuasiConcaveUtility hS u ∧ ∀ x y, u y < u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- **Definition 2.7e:** distinct weakly ordered endpoints give a strict improvement. -/
def StrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

/-- The domain-internal concavity definition is Mathlib concavity for restricted functions. -/
theorem concaveUtility_iff_concaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    ConcaveUtility hS (fun x => f x.val) ↔ ConcaveOn ℝ S f := by
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- The corresponding bridge for strict concavity. -/
theorem strictlyConcaveUtility_iff_strictConcaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    StrictlyConcaveUtility hS (fun x => f x.val) ↔ StrictConcaveOn ℝ S f := by
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy hne a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hne (congrArg Subtype.val he))
      a ⟨ha, by linarith⟩
  · intro h x y hne a ha
    exact h.2 x.property y.property (fun he => hne (Subtype.ext he))
      ha.1 (sub_pos.mpr ha.2) (by ring)

/-- The minimum formulation agrees with Mathlib's upper-contour definition. -/
theorem quasiConcaveUtility_iff_quasiconcaveOn (hS : Convex ℝ S) (f : E → ℝ) :
    QuasiConcaveUtility hS (fun x => f x.val) ↔ QuasiconcaveOn ℝ S f := by
  rw [quasiconcaveOn_iff_min_le]
  constructor
  · intro h
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    have he : b = 1 - a := by linarith
    subst b
    exact h ⟨x, hx⟩ ⟨y, hy⟩ a ⟨ha, by linarith⟩
  · intro h x y a ha
    exact h.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)

/-- Concavity implies quasi-concavity by comparing the weighted average with its smaller term. -/
theorem concaveUtility_quasi {hS : Convex ℝ S} {u : S → ℝ}
    (hc : ConcaveUtility hS u) : QuasiConcaveUtility hS u := by
  intro x y a ha
  calc
    min (u x) (u y) = a * min (u x) (u y) + (1 - a) * min (u x) (u y) := by ring
    _ ≤ a * u x + (1 - a) * u y := add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left _ _) ha.1)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (sub_nonneg.mpr ha.2))
    _ ≤ u (Mix hS x y a ha) := hc x y a ha

/-- Concavity also gives the semi-strict improvement used in later counterexamples. -/
theorem concaveUtility_semiStrict {hS : Convex ℝ S} {u : S → ℝ}
    (hc : ConcaveUtility hS u) : SemiStrictlyQuasiConcaveUtility hS u := by
  refine ⟨concaveUtility_quasi hc, fun x y hyx a ha => ?_⟩
  have hg := mul_pos ha.1 (sub_pos.mpr hyx)
  have hm := hc x y a ⟨ha.1.le, ha.2.le⟩
  nlinarith

/-- Strict concavity implies strict quasi-concavity. -/
theorem strictlyConcaveUtility_strictQuasi {hS : Convex ℝ S} {u : S → ℝ}
    (hc : StrictlyConcaveUtility hS u) : StrictlyQuasiConcaveUtility hS u := by
  intro x y hne hyx a ha
  have hg := mul_nonneg ha.1.le (sub_nonneg.mpr hyx)
  have hm := hc x y hne a ha
  nlinarith

/-- **Proposition 2.8b**, quasi-concavity iff preference convexity. -/
theorem proposition_2_8b_quasi {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) : QuasiConcaveUtility hS u ↔ ConvexPreference hS r := by
  constructor
  · intro h x y hxy a ha
    apply (hu _ y).mpr
    have hyx := (hu x y).mp hxy
    simpa only [min_eq_right hyx] using h x y a ha
  · intro h x y a ha
    rcases le_total (u y) (u x) with hyx | hxy
    · rw [min_eq_right hyx]
      exact (hu _ y).mp (h x y ((hu x y).mpr hyx) a ha)
    · rw [min_eq_left hxy, mix_swap]
      exact (hu _ x).mp (h y x ((hu y x).mpr hxy) (1 - a)
        ⟨sub_nonneg.mpr ha.2, by linarith [ha.1]⟩)

/-- **Proposition 2.8b**, strict quasi-concavity iff strict preference convexity. -/
theorem proposition_2_8b_strict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) :
    StrictlyQuasiConcaveUtility hS u ↔ StrictlyConvexPreference hS r := by
  constructor
  · intro h x y hne hxy a ha
    exact (strict_iff_utility_lt hu _ y).mpr (h x y hne ((hu x y).mp hxy) a ha)
  · intro h x y hne hyx a ha
    exact (strict_iff_utility_lt hu _ y).mp (h x y hne ((hu x y).mpr hyx) a ha)

/-- **Proposition 2.8b**, semi-strict quasi-concavity iff semi-strict preference convexity. -/
theorem proposition_2_8b_semiStrict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) :
    SemiStrictlyQuasiConcaveUtility hS u ↔ SemiStrictlyConvexPreference hS r := by
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨(proposition_2_8b_quasi hu).mp hq, fun x y hxy a ha => ?_⟩
    exact (strict_iff_utility_lt hu _ y).mpr
      (hs x y ((strict_iff_utility_lt hu x y).mp hxy) a ha)
  · rintro ⟨hq, hs⟩
    refine ⟨(proposition_2_8b_quasi hu).mpr hq, fun x y hyx a ha => ?_⟩
    exact (strict_iff_utility_lt hu _ y).mp
      (hs x y ((strict_iff_utility_lt hu x y).mpr hyx) a ha)

/-- **Proposition 2.8a**, a concave representation gives convex preference. -/
theorem proposition_2_8a_concave {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) (hc : ConcaveUtility hS u) : ConvexPreference hS r :=
  (proposition_2_8b_quasi hu).mp (concaveUtility_quasi hc)

/-- **Proposition 2.8a**, the strict version. -/
theorem proposition_2_8a_strict {hS : Convex ℝ S} {r : S → S → Prop} {u : S → ℝ}
    (hu : Represents u r) (hc : StrictlyConcaveUtility hS u) :
    StrictlyConvexPreference hS r :=
  (proposition_2_8b_strict hu).mp (strictlyConcaveUtility_strictQuasi hc)

/-- The conclusion on p. 35: increasing ordinal rescaling preserves quasi-concavity. -/
theorem quasiConcave_strictMono_transform {hS : Convex ℝ S} {u : S → ℝ}
    (hq : QuasiConcaveUtility hS u) {f : ℝ → ℝ} (hf : StrictMono f) :
    QuasiConcaveUtility hS (f ∘ u) := by
  intro x y a ha
  change min (f (u x)) (f (u y)) ≤ f (u (Mix hS x y a ha))
  rw [← hf.monotone.map_min]
  exact hf.monotone (hq x y a ha)

end Kreps.PreferenceProperties
