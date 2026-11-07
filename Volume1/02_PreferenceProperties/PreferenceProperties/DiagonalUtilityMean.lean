/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.BisymmetricMeanGrid
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The diagonal-inverse utility mean

Preparation for Kreps I, Proposition 2.14. A continuous utility that increases
strictly in both coordinates defines a unique mean: its diagonal value equals
the utility of the two inputs. The mean is continuous and strictly increasing.
A partial medial identity for the surrounding utility operation makes the
mean bisymmetric, without assuming a cardinal representation.
-/

namespace Kreps.PreferenceProperties

variable {A : Type*} {F : A → A → ℝ}

/-- A utility strictly increasing in both coordinates has a strictly increasing diagonal. -/
theorem utilityDiagonal_strictMono [LinearOrder A] (hl : ∀ y, StrictMono (fun x => F x y))
    (hr : ∀ x, StrictMono (F x)) : StrictMono (fun x => F x x) := by
  intro x y hxy
  exact (hl x hxy).trans (hr y hxy)

/-- Connectedness makes every pair's utility value attainable on the diagonal. -/
theorem utilityDiagonal_attains_pair [LinearOrder A] [TopologicalSpace A] [PreconnectedSpace A]
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hc : Continuous (fun x => F x x)) (x y : A) : ∃ z, F z z = F x y := by
  have hI := (isPreconnected_range hc).ordConnected
  rcases le_total x y with hxy | hyx
  · exact hI.out ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨(hr x).monotone hxy, (hl y).monotone hxy⟩
  · exact hI.out ⟨y, rfl⟩ ⟨x, rfl⟩ ⟨(hl y).monotone hyx, (hr x).monotone hyx⟩

/-- The unique equal-coordinate bundle with the same utility as the input pair. -/
noncomputable def DiagonalUtilityMean (F : A → A → ℝ)
    (he : ∀ x y, ∃ z, F z z = F x y) (x y : A) : A := Classical.choose (he x y)

/-- The defining indifference equation for the diagonal mean. -/
theorem diagonalUtilityMean_spec (he : ∀ x y, ∃ z, F z z = F x y) (x y : A) :
    F (DiagonalUtilityMean F he x y) (DiagonalUtilityMean F he x y) = F x y :=
  Classical.choose_spec (he x y)

/-- Equal inputs are fixed by the diagonal mean. -/
theorem diagonalUtilityMean_reflexive (he : ∀ x y, ∃ z, F z z = F x y)
    (hd : Function.Injective (fun x => F x x)) (x : A) :
    DiagonalUtilityMean F he x x = x := hd (diagonalUtilityMean_spec he x x)

/-- A symmetric pair utility induces a symmetric diagonal mean. -/
theorem diagonalUtilityMean_symmetric (he : ∀ x y, ∃ z, F z z = F x y)
    (hd : Function.Injective (fun x => F x x)) (hs : ∀ x y, F x y = F y x) (x y : A) :
    DiagonalUtilityMean F he x y = DiagonalUtilityMean F he y x := by
  apply hd
  change F (DiagonalUtilityMean F he x y) (DiagonalUtilityMean F he x y) =
    F (DiagonalUtilityMean F he y x) (DiagonalUtilityMean F he y x)
  rw [diagonalUtilityMean_spec he x y, diagonalUtilityMean_spec he y x, hs]

/-- The mean is strictly increasing in its first coordinate. -/
theorem diagonalUtilityMean_strictMono_left [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x)) (y : A) :
    StrictMono (fun x => DiagonalUtilityMean F he x y) := by
  intro x z hxz
  apply (utilityDiagonal_strictMono hl hr).lt_iff_lt.mp
  simpa only [diagonalUtilityMean_spec] using hl y hxz

/-- The mean is strictly increasing in its second coordinate. -/
theorem diagonalUtilityMean_strictMono_right [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x)) (x : A) :
    StrictMono (DiagonalUtilityMean F he x) := by
  intro y z hyz
  apply (utilityDiagonal_strictMono hl hr).lt_iff_lt.mp
  simpa only [diagonalUtilityMean_spec] using hr x hyz

/-- Comparing pair utilities is equivalent to comparing their diagonal means. -/
theorem diagonalUtilityMean_comparison [LinearOrder A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (a b c d : A) :
    F a b ≤ F c d ↔ DiagonalUtilityMean F he a b ≤ DiagonalUtilityMean F he c d := by
  rw [← diagonalUtilityMean_spec he a b, ← diagonalUtilityMean_spec he c d]
  exact (utilityDiagonal_strictMono hl hr).le_iff_le

/-- The inverse diagonal is continuous on its attained interval, so the mean is continuous. -/
theorem diagonalUtilityMean_continuous [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
    [PreconnectedSpace A] (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hc : Continuous (fun p : A × A => F p.1 p.2)) :
    Continuous (fun p : A × A => DiagonalUtilityMean F he p.1 p.2) := by
  have hd := utilityDiagonal_strictMono hl hr
  have hdc : Continuous (fun x => F x x) := hc.comp (continuous_id.prodMk continuous_id)
  let : Set.OrdConnected (Set.range (fun x => F x x)) := (isPreconnected_range hdc).ordConnected
  let e : A ≃o Set.range (fun x => F x x) := hd.orderIso (fun x => F x x)
  have hg : Continuous (fun p : A × A =>
      (⟨F p.1 p.2, he p.1 p.2⟩ : Set.range (fun x => F x x))) := hc.subtype_mk _
  convert e.symm.continuous.comp hg using 1
  funext p
  apply e.injective
  change e (DiagonalUtilityMean F he p.1 p.2) =
    e (e.symm ⟨F p.1 p.2, by exact he p.1 p.2⟩)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact diagonalUtilityMean_spec he p.1 p.2

/-- A numerical operation has the medial identity wherever its four intermediate values exist. -/
def PartialUtilityMedial {B : Type*} (G : B → B → ℝ) (f : B → ℝ) : Prop :=
  ∀ a b c d p q s t, G a b = f p → G c d = f q → G a c = f s → G b d = f t →
    G p q = G s t

/-- The partial medial identity of the surrounding operation gives a bisymmetric diagonal mean. -/
theorem diagonalUtilityMean_bisymmetric {B : Type*} (G : B → B → ℝ) (f : B → ℝ)
    (k : A → B) (he : ∀ x y, ∃ z, F z z = F x y)
    (hF : ∀ x y, F x y = G (k x) (k y))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p))
    (hdF : Function.Injective (fun x => F x x)) (a b c d : A) :
    DiagonalUtilityMean F he (DiagonalUtilityMean F he a b) (DiagonalUtilityMean F he c d) =
      DiagonalUtilityMean F he (DiagonalUtilityMean F he a c) (DiagonalUtilityMean F he b d) := by
  let M := DiagonalUtilityMean F he
  obtain ⟨p, hp⟩ := hsmall a b
  obtain ⟨q, hq⟩ := hsmall c d
  obtain ⟨s, hs⟩ := hsmall a c
  obtain ⟨t, ht⟩ := hsmall b d
  obtain ⟨v, hv⟩ := hsmall (M a b) (M c d)
  obtain ⟨w, hw⟩ := hsmall (M a c) (M b d)
  have hdiag (x y : A) : G (k (M x y)) (k (M x y)) = G (k x) (k y) := by
    rw [← hF, ← hF]
    exact diagonalUtilityMean_spec he x y
  have hvw : v = w := by
    apply hd
    calc
      G v v = G p q := hmed (k (M a b)) (k (M c d)) (k (M a b)) (k (M c d))
        v v p q hv hv ((hdiag a b).trans hp) ((hdiag c d).trans hq)
      _ = G s t := hmed (k a) (k b) (k c) (k d) p q s t hp hq hs ht
      _ = G w w := (hmed (k (M a c)) (k (M b d)) (k (M a c)) (k (M b d))
        w w s t hw hw ((hdiag a c).trans hs) ((hdiag b d).trans ht)).symm
  apply hdF
  change F (M (M a b) (M c d)) (M (M a b) (M c d)) =
    F (M (M a c) (M b d)) (M (M a c) (M b d))
  rw [diagonalUtilityMean_spec he (M a b) (M c d),
    diagonalUtilityMean_spec he (M a c) (M b d), hF, hF, hv, hw, hvw]

/-- Package the derived diagonal mean for the dyadic cardinal-scale construction. -/
noncomputable def OrderedUtilityMean [LinearOrder A] {B : Type*} (G : B → B → ℝ) (f : B → ℝ)
    (k : A → B) (he : ∀ x y, ∃ z, F z z = F x y)
    (hl : ∀ y, StrictMono (fun x => F x y)) (hr : ∀ x, StrictMono (F x))
    (hs : ∀ x y, F x y = F y x) (hF : ∀ x y, F x y = G (k x) (k y))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p)) :
    OrderedBisymmetricMean A where
  mean := DiagonalUtilityMean F he
  reflexive := diagonalUtilityMean_reflexive he (utilityDiagonal_strictMono hl hr).injective
  symmetric := diagonalUtilityMean_symmetric he (utilityDiagonal_strictMono hl hr).injective hs
  bisymmetric := diagonalUtilityMean_bisymmetric G f k he hF hsmall hmed hd
    (utilityDiagonal_strictMono hl hr).injective
  strictMono_left := diagonalUtilityMean_strictMono_left he hl hr
  strictMono_right := diagonalUtilityMean_strictMono_right he hl hr

end Kreps.PreferenceProperties
