/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.SimpleLottery

/-!
# Positive affine uniqueness of mixture and prize utilities

Kreps I, Propositions 5.3–5.4, pp. 88–96. Two mixture-affine representations
of one ranking have a common slope. A third alternative can lie below, between
or above the chosen anchors. Constant preferences and empty domains are included.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z X : Type*} [ConvexSpace ℝ Z]

/-- Mixture affinity and identical rankings put ordered triples on the same affine line. -/
theorem affine_segment_identity {u v : Z → ℝ} (hu : AffineInMix u) (hv : AffineInMix v)
    (hr : ∀ x y, u x ≤ u y ↔ v x ≤ v y) {l m h : Z}
    (hl : u l ≤ u m) (hh : u m ≤ u h) (hlt : u l < u h) :
    (v m - v l) * (u h - u l) = (u m - u l) * (v h - v l) := by
  have hd := sub_pos.mpr hlt
  let a : Weight := ⟨(u m - u l) / (u h - u l),
    div_nonneg (sub_nonneg.mpr hl) hd.le, (div_le_one hd).mpr (by linarith)⟩
  have hweight : a.val * (u h - u l) = u m - u l := div_mul_cancel₀ _ hd.ne'
  have he : u (Mix a h l) = u m := by
    rw [hu]
    linarith only [hweight]
  have hev : v (Mix a h l) = v m :=
    le_antisymm ((hr _ _).mp he.le) ((hr _ _).mp he.ge)
  rw [hv] at hev
  calc
    (v m - v l) * (u h - u l) = (a.val * (u h - u l)) * (v h - v l) := by
      rw [← hev]
      ring
    _ = _ := by rw [hweight]

/-- Positive affine uniqueness for arbitrary mixture-affine numerical representations. -/
theorem affineInMix_unique {u v : Z → ℝ} (hu : AffineInMix u) (hv : AffineInMix v)
    (hr : ∀ x y, u x ≤ u y ↔ v x ≤ v y) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, v x = A * u x + B := by
  classical
  by_cases hn : ∃ l h, u l < u h
  · obtain ⟨l, h, hlh⟩ := hn
    have hd := sub_pos.mpr hlh
    have hvlt : v l < v h := lt_of_not_ge (fun e => hlh.not_ge ((hr h l).mpr e))
    let A := (v h - v l) / (u h - u l)
    have hA : A * (u h - u l) = v h - v l := div_mul_cancel₀ _ hd.ne'
    refine ⟨A, div_pos (sub_pos.mpr hvlt) hd, v l - A * u l, fun x => ?_⟩
    have cross : (v x - v l) * (u h - u l) = (u x - u l) * (v h - v l) := by
      by_cases hb : u x < u l
      · have he := affine_segment_identity hu hv hr hb.le hlh.le (hb.trans hlh)
        linarith only [he]
      · by_cases ht : u h < u x
        · have he := affine_segment_identity hu hv hr hlh.le ht.le (hlh.trans ht)
          linarith only [he]
        · exact affine_segment_identity hu hv hr (le_of_not_gt hb) (le_of_not_gt ht) hlh
    rw [← hA] at cross
    apply (mul_left_inj' hd.ne').mp
    linarith only [cross]
  · cases isEmpty_or_nonempty Z with
    | inl he =>
      exact ⟨1, zero_lt_one, 0, fun x => isEmptyElim x⟩
    | inr he =>
      obtain ⟨b⟩ := he
      have hall (x y : Z) : u x ≤ u y := le_of_not_gt (fun h => hn ⟨_, _, h⟩)
      refine ⟨1, zero_lt_one, v b - u b, fun x => ?_⟩
      have heq := le_antisymm (hall x b) (hall b x)
      have hveq := le_antisymm ((hr x b).mp (hall x b)) ((hr b x).mp (hall b x))
      linarith

/-- The uniqueness part of Proposition 5.4 for a common primitive preference. -/
theorem proposition_5_4_unique {r : Z → Z → Prop} {u v : Z → ℝ}
    (hu : Represents u r) (hv : Represents v r) (hau : AffineInMix u) (hav : AffineInMix v) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, v x = A * u x + B :=
  affineInMix_unique hau hav (fun x y => (hu y x).symm.trans (hv y x))

/-- A positive affine transform preserves both the ranking and mixture affinity. -/
theorem positive_affine_representation {r : Z → Z → Prop} {u : Z → ℝ}
    (hu : Represents u r) (hau : AffineInMix u) (A B : ℝ) (hA : 0 < A) :
    Represents (fun x => A * u x + B) r ∧ AffineInMix (fun x => A * u x + B) := by
  constructor
  · intro x y
    rw [hu]
    simp only [add_le_add_iff_right, mul_le_mul_iff_right₀ hA]
  · intro a x y
    dsimp only
    rw [hau]
    ring

/-- The uniqueness part of Proposition 5.3 holds on the prize type itself. -/
theorem proposition_5_3_unique {r : SimpleLottery X → SimpleLottery X → Prop} {U V : X → ℝ}
    (hU : Represents (ExpectedUtility U) r) (hV : Represents (ExpectedUtility V) r) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, V x = A * U x + B := by
  obtain ⟨A, hA, B, h⟩ := proposition_5_4_unique hU hV (expectedUtility_affine U)
    (expectedUtility_affine V)
  exact ⟨A, hA, B, fun x => by simpa only [expectedUtility_pure] using h (PureLottery x)⟩

end Kreps.ChoiceUnderUncertainty
