/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ConvexPreference
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# A continuous connect-the-dots curve

Kreps I, Problem 2.14(a), p. 48. Interpolate linearly between consecutive integer
points in a convex domain. The affine formulas agree at every integer junction;
local finiteness of the closed unit intervals gives continuity on the whole line.
A sequence indexed by natural numbers is extended constantly to negative indices.
-/

namespace Kreps.PreferenceProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- Linear interpolation between each consecutive pair of integer-indexed points. -/
noncomputable def PolygonalCurve (hS : Convex ℝ S) (q : ℤ → S) (t : ℝ) : S :=
  Mix hS (q (⌊t⌋ + 1)) (q ⌊t⌋) (Int.fract t)
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- At an integer, interpolation returns the prescribed point. -/
theorem polygonalCurve_int (hS : Convex ℝ S) (q : ℤ → S) (n : ℤ) :
    PolygonalCurve hS q n = q n := by
  apply Subtype.ext
  simp [PolygonalCurve, Mix]

/-- Each closed unit interval carries one affine segment, including both endpoints. -/
theorem polygonalCurve_formula (hS : Convex ℝ S) (q : ℤ → S) (n : ℤ)
    {t : ℝ} (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    (PolygonalCurve hS q t).val =
      (t - n) • (q (n + 1)).val + (1 - (t - n)) • (q n).val := by
  by_cases hn : t < (n : ℝ) + 1
  · have hf : ⌊t⌋ = n := Int.floor_eq_iff.mpr ⟨ht.1, hn⟩
    simp only [PolygonalCurve, Mix, Int.fract, hf]
  · have he : t = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith [ht.2]
    rw [he, polygonalCurve_int]
    simp

/-- The integer unit intervals form a locally finite closed cover of the real line. -/
theorem integer_unit_intervals_locallyFinite :
    LocallyFinite (fun n : ℤ => Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
  locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
    (Filter.tendsto_atBot_add_const_right _ 1
      (tendsto_intCast_atBot_iff.mpr Filter.tendsto_id))

/-- Affine continuity on the closed unit intervals glues to a continuous curve. -/
theorem polygonalCurve_continuous (hS : Convex ℝ S) (q : ℤ → S) :
    Continuous (PolygonalCurve hS q) := by
  have hcover : (⋃ n : ℤ, Set.Icc (n : ℝ) ((n : ℝ) + 1)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact Set.mem_iUnion.mpr ⟨⌊t⌋, Int.floor_le t, (Int.lt_floor_add_one t).le⟩
  have hval : Continuous (fun t => (PolygonalCurve hS q t).val) := by
    apply integer_unit_intervals_locallyFinite.continuous hcover (fun _ => isClosed_Icc)
    intro n
    have hp : Continuous (fun t : ℝ =>
        (t - n) • (q (n + 1)).val + (1 - (t - n)) • (q n).val) := by fun_prop
    apply hp.continuousOn.congr
    intro t ht
    exact polygonalCurve_formula hS q n ht
  exact hval.subtype_mk _

/-- The image of a polygonal curve is connected in the sense needed for the crossing lemma. -/
theorem polygonalCurve_range_preconnected (hS : Convex ℝ S) (q : ℤ → S) :
    IsPreconnected (Set.range (PolygonalCurve hS q)) :=
  isPreconnected_range (polygonalCurve_continuous hS q)

/-- A natural-number sequence gives a curve constant before zero and joining all its points. -/
noncomputable def SequenceCurve (hS : Convex ℝ S) (q : ℕ → S) : ℝ → S :=
  PolygonalCurve hS (fun n => q n.toNat)

/-- Every prescribed sequence point lies on the curve at its natural-number parameter. -/
theorem sequenceCurve_nat (hS : Convex ℝ S) (q : ℕ → S) (n : ℕ) :
    SequenceCurve hS q n = q n := by
  simpa only [SequenceCurve, Int.cast_natCast, Int.toNat_natCast] using
    polygonalCurve_int hS (fun m => q m.toNat) n

/-- The countable connect-the-dots construction is continuous. -/
theorem sequenceCurve_continuous (hS : Convex ℝ S) (q : ℕ → S) :
    Continuous (SequenceCurve hS q) := polygonalCurve_continuous hS _

/-- Every point in the prescribed sequence belongs to the curve image. -/
theorem sequenceCurve_contains_range (hS : Convex ℝ S) (q : ℕ → S) :
    Set.range q ⊆ Set.range (SequenceCurve hS q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, sequenceCurve_nat hS q n⟩

end Kreps.PreferenceProperties
