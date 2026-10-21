/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ScalarChartCompatibility
import PreferenceProperties.CompanionChartCalibration

/-!
# Actual coordinate chart families from strong separability

Fix a reference bundle and one seed additive chart. For each target coordinate,
choose local additive charts along its entire reference slice, preserving that
seed at the reference value. Two other essential coordinates remain fixed and
therefore supply the companion domains needed for cardinal calibration.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] [Fintype I] {S : I → Set ℝ}
  {V : (∀ i, S i) → ℝ}

variable (V) (z : ∀ i, S i) (seed : ScalarAdditiveChart V)

/-- Local additive charts along one coordinate slice, with a prescribed common seed chart. -/
structure CoordinateChartFamily (i : I) where
  chart : S i → ScalarAdditiveChart V
  center : ∀ x p, (Function.update z i x p).val ∈ (chart x).domain p
  seed_eq : chart (z i) = seed

variable {V}

/-- Pointwise local additive existence supplies charts along every reference slice. -/
theorem exists_coordinateChartFamily
    (hl : ∀ z : ∀ i, S i, ∃ C : ScalarAdditiveChart V, ∀ i, (z i).val ∈ C.domain i)
    (z : ∀ i, S i) (seed : ScalarAdditiveChart V) (hz : ∀ i, (z i).val ∈ seed.domain i)
    (i : I) : Nonempty (CoordinateChartFamily V z seed i) := by
  classical
  choose C hC using hl
  let f (x : S i) := if x = z i then seed else C (Function.update z i x)
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro x p
    by_cases hx : x = z i
    · subst x
      simpa [f] using hz p
    · simpa only [f, ite_eq_right hx] using hC (Function.update z i x) p
  · simp [f]

/-- The target and its ordered pair of companion indices. -/
def companionCoordinateIndex (i j k : I) : Fin 3 → I := ![i, j, k]

omit [DecidableEq I] [Fintype I] in
/-- Distinct selected coordinates give an injective three-coordinate index map. -/
theorem companionCoordinateIndex_injective {i j k : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (companionCoordinateIndex i j k) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [companionCoordinateIndex]

/-- Two fixed companion coordinates turn the actual local charts into a calibration family. -/
def CoordinateChartFamily.toCompanionFamily {z : ∀ i, S i} {seed : ScalarAdditiveChart V}
    {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CompanionChartFamily (S i) where
  domain x p := (F.chart x).domain (companionCoordinateIndex i j k p)
  coord x p := (F.chart x).coord (companionCoordinateIndex i j k p)
  open_domain x p := (F.chart x).open_domain _
  interval x p := (F.chart x).interval _
  continuous x p := (F.chart x).continuous _
  increasing x p := (F.chart x).increasing _
  firstReference := (z j).val
  secondReference := (z k).val
  first_mem x := by
    simpa [companionCoordinateIndex, hij.symm] using F.center x j
  second_mem x := by
    simpa [companionCoordinateIndex, hik.symm] using F.center x k
  pair_compatible x y p q hpq := (F.chart x).pair_compatible (F.chart y) hs
    (fun n => ⟨(Function.update z i x n).val, F.center x n⟩)
    (fun n => ⟨(Function.update z i y n).val, F.center y n⟩)
    ((companionCoordinateIndex_injective hij hik hjk).ne hpq)

/-- The target domains of the companion family stay inside the original coordinate interval. -/
theorem CoordinateChartFamily.companion_target_subset {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ x, (F.toCompanionFamily hs hij hik hjk).domain x 0 ⊆ S i := by
  intro x
  exact (F.chart x).subset i

/-- These actual charts cover the entire target coordinate interval. -/
theorem CoordinateChartFamily.companion_target_cover {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ x ∈ S i, ∃ p, x ∈ (F.toCompanionFamily hs hij hik hjk).domain p 0 := by
  intro x hx
  refine ⟨⟨x, hx⟩, ?_⟩
  simpa [toCompanionFamily, companionCoordinateIndex] using F.center ⟨x, hx⟩ i

/-- The companion-family seed is the originally prescribed target chart. -/
theorem CoordinateChartFamily.companion_seed {z : ∀ i, S i}
    {seed : ScalarAdditiveChart V} {i j k : I} (F : CoordinateChartFamily V z seed i)
    (hs : StronglySeparable (UtilityPref V)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : Fin 3) :
    (F.toCompanionFamily hs hij hik hjk).domain (z i) p =
        seed.domain (companionCoordinateIndex i j k p) ∧
      (F.toCompanionFamily hs hij hik hjk).coord (z i) p =
        seed.coord (companionCoordinateIndex i j k p) := by
  simp [toCompanionFamily, F.seed_eq]

end Kreps.PreferenceProperties
