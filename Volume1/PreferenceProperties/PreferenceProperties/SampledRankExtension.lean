/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RecursiveRankDensity

/-!
# Completing an assigned scale from a dense sample

Kreps I, Problem 2.14(f)-(g). Taking the supremum of the assigned ranks weakly
below a point extends the specified scale. Including best and worst ranks in the
sample ensures finite bounds at every point. Strict separation gives representation;
density of the assigned values removes numerical gaps and gives continuity.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- Every point lies between two sampled original ranks, with equality permitted. -/
def SampleBrackets (v : X → ℝ) (q : ℕ → X) : Prop :=
  ∀ x, ∃ i j, v (q i) ≤ v x ∧ v x ≤ v (q j)

/-- The sample contains a representative of each attained extreme rank. -/
def SampleContainsExtremes (v : X → ℝ) (q : ℕ → X) : Prop :=
  (∀ x, (∀ y, v x ≤ v y) → ∃ n, v (q n) = v x) ∧
    (∀ x, (∀ y, v y ≤ v x) → ∃ n, v (q n) = v x)

/-- Strict separation and the included extreme ranks supply finite brackets everywhere. -/
theorem sampleBrackets_of_extremes {v : X → ℝ} {q : ℕ → X}
    (hs : StrictRankSeparator v (Set.range q)) (he : SampleContainsExtremes v q) :
    SampleBrackets v q := by
  intro x
  have hlo : ∃ i, v (q i) ≤ v x := by
    by_cases h : ∃ y, v y < v x
    · obtain ⟨y, hy⟩ := h
      obtain ⟨z, ⟨i, rfl⟩, _, hix⟩ := hs y x hy
      exact ⟨i, hix.le⟩
    · have hmin : ∀ y, v x ≤ v y := fun y => le_of_not_gt (fun hy => h ⟨y, hy⟩)
      obtain ⟨i, hi⟩ := he.1 x hmin
      exact ⟨i, hi.le⟩
  have hhi : ∃ j, v x ≤ v (q j) := by
    by_cases h : ∃ y, v x < v y
    · obtain ⟨y, hy⟩ := h
      obtain ⟨z, ⟨j, rfl⟩, hxj, _⟩ := hs x y hy
      exact ⟨j, hxj.le⟩
    · have hmax : ∀ y, v y ≤ v x := fun y => le_of_not_gt (fun hy => h ⟨y, hy⟩)
      obtain ⟨j, hj⟩ := he.2 x hmax
      exact ⟨j, hj.ge⟩
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  exact ⟨i, j, hi, hj⟩

/-- Assigned values of sampled points no better than the given point. -/
def SampleRankCut (v : X → ℝ) (q : ℕ → X) (u : ℕ → ℝ) (x : X) : Set ℝ :=
  u '' {n | v (q n) ≤ v x}

/-- Complete the assigned scale by taking the supremum of each lower cut. -/
noncomputable def SampleRankExtension (v : X → ℝ) (q : ℕ → X) (u : ℕ → ℝ) (x : X) : ℝ :=
  sSup (SampleRankCut v q u x)

/-- A sampled lower bracket makes every cut nonempty. -/
theorem sampleRankCut_nonempty {v : X → ℝ} {q : ℕ → X} (u : ℕ → ℝ)
    (hb : SampleBrackets v q) (x : X) : (SampleRankCut v q u x).Nonempty := by
  obtain ⟨i, _, hi, _⟩ := hb x
  exact ⟨u i, i, hi, rfl⟩

/-- A sampled upper bracket bounds every assigned lower cut. -/
theorem sampleRankCut_bddAbove {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q) (x : X) :
    BddAbove (SampleRankCut v q u x) := by
  obtain ⟨_, j, _, hj⟩ := hb x
  refine ⟨u j, ?_⟩
  rintro a ⟨i, hi, rfl⟩
  exact (hu i j).mp (hi.trans hj)

/-- A sampled rank below the point bounds its extension from below. -/
theorem sampleRankExtension_lower {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x : X} {i : ℕ} (hi : v (q i) ≤ v x) : u i ≤ SampleRankExtension v q u x :=
  le_csSup (sampleRankCut_bddAbove hu hb x) ⟨i, hi, rfl⟩

/-- A sampled rank above the point bounds its extension from above. -/
theorem sampleRankExtension_upper {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x : X} {j : ℕ} (hj : v x ≤ v (q j)) : SampleRankExtension v q u x ≤ u j := by
  apply csSup_le (sampleRankCut_nonempty u hb x)
  rintro a ⟨i, hi, rfl⟩
  exact (hu i j).mp (hi.trans hj)

/-- The extension agrees with all of the prescribed sampled values. -/
theorem sampleRankExtension_at_sample {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q) (i : ℕ) :
    SampleRankExtension v q u (q i) = u i :=
  le_antisymm (sampleRankExtension_upper hu hb le_rfl)
    (sampleRankExtension_lower hu hb le_rfl)

/-- Inclusion of lower cuts preserves weak original rank comparisons. -/
theorem sampleRankExtension_mono {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    {x y : X} (hxy : v x ≤ v y) :
    SampleRankExtension v q u x ≤ SampleRankExtension v q u y := by
  apply csSup_le (sampleRankCut_nonempty u hb x)
  rintro a ⟨i, hi, rfl⟩
  exact sampleRankExtension_lower hu hb (hi.trans hxy)

/-- Two intermediate sampled ranks force a strict comparison of the completed values. -/
theorem sampleRankExtension_strict {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    (hu : RankPreserving (v ∘ q) u) (hb : SampleBrackets v q)
    (hs : StrictRankSeparator v (Set.range q)) {x y : X} (hxy : v x < v y) :
    SampleRankExtension v q u x < SampleRankExtension v q u y := by
  obtain ⟨a, ⟨i, rfl⟩, hxi, hiy⟩ := hs x y hxy
  obtain ⟨b, ⟨j, rfl⟩, hij, hjy⟩ := hs (q i) y hiy
  exact (sampleRankExtension_upper hu hb hxi.le).trans_lt
    (((rankPreserving_lt hu i j).mp hij).trans_le (sampleRankExtension_lower hu hb hjy.le))

/-- The extension represents the original preference on the entire domain. -/
theorem sampleRankExtension_represents {v : X → ℝ} {q : ℕ → X} {u : ℕ → ℝ}
    {r : X → X → Prop} (hv : Represents v r) (hu : RankPreserving (v ∘ q) u)
    (hb : SampleBrackets v q) (hs : StrictRankSeparator v (Set.range q)) :
    Represents (SampleRankExtension v q u) r := by
  intro x y
  constructor
  · exact fun hxy => sampleRankExtension_mono hu hb ((hv x y).mp hxy)
  · intro hxy
    by_contra h
    have hlt : v x < v y := lt_of_not_ge (fun hle => h ((hv x y).mpr hle))
    exact not_lt_of_ge hxy (sampleRankExtension_strict hu hb hs hlt)

/-- A represented continuous preference has continuous utility if its range has no open gaps. -/
theorem continuous_of_interval_closure_range [TopologicalSpace X]
    {r : X → X → Prop} {u : X → ℝ} (hu : Represents u r) (hc : ContinuousPreference r)
    (hgap : ∀ x y, Set.Icc (u x) (u y) ⊆ closure (Set.range u)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change a < u x at hx
    by_cases hall : ∀ y, a < u y
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · push Not at hall
      obtain ⟨y, hy⟩ := hall
      have hm : (a + u x) / 2 ∈ closure (Set.range u) :=
        hgap y x ⟨by linarith, by linarith⟩
      obtain ⟨_, ⟨haz, hzx⟩, z, rfl⟩ := mem_closure_iff.mp hm (Set.Ioo a (u x))
        isOpen_Ioo ⟨by linarith, by linarith⟩
      have hxz := (strict_iff_utility_lt hu x z).mpr hzx
      apply Filter.mem_of_superset ((ho z).1.mem_nhds hxz)
      intro w hw
      exact haz.trans ((strict_iff_utility_lt hu w z).mp hw)
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change u x < a at hx
    by_cases hall : ∀ y, u y < a
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => hall y)
    · push Not at hall
      obtain ⟨y, hy⟩ := hall
      have hm : (u x + a) / 2 ∈ closure (Set.range u) :=
        hgap x y ⟨by linarith, by linarith⟩
      obtain ⟨_, ⟨hxz, hza⟩, z, rfl⟩ := mem_closure_iff.mp hm (Set.Ioo (u x) a)
        isOpen_Ioo ⟨by linarith, by linarith⟩
      have hzx := (strict_iff_utility_lt hu z x).mpr hxz
      apply Filter.mem_of_superset ((ho z).2.mem_nhds hzx)
      intro w hw
      exact ((strict_iff_utility_lt hu z w).mp hw).trans hza

end Kreps.PreferenceProperties
