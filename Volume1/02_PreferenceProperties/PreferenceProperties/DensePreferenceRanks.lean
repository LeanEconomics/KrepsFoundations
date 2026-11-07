/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.ContinuousUtility
import Mathlib.Order.CountableDenseLinearOrder

/-!
# Countable dense ranks for the general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. The general proof here uses Cantor's
isomorphism theorem on the interior ranks of a countable dense subset. It handles
attained and unattained extrema without assuming monotonicity. Problem 2.14's
particular recursive assignment is a separate source-map obligation.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*}

/-- Every strict numerical gap contains a rank from the chosen subset. -/
def StrictRankSeparator (v : X → ℝ) (D : Set X) : Prop :=
  ∀ x y, v x < v y → ∃ d ∈ D, v x < v d ∧ v d < v y

/-- A dense subset strictly separates represented continuous preferences on a connected space. -/
theorem dense_strictRankSeparator [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) {D : Set X} (hD : Dense D) : StrictRankSeparator v D := by
  intro x y hxy
  obtain ⟨z, hyz, hzx⟩ := exists_strict_between hr hc
    ((strict_iff_utility_lt hv y x).mpr hxy)
  have ho := continuousPreference_openStrictContours hc
  obtain ⟨d, hd, hdx, hyd⟩ := hD.exists_mem_open ((ho x).1.inter (ho y).2) ⟨z, hzx, hyz⟩
  exact ⟨d, hd, (strict_iff_utility_lt hv d x).mp hdx,
    (strict_iff_utility_lt hv y d).mp hyd⟩

/-- Remove any globally best and worst ranks from the chosen countable set. -/
def InteriorRankSet (v : X → ℝ) (D : Set X) : Set ℝ :=
  {a | a ∈ v '' D ∧ (∃ x, v x < a) ∧ ∃ y, a < v y}

/-- Every interior rank is the utility of an actual bundle. -/
theorem interiorRank_witness {v : X → ℝ} {D : Set X} (a : InteriorRankSet v D) :
    ∃ x, v x = a.val := by
  obtain ⟨x, _, hx⟩ := a.property.1
  exact ⟨x, hx⟩

/-- Every strict comparison brackets an interior rank, including near global endpoints. -/
theorem interiorRank_between {v : X → ℝ} {D : Set X} (hs : StrictRankSeparator v D)
    {x y : X} (hxy : v x < v y) :
    ∃ a : InteriorRankSet v D, v x < a.val ∧ a.val < v y := by
  obtain ⟨d, hd, hxd, hdy⟩ := hs x y hxy
  exact ⟨⟨v d, ⟨d, hd, rfl⟩, ⟨x, hxd⟩, ⟨y, hdy⟩⟩, hxd, hdy⟩

/-- The rank set remains countable after excluding endpoints. -/
theorem interiorRankSet_countable {v : X → ℝ} {D : Set X} (hD : D.Countable) :
    (InteriorRankSet v D).Countable :=
  (hD.image v).mono (fun _ h => h.1)

/-- The bounded rational scale used to fill every numerical gap. -/
abbrev RationalUnit : Type := Set.Ioo (0 : ℚ) 1

/-- A nonconstant preference's interior countable ranks have exactly the order type of (0,1) ∩ ℚ. -/
theorem interiorRanks_orderIso {v : X → ℝ} {D : Set X} (hD : D.Countable)
    (hs : StrictRankSeparator v D) (hn : ∃ x y, v x < v y) :
    Nonempty (InteriorRankSet v D ≃o RationalUnit) := by
  let A : Type := InteriorRankSet v D
  let : Countable A := (interiorRankSet_countable hD).to_subtype
  let : Nonempty A := by
    obtain ⟨x, y, hxy⟩ := hn
    obtain ⟨a, _⟩ := interiorRank_between hs hxy
    exact ⟨a⟩
  let : DenselyOrdered A := ⟨by
    intro a b hab
    obtain ⟨x, hx⟩ := interiorRank_witness a
    obtain ⟨y, hy⟩ := interiorRank_witness b
    have hxy : v x < v y := by rw [hx, hy]; exact hab
    obtain ⟨c, hxc, hcy⟩ := interiorRank_between hs hxy
    rw [hx] at hxc
    rw [hy] at hcy
    exact ⟨c, hxc, hcy⟩⟩
  let : NoMinOrder A := ⟨by
    intro a
    obtain ⟨x, hxa⟩ := a.property.2.1
    obtain ⟨y, hy⟩ := interiorRank_witness a
    obtain ⟨b, _, hby⟩ := interiorRank_between hs (hy.symm ▸ hxa)
    rw [hy] at hby
    exact ⟨b, hby⟩⟩
  let : NoMaxOrder A := ⟨by
    intro a
    obtain ⟨y, hay⟩ := a.property.2.2
    obtain ⟨x, hx⟩ := interiorRank_witness a
    obtain ⟨b, hxb, _⟩ := interiorRank_between hs (hx.symm ▸ hay)
    rw [hx] at hxb
    exact ⟨b, hxb⟩⟩
  let : Nonempty RationalUnit := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
  exact Order.iso_of_countable_dense A RationalUnit

end Kreps.PreferenceProperties
