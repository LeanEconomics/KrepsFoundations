/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommonScoreRestriction

/-!
# One common pair operation on all normalized active axes

Independence transports a one-axis indifference through a held-fixed second
coordinate. With three active axes, repeated transports identify every ordered
pair with a fixed anchor pair, including pairs that share an anchor coordinate.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {B : I → Type*} {D : Type*}

/-- Utility on two selected coordinates of one fixed surrounding bundle. -/
def CoordinatePairUtility (V : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (k : ∀ i, D → B i) (i j : I) (x y : D) : ℝ :=
  V (Function.update (Function.update z i (k i x)) j (k j y))

/-- All selected axes use the same normalized numerical scale. -/
def NormalizedCoordinateAxes (V : (∀ i, B i) → ℝ) (z : ∀ i, B i)
    (k : ∀ i, D → B i) (f : D → ℝ) (T : Set I) : Prop :=
  ∀ i ∈ T, ∀ x, V (Function.update z i (k i x)) = f x

/-- Changing a coordinate that is common to two bundles preserves utility equality. -/
theorem stronglySeparable_common_update_utility_eq [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) {i : I} {x y : ∀ i, B i}
    (hxy : x i = y i) (a : B i) :
    V x = V y ↔ V (Function.update x i a) = V (Function.update y i a) := by
  have h₁ := stronglySeparable_common_update_iff hs hxy a
  have h₂ := stronglySeparable_common_update_iff hs hxy.symm a
  change (V y ≤ V x ↔ _) at h₁
  change (V x ≤ V y ↔ _) at h₂
  constructor
  · intro h
    exact le_antisymm (h₂.mp h.le) (h₁.mp h.ge)
  · intro h
    exact le_antisymm (h₂.mpr h.le) (h₁.mpr h.ge)

/-- The first occupied score can move to any coordinate distinct from the held second one. -/
theorem coordinatePairUtility_move_first [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {i j p : I} (hji : j ≠ i) (hjp : j ≠ p)
    (hi : ∀ x, V (Function.update z i (k i x)) = f x)
    (hp : ∀ x, V (Function.update z p (k p x)) = f x) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k p j x y := by
  apply (stronglySeparable_common_update_utility_eq hs
    (show Function.update z i (k i x) j = Function.update z p (k p x) j by
      simp only [Function.update_of_ne hji, Function.update_of_ne hjp]) (k j y)).mp
  exact (hi x).trans (hp x).symm

/-- The second occupied score can move while the first coordinate is held fixed. -/
theorem coordinatePairUtility_move_second [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {i j q : I} (hij : i ≠ j) (hiq : i ≠ q)
    (hj : ∀ y, V (Function.update z j (k j y)) = f y)
    (hq : ∀ y, V (Function.update z q (k q y)) = f y) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k i q x y := by
  unfold CoordinatePairUtility
  rw [Function.update_comm hij, Function.update_comm hiq]
  exact coordinatePairUtility_move_first hs z k hij hiq hj hq y x

/-- Three distinct active indices provide a spare coordinate outside any occupied pair. -/
theorem three_members_spare {K : Type*} {T : Set K}
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c) (i j : K) :
    ∃ k ∈ T, k ≠ i ∧ k ≠ j := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := ht
  by_cases ha' : a ≠ i ∧ a ≠ j
  · exact ⟨a, ha, ha'⟩
  by_cases hb' : b ≠ i ∧ b ≠ j
  · exact ⟨b, hb, hb'⟩
  refine ⟨c, hc, ?_⟩
  aesop

/-- All ordered pairs of distinct normalized active coordinates have the same pair utility. -/
theorem coordinatePairUtility_same [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f : D → ℝ} {T : Set I} (hn : NormalizedCoordinateAxes V z k f T)
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {i j p q : I} (hi : i ∈ T) (hj : j ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hij : i ≠ j) (hpq : p ≠ q) (x y : D) :
    CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k p q x y := by
  by_cases hjp : j ≠ p
  · exact (coordinatePairUtility_move_first hs z k hij.symm hjp (hn i hi) (hn p hp) x y).trans
      (coordinatePairUtility_move_second hs z k hjp.symm hpq (hn j hj) (hn q hq) x y)
  · have hjp' : j = p := not_ne_iff.mp hjp
    obtain ⟨l, hl, hli, hlj⟩ := three_members_spare ht i j
    have hlp : l ≠ p := hjp' ▸ hlj
    calc
      CoordinatePairUtility V z k i j x y = CoordinatePairUtility V z k i l x y :=
        coordinatePairUtility_move_second hs z k hij hli.symm (hn j hj) (hn l hl) x y
      _ = CoordinatePairUtility V z k p l x y :=
        coordinatePairUtility_move_first hs z k hli hlp (hn i hi) (hn p hp) x y
      _ = CoordinatePairUtility V z k p q x y :=
        coordinatePairUtility_move_second hs z k hlp.symm hpq (hn l hl) (hn q hq) x y

/-- Replacing the selected pair of a two-coordinate bundle changes only its surrounding context. -/
theorem piecewise_pair_updates (z t : ∀ i, B i) {i j : I} (hij : i ≠ j)
    (a : B i) (b : B j) :
    ({i, j} : Finset I).piecewise (Function.update (Function.update z i a) j b) t =
      Function.update (Function.update t i a) j b := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [hij, Finset.piecewise]
  by_cases hlj : l = j
  · subst l
    simp [Finset.piecewise]
  · simp [hli, hlj, Finset.piecewise]

/-- Pair comparisons on the reference slice hold in every surrounding context. -/
theorem coordinatePairUtility_context_iff {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z t : ∀ i, B i) (k : ∀ i, D → B i)
    {i j : I} (hij : i ≠ j) (x y x' y' : D) :
    CoordinatePairUtility V z k i j x y ≤ CoordinatePairUtility V z k i j x' y' ↔
      CoordinatePairUtility V t k i j x y ≤ CoordinatePairUtility V t k i j x' y' := by
  have h := hs {i, j}
    (Function.update (Function.update z i (k i x')) j (k j y'))
    (Function.update (Function.update z i (k i x)) j (k j y)) z t
  simpa only [piecewise_pair_updates _ _ hij, UtilityPref, CoordinatePairUtility] using h

/-- One anchor-pair additive scale represents every active pair in every surrounding context. -/
theorem coordinatePairUtility_all_comparisons [Finite I] {V : (∀ i, B i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (z : ∀ i, B i) (k : ∀ i, D → B i)
    {f φ : D → ℝ} {T : Set I} (hn : NormalizedCoordinateAxes V z k f T)
    (ht : ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {p q : I} (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (hφ : ∀ x y x' y', CoordinatePairUtility V z k p q x y ≤
      CoordinatePairUtility V z k p q x' y' ↔ φ x + φ y ≤ φ x' + φ y')
    (t : ∀ i, B i) {i j : I} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (x y x' y' : D) :
    CoordinatePairUtility V t k i j x y ≤ CoordinatePairUtility V t k i j x' y' ↔
      φ x + φ y ≤ φ x' + φ y' := by
  rw [← coordinatePairUtility_context_iff hs z t k hij,
    coordinatePairUtility_same hs z k hn ht hi hj hp hq hij hpq x y,
    coordinatePairUtility_same hs z k hn ht hi hj hp hq hij hpq x' y']
  exact hφ x y x' y'

end Kreps.PreferenceProperties
