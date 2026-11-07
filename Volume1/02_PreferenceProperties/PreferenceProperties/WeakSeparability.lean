/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.FiniteCoordinateComparison

/-!
# Weak separability and an increasing aggregator

Kreps I, Definition 2.11 and Proposition 2.12, pp. 40-41. A bundle consists of
finitely many independent commodity blocks and an arbitrary leftover bundle.
The aggregator is defined only on attained subutility ranges and is strictly
increasing when some block score increases and none decreases.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} {B : I → Type*} {L : Type*}

/-- The selected disjoint blocks, together with all leftover goods. -/
abbrev BlockBundle (B : I → Type*) (L : Type*) := (∀ i, B i) × L

/-- Substitute one block while keeping every other good fixed. -/
def ReplaceBlock [DecidableEq I] (s : BlockBundle B L) (i : I) (a : B i) : BlockBundle B L :=
  (Function.update s.1 i a, s.2)

/-- **Definition 2.11:** comparisons within each block ignore the surrounding bundle. -/
def WeaklySeparable [DecidableEq I] (r : BlockBundle B L → BlockBundle B L → Prop) : Prop :=
  ∀ i a b s t, r (ReplaceBlock s i a) (ReplaceBlock s i b) ↔
    r (ReplaceBlock t i a) (ReplaceBlock t i b)

/-- Independence of the surrounding goods also preserves strict comparisons. -/
theorem weaklySeparable_strict [DecidableEq I]
    {r : BlockBundle B L → BlockBundle B L → Prop} (hs : WeaklySeparable r)
    (i : I) (a b : B i) (s t : BlockBundle B L) :
    Strict r (ReplaceBlock s i a) (ReplaceBlock s i b) ↔
      Strict r (ReplaceBlock t i a) (ReplaceBlock t i b) :=
  and_congr (hs i a b s t) (not_congr (hs i b a s t))

/-- The book's subutility, evaluated against a fixed reference bundle. -/
def BaselineSubutility [DecidableEq I] (u : BlockBundle B L → ℝ) (s₀ : BlockBundle B L)
    (i : I) (a : B i) : ℝ := u (ReplaceBlock s₀ i a)

/-- Weak separability transports each baseline comparison to every surrounding bundle. -/
theorem baseline_comparison_iff [DecidableEq I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ : BlockBundle B L) (i : I) (s : BlockBundle B L)
    (a b : B i) :
    u (ReplaceBlock s i a) ≤ u (ReplaceBlock s i b) ↔
      BaselineSubutility u s₀ i a ≤ BaselineSubutility u s₀ i b := by
  calc
    u (ReplaceBlock s i a) ≤ u (ReplaceBlock s i b) ↔
        r (ReplaceBlock s i b) (ReplaceBlock s i a) := (hu _ _).symm
    _ ↔ r (ReplaceBlock s₀ i b) (ReplaceBlock s₀ i a) := hs i b a s s₀
    _ ↔ BaselineSubutility u s₀ i a ≤ BaselineSubutility u s₀ i b := hu _ _

/-- Each coordinate carries its score and evidence that the score is attained. -/
def BlockScores (w : ∀ i, B i → ℝ) (x : ∀ i, B i) : ∀ i, Set.range (w i) :=
  fun i => ⟨w i (x i), x i, rfl⟩

/-- Block substitution changes exactly the corresponding score coordinate. -/
theorem blockScores_update [DecidableEq I] (w : ∀ i, B i → ℝ)
    (x : ∀ i, B i) (i : I) (a : B i) :
    BlockScores w (Function.update x i a) =
      Function.update (BlockScores w x) i ⟨w i a, a, rfl⟩ := by
  funext j
  apply Subtype.ext
  by_cases hj : j = i
  · subst j
    simp [BlockScores]
  · simp [BlockScores, Function.update_of_ne hj]

/-- Select an actual block attaining a given subutility value. -/
noncomputable def ScoreRepresentative (w : ∀ i, B i → ℝ) (i : I)
    (q : Set.range (w i)) : B i := Classical.choose q.property

/-- The selected block has exactly the specified score. -/
theorem scoreRepresentative_spec (w : ∀ i, B i → ℝ) (i : I) (q : Set.range (w i)) :
    w i (ScoreRepresentative w i q) = q.val := Classical.choose_spec q.property

/-- Reconstruct utility from representatives of the attained block scores. -/
noncomputable def SubutilityAggregator (u : BlockBundle B L → ℝ) (w : ∀ i, B i → ℝ)
    (p : (∀ i, Set.range (w i)) × L) : ℝ :=
  u ((fun i => ScoreRepresentative w i (p.1 i)), p.2)

/-- Strict increase in the first coordinates, with the leftover goods held fixed. -/
def IncreasingAggregator (w : ∀ i, B i → ℝ)
    (V : ((∀ i, Set.range (w i)) × L) → ℝ) : Prop :=
  ∀ l, StrictMono (fun q => V (q, l))

/-- The exact factorization of the given utility required by **Proposition 2.12**. -/
def WeakSeparabilityRepresentation (u : BlockBundle B L → ℝ) : Prop :=
  ∃ w : ∀ i, B i → ℝ, ∃ V : ((∀ i, Set.range (w i)) × L) → ℝ,
    IncreasingAggregator w V ∧ ∀ x, u x = V (BlockScores w x.1, x.2)

/-- A strictly increasing aggregator orders changes in one block by its subutility. -/
theorem aggregator_coordinate_comparison [DecidableEq I] {w : ∀ i, B i → ℝ}
    {V : ((∀ i, Set.range (w i)) × L) → ℝ} (hV : IncreasingAggregator w V)
    (x : ∀ i, B i) (l : L) (i : I) (a b : B i) :
    V (BlockScores w (Function.update x i a), l) ≤
      V (BlockScores w (Function.update x i b), l) ↔ w i a ≤ w i b := by
  rw [blockScores_update, blockScores_update]
  exact ((hV l).comp Function.update_strictMono).le_iff_le

/-- The aggregator form implies independence of the surrounding goods. -/
theorem weaklySeparable_of_representation [DecidableEq I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hf : WeakSeparabilityRepresentation u) : WeaklySeparable r := by
  obtain ⟨w, V, hV, he⟩ := hf
  intro i a b s t
  have hcompare (z : BlockBundle B L) :
      r (ReplaceBlock z i a) (ReplaceBlock z i b) ↔ w i b ≤ w i a := by
    rw [hu, he (ReplaceBlock z i b), he (ReplaceBlock z i a)]
    exact aggregator_coordinate_comparison hV z.1 z.2 i b a
  exact (hcompare s).trans (hcompare t).symm

/-- Equal subutility coordinates give equal overall utility by the finite substitution chain. -/
theorem subutilityAggregator_factors [DecidableEq I] [Finite I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ x : BlockBundle B L) :
    u x = SubutilityAggregator u (BaselineSubutility u s₀)
      (BlockScores (BaselineSubutility u s₀) x.1, x.2) := by
  let w := BaselineSubutility u s₀
  change u (x.1, x.2) = u ((fun i => ScoreRepresentative w i (BlockScores w x.1 i)), x.2)
  apply finite_coordinate_eq (F := fun z => u (z, x.2)) (w := w)
    (fun i z a b h => (baseline_comparison_iff hu hs s₀ i (z, x.2) a b).mpr h)
  intro i
  exact (scoreRepresentative_spec w i (BlockScores w x.1 i)).symm

/-- A strict increase of any score makes the finite substitution chain strict. -/
theorem subutilityAggregator_increasing [DecidableEq I] [Finite I] {u : BlockBundle B L → ℝ}
    {r : BlockBundle B L → BlockBundle B L → Prop} (hu : Represents u r)
    (hs : WeaklySeparable r) (s₀ : BlockBundle B L) :
    IncreasingAggregator (BaselineSubutility u s₀)
      (SubutilityAggregator u (BaselineSubutility u s₀)) := by
  let w := BaselineSubutility u s₀
  intro l q t hqt
  have hle := le_of_lt hqt
  have hn := not_le_of_gt hqt
  change ¬∀ i, t i ≤ q i at hn
  obtain ⟨i, hi⟩ := not_forall.mp hn
  change u ((fun j => ScoreRepresentative w j (q j)), l) <
    u ((fun j => ScoreRepresentative w j (t j)), l)
  apply finite_coordinate_strict (F := fun z => u (z, l)) (w := w)
    (fun j z a b => baseline_comparison_iff hu hs s₀ j (z, l) a b)
  · intro j
    rw [scoreRepresentative_spec w j (q j), scoreRepresentative_spec w j (t j)]
    exact hle j
  · refine ⟨i, ?_⟩
    rw [scoreRepresentative_spec w i (q i), scoreRepresentative_spec w i (t i)]
    exact lt_of_not_ge hi

/-- The baseline construction supplies both the exact factorization and strict increase. -/
theorem weakSeparabilityRepresentation_of_separable [DecidableEq I] [Finite I]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) (hs : WeaklySeparable r) (s₀ : BlockBundle B L) :
    WeakSeparabilityRepresentation u :=
  ⟨BaselineSubutility u s₀, SubutilityAggregator u (BaselineSubutility u s₀),
    subutilityAggregator_increasing hu hs s₀, subutilityAggregator_factors hu hs s₀⟩

/-- **Proposition 2.12:** weak separability is equivalent to the given utility's factorization. -/
theorem proposition_2_12 [DecidableEq I] [Finite I] [Nonempty (BlockBundle B L)]
    {u : BlockBundle B L → ℝ} {r : BlockBundle B L → BlockBundle B L → Prop}
    (hu : Represents u r) : WeaklySeparable r ↔ WeakSeparabilityRepresentation u := by
  constructor
  · intro hs
    obtain ⟨s₀⟩ := ‹Nonempty (BlockBundle B L)›
    exact weakSeparabilityRepresentation_of_separable hu hs s₀
  · exact weaklySeparable_of_representation hu

end Kreps.PreferenceProperties
