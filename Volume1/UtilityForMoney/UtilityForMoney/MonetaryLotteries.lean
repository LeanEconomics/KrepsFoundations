/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# Lotteries over monetary prizes

Kreps I, §§6.1–6.2, pp. 123–127. Each lottery has its own finite support in an
arbitrary prize type. Monetary prizes lie in an interval of the real line.
The standard simplex and the utility orientation agree with Chapter 5.
-/

namespace Kreps.UtilityForMoney

open Convexity

/-- A simple lottery has nonnegative, finitely supported probabilities summing to one. -/
abbrev SimpleLottery (X : Type*) := StdSimplex ℝ X

/-- Expected utility is the weighted sum over the lottery's support. -/
noncomputable def ExpectedUtility {X : Type*} (U : X → ℝ) (p : SimpleLottery X) : ℝ :=
  p.weights.sum fun x a => a * U x

/-- A binary lottery puts mass `a` on its first prize and `1-a` on its second. -/
noncomputable def BinaryLottery {X : Type*} (x y : X) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    SimpleLottery X :=
  convexCombPair a (1 - a) ha.1 (sub_nonneg.mpr ha.2) (by ring)
    (StdSimplex.single x) (StdSimplex.single y)

/-- Expected utility is Mathlib's affine extension of the evaluation on sure prizes. -/
theorem expectedUtility_eq_affine {X : Type*} (U : X → ℝ) (p : SimpleLottery X) :
    ExpectedUtility U p = StdSimplex.affineMapMk U p := by
  rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum]
  rfl

/-- The expected utility of a sure prize is its utility. -/
theorem expectedUtility_single {X : Type*} (U : X → ℝ) (x : X) :
    ExpectedUtility U (StdSimplex.single x) = U x := by
  rw [expectedUtility_eq_affine, StdSimplex.affineMapMk_single]

/-- Evaluation of a binary lottery, including equal prizes and zero weights. -/
theorem expectedUtility_binary {X : Type*} (U : X → ℝ) (x y : X) (a : ℝ)
    (ha : a ∈ Set.Icc 0 1) :
    ExpectedUtility U (BinaryLottery x y a ha) = a * U x + (1 - a) * U y := by
  rw [expectedUtility_eq_affine, BinaryLottery,
    (StdSimplex.affineMapMk U).isAffineMap.map_convexCombPair,
    convexCombPair_eq_sum, StdSimplex.affineMapMk_single, StdSimplex.affineMapMk_single]
  rfl

/-- **Proposition 6.1:** a strict ranking of sure prizes is exactly strict increase. -/
theorem proposition_6_1 {X : Type*} [Preorder X] (U : X → ℝ) :
    StrictMono U ↔ ∀ x y : X, x < y →
      ExpectedUtility U (StdSimplex.single x) < ExpectedUtility U (StdSimplex.single y) := by
  simp only [expectedUtility_single]
  exact ⟨fun h x y hxy => h hxy, fun h _ _ hxy => h _ _ hxy⟩

/-- Every utility level between two prize evaluations is attained by a simple lottery. -/
theorem exists_lottery_of_between {X : Type*} (U : X → ℝ) (x y : X) {t : ℝ}
    (hx : U x ≤ t) (hy : t ≤ U y) : ∃ p : SimpleLottery X, ExpectedUtility U p = t := by
  rcases hx.eq_or_lt with he | hxt
  · exact ⟨StdSimplex.single x, (expectedUtility_single U x).trans he⟩
  have hpos := sub_pos.mpr (hxt.trans_le hy)
  let a := (t - U x) / (U y - U x)
  have ha : a ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx) hpos.le, (div_le_one hpos).mpr (by linarith)⟩
  refine ⟨BinaryLottery y x a ha, ?_⟩
  rw [expectedUtility_binary]
  dsimp [a]
  field_simp
  ring

/-- Expected values of lotteries on a convex real set remain in that set. -/
theorem expectedUtility_mem_of_convex {X : Type*} {S : Set ℝ} (hS : Convex ℝ S)
    (f : X → ℝ) (hf : ∀ x, f x ∈ S) (p : SimpleLottery X) : ExpectedUtility f p ∈ S := by
  simpa only [ExpectedUtility, Finsupp.sum, smul_eq_mul] using
    hS.sum_mem (t := p.weights.support) (w := fun x => p.weights x)
      (fun x _ => p.nonneg x) p.total (fun x _ => hf x)

/-- Finite Jensen inequality over an arbitrary simple lottery on the stated domain. -/
theorem expectedUtility_jensen {X : Type*} {S : Set ℝ} {U : ℝ → ℝ} (hU : ConcaveOn ℝ S U)
    (f : X → ℝ) (hf : ∀ x, f x ∈ S) (p : SimpleLottery X) :
    ExpectedUtility (fun x => U (f x)) p ≤ U (ExpectedUtility f p) := by
  simpa only [ExpectedUtility, Finsupp.sum, smul_eq_mul] using
    hU.le_map_sum (t := p.weights.support) (w := fun x => p.weights x)
      (fun x _ => p.nonneg x) p.total (fun x _ => hf x)

/-- **Proposition 6.3:** concavity on the monetary interval is equivalent to risk aversion. -/
theorem proposition_6_3 {S : Set ℝ} (hS : Convex ℝ S) (U : ℝ → ℝ) :
    ConcaveOn ℝ S U ↔ ∀ p : SimpleLottery S,
      ExpectedUtility (fun x : S => U x) p ≤ U (ExpectedUtility Subtype.val p) := by
  refine ⟨fun hu p => expectedUtility_jensen hu Subtype.val Subtype.property p, ?_⟩
  intro h
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
  have hp := h (BinaryLottery (⟨x, hx⟩ : S) ⟨y, hy⟩ a ha')
  simpa only [expectedUtility_binary, smul_eq_mul, show 1 - a = b by linarith] using hp

/-- **Definition 6.4:** a sure prize is indifferent to the lottery. -/
def IsCertaintyEquivalent {X : Type*} (U : X → ℝ) (p : SimpleLottery X) (x : X) : Prop :=
  U x = ExpectedUtility U p

/-- **Proposition 6.5:** continuous utility on a real interval admits a certainty equivalent. -/
theorem proposition_6_5_exists {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hU : ContinuousOn U S) (p : SimpleLottery S) :
    ∃ x : S, IsCertaintyEquivalent (fun z : S => U z) p x := by
  have hconv := (hS.isPreconnected.image U hU).convex
  obtain ⟨x, hx, he⟩ := expectedUtility_mem_of_convex hconv (fun x : S => U x)
    (fun x => Set.mem_image_of_mem U x.property) p
  exact ⟨⟨x, hx⟩, he⟩

/-- Strictly increasing utility gives at most one certainty equivalent, without continuity. -/
theorem proposition_6_5_unique {X : Type*} [LinearOrder X] {U : X → ℝ} (hU : StrictMono U)
    (p : SimpleLottery X) {x y : X} (hx : IsCertaintyEquivalent U p x)
    (hy : IsCertaintyEquivalent U p y) : x = y := hU.injective (hx.trans hy.symm)

/-- Risk premium is the mean minus the certainty equivalent, in monetary units. -/
noncomputable def RiskPremium {S : Set ℝ} (p : SimpleLottery S) (c : S) : ℝ :=
  ExpectedUtility Subtype.val p - (c : ℝ)

/-- For increasing concave utility every risk premium is nonnegative. -/
theorem riskPremium_nonneg {S : Set ℝ} {U : ℝ → ℝ} (hU : ConcaveOn ℝ S U)
    (hi : StrictMonoOn U S) {p : SimpleLottery S} {c : S}
    (hc : IsCertaintyEquivalent (fun x : S => U x) p c) : 0 ≤ RiskPremium p c := by
  have hm := expectedUtility_mem_of_convex hU.1 Subtype.val Subtype.property p
  apply sub_nonneg.mpr
  exact (hi.le_iff_le c.property hm).mp (hc.le.trans ((proposition_6_3 hU.1 U).mp hU p))

end Kreps.UtilityForMoney
