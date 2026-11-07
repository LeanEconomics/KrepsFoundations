import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.Prod
import Mathlib.Geometry.Convex.Set
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Gaussian.Real
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Acts, state separability and the Sure-Thing Principle

Kreps I, pp. 79–83 and 103–105. Acts assign consequences to states. Additive state
utility implies Savage's Sure-Thing Principle. For the converse construction used in
Proposition 5.12, a utility preserving pointwise midpoints separates into the sum of
its single-state changes from a reference act.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*}

/-- An act specifies the prize in each state of nature. -/
abbrev StateAct (S X : Type*) := S → X

/-- Equation (5.1), the sum of utilities evaluated in their respective states. -/
noncomputable def StateAdditiveValue [Fintype S] (U : S → X → ℝ) (h : StateAct S X) : ℝ :=
  ∑ s, U s (h s)

/-- Equation (5.2), the probability-weighted value of a state-independent utility. -/
noncomputable def SubjectiveActValue [Fintype S] (p : S → ℝ) (U : X → ℝ)
    (h : StateAct S X) : ℝ := ∑ s, p s * U (h s)

/-- Subjective expected utility is additive with state-specific utilities scaled by probability. -/
theorem subjectiveActValue_eq_stateAdditiveValue [Fintype S] (p : S → ℝ) (U : X → ℝ)
    (h : StateAct S X) :
    SubjectiveActValue p U h = StateAdditiveValue (fun s x => p s * U x) h := rfl

/-- Axiom 5.1. Changing the common consequences off an event preserves the ranking. -/
def SureThing (r : StateAct S X → StateAct S X → Prop) : Prop :=
  ∀ (T : Set S) (a a' b b' : StateAct S X),
    (∀ s ∈ T, a s = a' s ∧ b s = b' s) →
    (∀ s ∉ T, a s = b s ∧ a' s = b' s) → (r a b ↔ r a' b')

/-- An additive representation satisfies the Sure-Thing Principle for every event. -/
theorem sureThing_of_stateAdditive [Fintype S] (U : S → X → ℝ)
    {r : StateAct S X → StateAct S X → Prop}
    (hU : ∀ a b, r a b ↔ StateAdditiveValue U b ≤ StateAdditiveValue U a) : SureThing r := by
  intro T a a' b b' hin hout
  have hd : StateAdditiveValue U a - StateAdditiveValue U b =
      StateAdditiveValue U a' - StateAdditiveValue U b' := by
    simp only [StateAdditiveValue, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ T
    · rw [(hin s hs).1, (hin s hs).2]
    · rw [(hout s hs).1, (hout s hs).2, sub_self, sub_self]
  rw [hU, hU]
  constructor <;> intro h <;> linarith

/-- The utility contribution of replacing the reference consequence in one state. -/
noncomputable def StateIncrement [DecidableEq S] (u : StateAct S X → ℝ) (base : StateAct S X)
    (s : S) (x : X) : ℝ := u (Function.update base s x) - u base

/-- Midpoint affinity makes a single-state increment independent of the other coordinates. -/
theorem stateIncrement_independent [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) (s : S) (hs : h s = base s) (x : X) :
    u (Function.update h s x) - u h = StateIncrement u base s x := by
  have he : (fun t => m (Function.update h s x t) (base t)) =
      fun t => m (h t) (Function.update base s x t) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp [hs, hsym x (base s)]
    · simp [Function.update_of_ne ht]
  have h₁ := hu (Function.update h s x) base
  have h₂ := hu h (Function.update base s x)
  rw [he] at h₁
  unfold StateIncrement
  linarith

/-- The act that agrees with the chosen act on a finite event and the reference elsewhere. -/
noncomputable def PartialAct [DecidableEq S] (base h : StateAct S X) (T : Finset S) :
    StateAct S X := fun s => if s ∈ T then h s else base s

/-- Adding one state at a time sums its reference increments over any finite event. -/
theorem partialAct_value [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) (T : Finset S) :
    u (PartialAct base h T) - u base = ∑ s ∈ T, StateIncrement u base s (h s) := by
  induction T using Finset.induction_on with
  | empty =>
    have he : PartialAct base h ∅ = base := by ext s; simp [PartialAct]
    rw [he]
    simp
  | @insert s T hst ih =>
    have he : PartialAct base h (insert s T) = Function.update (PartialAct base h T) s (h s) := by
      funext t
      by_cases ht : t = s
      · subst t
        simp [PartialAct]
      · simp [PartialAct, ht]
    have hi := stateIncrement_independent m hsym u hu base (PartialAct base h T) s
      (by simp [PartialAct, hst]) (h s)
    rw [he, Finset.sum_insert hst]
    linarith

/-- The normalized utility of a complete act is the sum of its single-state contributions. -/
theorem stateAct_decomposition [Fintype S] [DecidableEq S] (m : X → X → X)
    (hsym : ∀ x y, m x y = m y x) (u : StateAct S X → ℝ)
    (hu : ∀ h g : StateAct S X, 2 * u (fun s => m (h s) (g s)) = u h + u g)
    (base h : StateAct S X) :
    u h - u base = StateAdditiveValue (StateIncrement u base) h := by
  have he : PartialAct base h Finset.univ = h := by ext s; simp [PartialAct]
  simpa only [he, StateAdditiveValue] using partialAct_value m hsym u hu base h Finset.univ

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1 at commit `f9c357a`.
Imports and namespace are adapted for this independent project.

# Choice, preference, and utility

Kreps I, §1.1, pp. 1-4: feasible choice, finite nonemptiness, choice coherence,
complete and transitive preferences, and equations (1.1)-(1.3).

Choice is extended to the empty menu by the empty set. Nonemptiness is a separate
hypothesis, imposed only on finite nonempty menus in `FiniteNonempty`.
`FeasibleOn` and `CoherentOn` retain restricted menu domains for Problems 1.15-1.16.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {X : Type*}

/-- The complete collection of nonempty menus. -/
def FullMenus (X : Type*) : Set (Set X) := {A | A.Nonempty}

/-- A choice rule returns a set of acceptable alternatives from each menu. -/
abbrev ChoiceRule (X : Type*) := Set X → Set X

/-- Feasibility on an explicitly specified menu domain. -/
def FeasibleOn (menus : Set (Set X)) (c : ChoiceRule X) : Prop :=
  ∀ A ∈ menus, c A ⊆ A

/-- Feasibility for the full-domain extension, including the empty menu. -/
def Feasible (c : ChoiceRule X) : Prop := ∀ A, c A ⊆ A

/-- **Definition 1.1a.** Choice is nonempty on every finite nonempty menu. -/
def FiniteNonempty (c : ChoiceRule X) : Prop :=
  ∀ A, A.Finite → A.Nonempty → (c A).Nonempty

/-- **Definition 1.1b.** Coherence with an explicit admissible-menu domain. -/
def CoherentOn (menus : Set (Set X)) (c : ChoiceRule X) : Prop :=
  ∀ A ∈ menus, ∀ B ∈ menus, ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B,
    x ∈ c A → y ∉ c A → y ∉ c B

/-- **Definition 1.1b.** Full-domain choice coherence. -/
def Coherent (c : ChoiceRule X) : Prop :=
  ∀ A B, ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, x ∈ c A → y ∉ c A → y ∉ c B

/-- **Definition 1.1c.** Every pair of alternatives can be compared. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- **Definition 1.1d.** The preference relation is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- Complete and transitive weak preference; indifference is allowed. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Equation (1.2): all alternatives at least as good as every menu member. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Equation (1.3): preference induced by a real-valued utility function. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- Equation (1.1): the full set of utility-maximizing alternatives. -/
def UtilityChoice (u : X → ℝ) : ChoiceRule X := PrefChoice (UtilityPref u)

/-- A numerical function represents preference, with the book's orientation. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Preference revealed by choice from pairs, including singleton pairs. -/
def Revealed (c : ChoiceRule X) (x y : X) : Prop := x ∈ c {x, y}

/-- Strict preference derived from weak preference. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference derived from weak preference. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- **Definition 1.6**, p. 7: the alternatives no better than `x`. -/
def NoBetterThan (r : X → X → Prop) (x : X) : Set X := {y | r x y}

/-- Complete preferences are reflexive. -/
theorem complete_refl {r : X → X → Prop} (hc : Complete r) (x : X) : r x x :=
  (hc x x).elim id id

/-- Choice generated by a preference relation is feasible. -/
theorem prefChoice_feasible (r : X → X → Prop) : Feasible (PrefChoice r) :=
  fun _ _ h => h.1

/-- A feasible full-domain choice selects nothing from the empty menu. -/
theorem feasible_empty {c : ChoiceRule X} (hc : Feasible c) : c ∅ = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hc ∅ hx

/-- Equal numerical representations give identical maximizing sets. -/
theorem represents_choice {u : X → ℝ} {r : X → X → Prop} (hu : Represents u r) :
    PrefChoice r = UtilityChoice u := by
  ext A x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨hx, fun y hy => (hu x y).mp (hr y hy)⟩
  · rintro ⟨hx, hu'⟩
    exact ⟨hx, fun y hy => (hu x y).mpr (hu' y hy)⟩

/-- The full-domain coherence condition is exactly coherence on nonempty menus. -/
theorem coherent_iff_on_full {c : ChoiceRule X} :
    Coherent c ↔ CoherentOn (FullMenus X) c := by
  constructor
  · intro h A _ B _ x hx y hy
    exact h A B x hx y hy
  · intro h A B x hx y hy
    exact h A ⟨x, hx.1⟩ B ⟨x, hx.2⟩ x hx y hy

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy from Chapter 1 at commit `f9c357a`.
Imports and namespace are adapted for this independent project.

# Strict preference and indifference

Kreps I, §1.4, Propositions 1.9-1.10, pp. 9-10, and Problem 1.9, p. 26.
The two presentations of rational preference are equivalent: complete, transitive
weak preference, or asymmetric, negatively transitive strict preference.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {X : Type*} {r : X → X → Prop}

/-- A strict preference cannot run both ways. -/
def AsymmetricPref (s : X → X → Prop) : Prop := ∀ x y, s x y → ¬s y x

/-- The book's disjunctive formulation of negative transitivity. -/
def NegativelyTransitive (s : X → X → Prop) : Prop :=
  ∀ x y z, s x y → s z y ∨ s x z

/-- Recover weak preference by denying the reversed strict preference. -/
def WeakFromStrict (s : X → X → Prop) (x y : X) : Prop := ¬s y x

/-- Recover indifference when neither strict comparison holds. -/
def IndifferenceFromStrict (s : X → X → Prop) (x y : X) : Prop :=
  ¬s x y ∧ ¬s y x

/-- **Proposition 1.9a**, p. 9. -/
theorem proposition_1_9a (hc : Complete r) (x y : X) : Strict r x y ↔ ¬r y x :=
  ⟨And.right, fun h => ⟨(hc x y).resolve_right h, h⟩⟩

/-- **Proposition 1.9b**, p. 9. No completeness assumption is needed. -/
theorem proposition_1_9b (r : X → X → Prop) : AsymmetricPref (Strict r) :=
  fun _ _ hxy hyx => hxy.2 hyx.1

/-- First half of **Proposition 1.9g**, p. 9. -/
theorem strict_weak_trans (ht : TransitivePref r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨ht x y z hxy.1 hyz, fun hzx => hxy.2 (ht y z x hyz hzx)⟩

/-- Second half of **Proposition 1.9g**, p. 9. -/
theorem weak_strict_trans (ht : TransitivePref r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨ht x y z hxy hyz.1, fun hzx => hyz.2 (ht z x y hzx hxy)⟩

/-- **Proposition 1.9c**, p. 9. -/
theorem proposition_1_9c (hr : Rational r) : NegativelyTransitive (Strict r) := by
  intro x y z hxy
  by_cases hzy : Strict r z y
  · exact Or.inl hzy
  · right
    have hyz : r y z := by
      by_contra h
      exact hzy ((proposition_1_9a hr.1 z y).mpr h)
    exact strict_weak_trans hr.2 hxy hyz

/-- **Proposition 1.9d**, p. 9: reflexivity of indifference. -/
theorem proposition_1_9d (hc : Complete r) (x : X) : Indifferent r x x :=
  ⟨complete_refl hc x, complete_refl hc x⟩

/-- **Proposition 1.9e**, p. 9: symmetry of indifference. -/
theorem proposition_1_9e {x y : X} (hxy : Indifferent r x y) : Indifferent r y x :=
  ⟨hxy.2, hxy.1⟩

/-- **Proposition 1.9f**, p. 9: transitivity of indifference. -/
theorem proposition_1_9f (ht : TransitivePref r) {x y z : X}
    (hxy : Indifferent r x y) (hyz : Indifferent r y z) : Indifferent r x z :=
  ⟨ht x y z hxy.1 hyz.1, ht z y x hyz.2 hxy.2⟩

/-- **Proposition 1.9g**, p. 9: both mixed transitivity statements. -/
theorem proposition_1_9g (ht : TransitivePref r) (x y z : X) :
    (Strict r x y → r y z → Strict r x z) ∧
      (r x y → Strict r y z → Strict r x z) :=
  ⟨fun hxy hyz => strict_weak_trans ht hxy hyz,
    fun hxy hyz => weak_strict_trans ht hxy hyz⟩

/-- **Proposition 1.9h**, p. 9: transitivity of strict preference. -/
theorem proposition_1_9h (ht : TransitivePref r) : TransitivePref (Strict r) :=
  fun _ _ _ hxy hyz => strict_weak_trans ht hxy hyz.1

/-- **Proposition 1.10**, p. 10: reconstruction, including both recovered relations. -/
theorem proposition_1_10 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    by_cases h : s y x
    · exact Or.inr (ha y x h)
    · exact Or.inl h
  · intro x y z hxy hyz hzx
    exact (hn z x y hzx).elim hxy hyz
  · funext x y
    apply propext
    change (¬s y x ∧ ¬¬s x y) ↔ s x y
    exact ⟨fun h => not_not.mp h.2, fun h => ⟨ha x y h, not_not.mpr h⟩⟩
  · funext x y
    exact propext and_comm

/-- **Problem 1.9**, p. 26: the reconstructed weak relation is complete and transitive. -/
theorem problem_1_9 {s : X → X → Prop}
    (ha : AsymmetricPref s) (hn : NegativelyTransitive s) :
    Rational (WeakFromStrict s) ∧
      Strict (WeakFromStrict s) = s ∧
      Indifferent (WeakFromStrict s) = IndifferenceFromStrict s :=
  proposition_1_10 ha hn

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Mixture spaces and their preference axioms

Kreps I, Sections 5.1–5.2, pp. 88–92. Mathlib's convex spaces supply the
usual mixture identities on abstract spaces. The independence axiom compares
different common backgrounds at a fixed weight, including both endpoint weights.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- A mixture weight, including both endpoints. -/
abbrev Weight := Set.Icc (0 : ℝ) 1

/-- The mixture with probability `a` on the first alternative. -/
noncomputable def Mix {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x y : Z) : Z :=
  convexCombPair a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
    (by ring) x y

/-- A numerical index is affine in the book's binary mixtures. -/
def AffineInMix {Z : Type*} [ConvexSpace ℝ Z] (u : Z → ℝ) : Prop :=
  ∀ (a : Weight) x y, u (Mix a x y) = a.val * u x + (1 - a.val) * u y

/-- Part (b) of Proposition 5.4 compares strict rankings under a change of common background. -/
def BackgroundIndependent {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ (a : Weight) x y z w,
    Strict r (Mix a x z) (Mix a y z) ↔ Strict r (Mix a x w) (Mix a y w)

/-- Part (c) of Proposition 5.4 requires both strict comparisons near weight one. -/
def MixtureContinuous {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ x y, Strict r x y → ∀ z, ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ a : Weight,
    c < a.val → Strict r (Mix a x z) y ∧ Strict r x (Mix a y z)

/-- The three primitive hypotheses of the mixture-space theorem. -/
def MixtureAxioms {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  Rational r ∧ BackgroundIndependent r ∧ MixtureContinuous r

/-- Complementary mixture weight. -/
def Complement (a : Weight) : Weight :=
  ⟨1 - a.val, sub_nonneg.mpr a.property.2, sub_le_self _ a.property.1⟩

/-- Mixing a point with itself leaves it fixed. -/
theorem mix_self {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x : Z) : Mix a x x = x :=
  convexCombPair_same _ _ _

/-- Zero weight selects the second alternative. -/
theorem mix_zero {Z : Type*} [ConvexSpace ℝ Z] (x y : Z) : Mix 0 x y = y := by
  simp [Mix]

/-- Unit weight selects the first alternative. -/
theorem mix_one {Z : Type*} [ConvexSpace ℝ Z] (x y : Z) : Mix 1 x y = x := by
  simp [Mix]

/-- Complementing the weight and swapping alternatives preserves a mixture. -/
theorem mix_swap {Z : Type*} [ConvexSpace ℝ Z] (a : Weight) (x y : Z) :
    Mix a x y = Mix (Complement a) y x := by
  unfold Mix Complement
  rw [convexCombPair_symm]
  congr 1
  ring

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite-support lotteries and expected utility

Kreps I, Definition 5.2 and equation (5.3), pp. 85–88. Prize types may be
infinite. Mathlib's standard simplex gives each lottery its own finite support.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- A finitely supported probability distribution on an arbitrary prize space. -/
abbrev SimpleLottery (X : Type*) := StdSimplex ℝ X

/-- Degenerate lottery paying the given prize with certainty. -/
noncomputable def PureLottery {X : Type*} (x : X) : SimpleLottery X :=
  StdSimplex.single x

/-- The finite support sum of probability times prize utility. -/
noncomputable def ExpectedUtility {X : Type*} (U : X → ℝ) (p : SimpleLottery X) : ℝ :=
  p.weights.sum (fun x a => a * U x)

/-- Expected utility equals Mathlib's barycentric evaluation of the prize index. -/
theorem expectedUtility_eq_affineMap {X : Type*} (U : X → ℝ) (p : SimpleLottery X) :
    ExpectedUtility U p = StdSimplex.affineMapMk U p := by
  rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum]
  rfl

/-- A sure prize has exactly its specified prize utility. -/
theorem expectedUtility_pure {X : Type*} (U : X → ℝ) (x : X) :
    ExpectedUtility U (PureLottery x) = U x := by
  rw [expectedUtility_eq_affineMap]
  exact StdSimplex.affineMapMk_single U x

/-- Reduction of compound lotteries is coordinatewise probability averaging. -/
theorem lottery_mix_weight {X : Type*} (a : Weight) (p q : SimpleLottery X) (x : X) :
    (Mix a p q).weights x = a.val * p.weights x + (1 - a.val) * q.weights x := by
  simp [Mix]

/-- Expected utility is affine under objective mixtures of any two simple lotteries. -/
theorem expectedUtility_affine {X : Type*} (U : X → ℝ) : AffineInMix (ExpectedUtility U) := by
  intro a p q
  simp only [expectedUtility_eq_affineMap, Mix]
  rw [(StdSimplex.affineMapMk U).isAffineMap.map_convexCombPair, convexCombPair_eq_sum]
  rfl

/-- On a finite prize type the support sum also equals the sum over the entire type. -/
theorem expectedUtility_eq_sum {X : Type*} [Fintype X] (U : X → ℝ) (p : SimpleLottery X) :
    ExpectedUtility U p = ∑ x, p.weights x * U x := by
  exact Finsupp.sum_fintype _ _ (by simp)

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Algebra of a binary mixture segment

Kreps I, p. 89. Two nested mixtures of the same prizes reduce to a single
mixture whose first probability is the weighted mean of the inner probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- A weighted mean of two probabilities lies in the unit interval. -/
def WeightMean (a b c : Weight) : Weight :=
  ⟨a.val * b.val + (1 - a.val) * c.val,
    add_nonneg (mul_nonneg a.property.1 b.property.1)
      (mul_nonneg (sub_nonneg.mpr a.property.2) c.property.1), by
    nlinarith [mul_nonneg a.property.1 (sub_nonneg.mpr b.property.2),
      mul_nonneg (sub_nonneg.mpr a.property.2) (sub_nonneg.mpr c.property.2)]⟩

/-- A mixture of mixtures on the same segment reduces to one weighted mean. -/
theorem mix_mix {Z : Type*} [ConvexSpace ℝ Z] (a b c : Weight) (x y : Z) :
    Mix a (Mix b x y) (Mix c x y) = Mix (WeightMean a b c) x y := by
  let d (t : Weight) : StdSimplex ℝ Z :=
    .duple x y t.property.1 (sub_nonneg.mpr t.property.2) (by ring)
  change Mix a (sConvexComb (d b)) (sConvexComb (d c)) = sConvexComb (d _)
  unfold Mix
  rw [← sConvexComb_convexCombPair]
  apply congrArg sConvexComb
  apply StdSimplex.ext
  classical
  simp only [StdSimplex.weights_convexCombPair, d, StdSimplex.weights_duple, smul_add,
    Finsupp.smul_single, smul_eq_mul, WeightMean]
  rw [add_add_add_comm, ← Finsupp.single_add, ← Finsupp.single_add]
  congr 2
  ring

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Background substitution and equally spaced comparisons

Kreps I, Lemmas 5.5–5.7, pp. 91–92. At fixed mixture weight a common
background can be replaced in either a strict or a weak comparison. Along a
single segment, comparisons separated by the same probability increment are
therefore identical. This holds before any continuity assumption is imposed.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Background substitution for weak comparison. -/
def WeakBackgroundIndependent (r : Z → Z → Prop) : Prop :=
  ∀ (a : Weight) x y z w, r (Mix a x z) (Mix a y z) ↔ r (Mix a x w) (Mix a y w)

/-- **Lemma 5.5:** a strict comparison for some common background holds for every background. -/
theorem lemma_5_5_some_iff : BackgroundIndependent r ↔
    ∀ (a : Weight) x y, (∃ z, Strict r (Mix a x z) (Mix a y z)) →
      ∀ w, Strict r (Mix a x w) (Mix a y w) := by
  constructor
  · rintro h a x y ⟨z, hz⟩ w
    exact (h a x y z w).mp hz
  · intro h a x y z w
    exact ⟨fun hz => h a x y ⟨z, hz⟩ w, fun hw => h a x y ⟨w, hw⟩ z⟩

/-- **Lemma 5.5:** weak and strict background-independence are equivalent for complete tastes. -/
theorem lemma_5_5_weak_iff (hc : Complete r) :
    BackgroundIndependent r ↔ WeakBackgroundIndependent r := by
  constructor
  · intro h a x y z w
    have he := h a y x z w
    rw [proposition_1_9a hc, proposition_1_9a hc] at he
    exact not_iff_not.mp he
  · intro h a x y z w
    rw [proposition_1_9a hc, proposition_1_9a hc]
    exact not_congr (h a y x z w)

/-- **Lemma 5.5:** a common background can also be replaced in an indifference comparison. -/
theorem lemma_5_5_indifferent (hc : Complete r) (hi : BackgroundIndependent r)
    (a : Weight) (x y z w : Z) :
    Indifferent r (Mix a x z) (Mix a y z) ↔ Indifferent r (Mix a x w) (Mix a y w) :=
  and_congr ((lemma_5_5_weak_iff hc).mp hi a x y z w)
    ((lemma_5_5_weak_iff hc).mp hi a y x z w)

/-- Moving the common background along a segment translates a probability increment. -/
theorem segment_shift {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val)
    (x y : Z) : ∃ z, Mix d x z = Mix t x y ∧ Mix d y z = Mix s x y := by
  have hp : 0 < 1 - d.val := sub_pos.mpr hd
  let b : Weight := ⟨s.val / (1 - d.val), div_nonneg s.property.1 hp.le,
    (div_le_one hp).mpr (by linarith [t.property.2])⟩
  refine ⟨Mix b x y, ?_, ?_⟩
  · calc
      Mix d x (Mix b x y) = Mix d (Mix 1 x y) (Mix b x y) := by rw [mix_one]
      _ = Mix (WeightMean d 1 b) x y := mix_mix ..
      _ = Mix t x y := by
        apply congrArg (fun a => Mix a x y)
        apply Subtype.ext
        change d.val * 1 + (1 - d.val) * (s.val / (1 - d.val)) = t.val
        rw [mul_comm (1 - d.val), div_mul_cancel₀ _ hp.ne']
        linarith
  · calc
      Mix d y (Mix b x y) = Mix d (Mix 0 x y) (Mix b x y) := by rw [mix_zero]
      _ = Mix (WeightMean d 0 b) x y := mix_mix ..
      _ = Mix s x y := by
        apply congrArg (fun a => Mix a x y)
        apply Subtype.ext
        change d.val * 0 + (1 - d.val) * (s.val / (1 - d.val)) = s.val
        rw [mul_zero, zero_add, mul_comm, div_mul_cancel₀ _ hp.ne']

/-- Equal upward increments have the same weak comparison at every admissible starting point. -/
theorem segment_step_weak (hr : Rational r) (hi : BackgroundIndependent r) (x y : Z)
    {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val) :
    r (Mix t x y) (Mix s x y) ↔ r (Mix d x y) y := by
  obtain ⟨z, hz, hz'⟩ := segment_shift hd he x y
  simpa only [hz, hz', mix_self] using (lemma_5_5_weak_iff hr.1).mp hi d x y z y

/-- Equal upward increments have the same strict comparison at every admissible starting point. -/
theorem segment_step_strict (hi : BackgroundIndependent r) (x y : Z)
    {d t s : Weight} (hd : d.val < 1) (he : t.val = s.val + d.val) :
    Strict r (Mix t x y) (Mix s x y) ↔ Strict r (Mix d x y) y := by
  obtain ⟨z, hz, hz'⟩ := segment_shift hd he x y
  simpa only [hz, hz', mix_self] using hi d x y z y

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preferences on probability grids

Kreps I, proof of Lemma 5.7, pp. 91–92. Background substitution makes all
adjacent intervals of a grid comparable in the same direction. A chain of
those intervals transfers comparisons between endpoints to every rational grid
weight. Equal-step grids include the dyadic ones in the printed proof.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Probability at the specified grid point with a positive denominator. -/
noncomputable def GridWeight (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) : Weight :=
  ⟨(j : ℝ) / n, by positivity, (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hj)⟩

/-- At the last grid point the full first alternative is selected. -/
theorem gridWeight_last (n : ℕ) (hn : 0 < n) : GridWeight n n hn le_rfl = 1 := by
  apply Subtype.ext
  change (n : ℝ) / n = 1
  exact div_self (by positivity)

/-- At the first grid point the second alternative is selected. -/
theorem gridWeight_zero (n : ℕ) (hn : 0 < n) : GridWeight n 0 hn (Nat.zero_le _) = 0 := by
  apply Subtype.ext
  simp [GridWeight]

/-- Each step of the grid has probability increment one over the denominator. -/
theorem gridWeight_step {n i : ℕ} (hi : i < n) :
    (GridWeight n (i + 1) (by omega) hi).val =
      (GridWeight n i (by omega) hi.le).val + (GridWeight n 1 (by omega) (by omega)).val := by
  simp [GridWeight, add_div]

/-- Chaining a common comparison from the first grid interval to any positive grid point. -/
theorem grid_chain {P : Z → Z → Prop} (ht : TransitivePref P) (x y : Z) {n : ℕ} (hn : 0 < n)
    (h : ∀ i (hi : i < n), P (Mix (GridWeight n (i + 1) hn hi) x y)
      (Mix (GridWeight n i hn hi.le) x y)) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    P (Mix (GridWeight n m hn hmn) x y) y := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hi : m < n := by omega
    by_cases hz : m = 0
    · subst m
      simpa only [gridWeight_zero, mix_zero] using h 0 hi
    · exact ht _ _ _ (h m hi) (ih (by omega) hi.le)

/-- Weak upward grid comparisons all agree with the endpoint comparison. -/
theorem grid_weak (hr : Rational r) (hi : BackgroundIndependent r) {x y : Z} (hxy : r x y)
    {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) :
    r (Mix (GridWeight n m (by omega) hmn) x y) y := by
  have hd : (GridWeight n 1 (by omega) (by omega)).val < 1 := by
    simp only [GridWeight, Nat.cast_one]
    exact (div_lt_one (by positivity)).mpr (by exact_mod_cast hn)
  have hs (i : ℕ) (h : i < n) := segment_step_weak hr hi x y hd (gridWeight_step h)
  have hu : r (Mix (GridWeight n 1 (by omega) (by omega)) x y) y := by
    by_contra h
    have hrev := grid_chain (P := fun a b => Strict r b a)
      (fun a b c hab hbc => proposition_1_9h hr.2 c b a hbc hab) x y (by omega : 0 < n)
      (fun i hni => (proposition_1_9a hr.1 _ _).mpr (fun hc => h ((hs i hni).mp hc)))
      (m := n) (by omega) le_rfl
    rw [gridWeight_last, mix_one] at hrev
    exact hrev.2 hxy
  exact grid_chain hr.2 x y (by omega) (fun i h => (hs i h).mpr hu) hm hmn

/-- Strict upward grid comparisons all agree with the strict endpoint comparison. -/
theorem grid_strict (hr : Rational r) (hi : BackgroundIndependent r) {x y : Z}
    (hxy : Strict r x y) {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) :
    Strict r (Mix (GridWeight n m (by omega) hmn) x y) y := by
  have hd : (GridWeight n 1 (by omega) (by omega)).val < 1 := by
    simp only [GridWeight, Nat.cast_one]
    exact (div_lt_one (by positivity)).mpr (by exact_mod_cast hn)
  have hs (i : ℕ) (h : i < n) := segment_step_strict hi x y hd (gridWeight_step h)
  have hu : Strict r (Mix (GridWeight n 1 (by omega) (by omega)) x y) y := by
    by_contra h
    have hrev := grid_chain (P := fun a b => r b a)
      (fun a b c hab hbc => hr.2 c b a hbc hab) x y (by omega : 0 < n)
      (fun i hni => not_not.mp (fun hc => h ((hs i hni).mp
        ((proposition_1_9a hr.1 _ _).mpr hc)))) (m := n) (by omega) le_rfl
    rw [gridWeight_last, mix_one] at hrev
    exact hxy.2 hrev
  exact grid_chain (proposition_1_9h hr.2) x y (by omega) (fun i h => (hs i h).mpr hu) hm hmn

/-- Every nonempty open subinterval of probabilities contains a positive grid point. -/
theorem exists_gridWeight_between {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (n m : ℕ) (hn : 1 < n) (_hm : 0 < m) (hmn : m ≤ n),
      a < (GridWeight n m (by omega) hmn).val ∧ (GridWeight n m (by omega) hmn).val < b := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (b - a)⁻¹)
  have hn' : 1 < n := by exact_mod_cast (le_max_left _ _).trans_lt hn
  obtain ⟨z, hz, hz'⟩ := exists_div_btwn hab ((le_max_right _ _).trans_lt hn)
  have hnpos : (0 : ℝ) < n := by positivity
  have hzpos : (0 : ℝ) < z := (div_pos_iff_of_pos_right hnpos).mp (ha.trans_lt hz)
  have hzi : 0 ≤ z := by exact_mod_cast hzpos.le
  lift z to ℕ using hzi
  have hm : 0 < z := by exact_mod_cast hzpos
  have hmn : z ≤ n := by exact_mod_cast (div_le_one hnpos).mp (hz'.le.trans hb)
  exact ⟨n, z, hn', hm, hmn, by simpa [GridWeight] using hz, by simpa [GridWeight] using hz'⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Order on a mixture segment

Kreps I, Lemmas 5.6–5.8, pp. 91–92. First transfer weak comparisons on rational
grids to every probability by the endpoint continuity axiom. A strictly ordered
pair then gives strict monotonicity at every positive probability increment.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The lower endpoint is weakly dominated at every probability of the better outcome. -/
theorem segment_base_weak (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (d : Weight) :
    r (Mix d x y) y := by
  by_cases hz : d.val = 0
  · have he : d = 0 := Subtype.ext hz
    rw [he, mix_zero]
    exact complete_refl h.1.1 y
  have hd := lt_of_le_of_ne d.property.1 (Ne.symm hz)
  by_contra hn
  have hrev := (proposition_1_9a h.1.1 _ _).mpr hn
  obtain ⟨c, hc, ht⟩ := h.2.2 y (Mix d x y) hrev y
  obtain ⟨n, m, hN, hM, hMN, hlo, hhi⟩ := exists_gridWeight_between
    (mul_nonneg hc.1.le hd.le) (mul_lt_of_lt_one_left hd hc.2) d.property.2
  let q := GridWeight n m (by omega) hMN
  let a : Weight := ⟨q.val / d.val, div_nonneg q.property.1 hd.le,
    (div_le_one hd).mpr hhi.le⟩
  have hca : c < a.val := (lt_div_iff₀ hd).mpr hlo
  have he : Mix a (Mix d x y) y = Mix q x y := by
    calc
      _ = Mix a (Mix d x y) (Mix 0 x y) := by rw [mix_zero]
      _ = Mix (WeightMean a d 0) x y := mix_mix ..
      _ = Mix q x y := by
        apply congrArg (fun t => Mix t x y)
        apply Subtype.ext
        change q.val / d.val * d.val + _ * 0 = _
        rw [mul_zero, add_zero, div_mul_cancel₀ _ hd.ne']
  have bad := (ht a hca).2
  rw [he] at bad
  exact bad.2 (grid_weak h.1 h.2.1 hxy hN hM hMN)

/-- Increasing the probability of a weakly better endpoint is weakly preferred. -/
theorem segment_mono (h : MixtureAxioms r) {x y : Z} (hxy : r x y)
    {s t : Weight} (hst : s.val ≤ t.val) : r (Mix t x y) (Mix s x y) := by
  let d : Weight := ⟨t.val - s.val, sub_nonneg.mpr hst,
    (sub_le_self _ s.property.1).trans t.property.2⟩
  have he : t.val = s.val + d.val := by dsimp [d]; ring
  by_cases hd : d.val < 1
  · exact (segment_step_weak h.1 h.2.1 x y hd he).mpr (segment_base_weak h hxy d)
  · have h0 : s = 0 := Subtype.ext (by change s.val = 0; linarith [t.property.2, s.property.1])
    have h1 : t = 1 := Subtype.ext (by change t.val = 1; linarith [t.property.2, s.property.1])
    rwa [h0, h1, mix_one, mix_zero]

/-- Every positive probability of a strictly better endpoint strictly improves on the baseline. -/
theorem segment_base_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (d : Weight) (hd : 0 < d.val) : Strict r (Mix d x y) y := by
  obtain ⟨n, m, hN, hM, hMN, _, hhi⟩ := exists_gridWeight_between le_rfl hd d.property.2
  exact weak_strict_trans h.1.2 (segment_mono h hxy.1 hhi.le)
    (grid_strict h.1 h.2.1 hxy hN hM hMN)

/-- **Lemma 5.7:** more probability on a strictly preferred endpoint is strictly preferred. -/
theorem lemma_5_7_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    {s t : Weight} (hst : s.val < t.val) : Strict r (Mix t x y) (Mix s x y) := by
  let d : Weight := ⟨t.val - s.val, sub_nonneg.mpr hst.le,
    (sub_le_self _ s.property.1).trans t.property.2⟩
  have he : t.val = s.val + d.val := by dsimp [d]; ring
  by_cases hd : d.val < 1
  · exact (segment_step_strict h.2.1 x y hd he).mpr
      (segment_base_strict h hxy d (sub_pos.mpr hst))
  · have h0 : s = 0 := Subtype.ext (by change s.val = 0; linarith [t.property.2, s.property.1])
    have h1 : t = 1 := Subtype.ext (by change t.val = 1; linarith [t.property.2, s.property.1])
    rwa [h0, h1, mix_one, mix_zero]

/-- The mixture lies between its weakly ordered endpoints. -/
theorem segment_bounds (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (a : Weight) :
    r x (Mix a x y) ∧ r (Mix a x y) y := by
  refine ⟨?_, segment_base_weak h hxy a⟩
  simpa only [mix_one] using segment_mono h hxy (s := a) (t := 1) a.property.2

/-- **Lemma 5.7:** every mixture of indifferent endpoints is indifferent to both. -/
theorem lemma_5_7_indifferent (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y)
    (a : Weight) : Indifferent r x (Mix a x y) ∧ Indifferent r (Mix a x y) y := by
  obtain ⟨hx, hy⟩ := segment_bounds h hxy.1 a
  exact ⟨⟨hx, h.1.2 _ y x hy hxy.2⟩, ⟨hy, h.1.2 y x _ hxy.2 hx⟩⟩

/-- **Lemma 5.6:** the midpoint lies strictly between strictly ranked endpoints. -/
theorem lemma_5_6_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y) :
    let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
    Strict r x (Mix a x y) ∧ Strict r (Mix a x y) y := by
  intro a
  refine ⟨?_, segment_base_strict h hxy a (by dsimp [a]; norm_num)⟩
  simpa only [mix_one] using lemma_5_7_strict h hxy (s := a) (t := 1) (by dsimp [a]; norm_num)

/-- **Lemma 5.6:** the midpoint of indifferent endpoints is indifferent to both. -/
theorem lemma_5_6_indifferent (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y) :
    let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
    Indifferent r x (Mix a x y) ∧ Indifferent r (Mix a x y) y :=
  lemma_5_7_indifferent h hxy _

/-- Mixing with a common background preserves any weak comparison. -/
theorem mix_monotone (h : MixtureAxioms r) {x y : Z} (hxy : r x y) (a : Weight) (z : Z) :
    r (Mix a x z) (Mix a y z) := by
  apply ((lemma_5_5_weak_iff h.1.1).mp h.2.1 a x y y z).mp
  rw [mix_self]
  exact segment_base_weak h hxy a

/-- Mixing with a common background at positive first weight preserves strict comparison. -/
theorem mix_strict (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (a : Weight) (ha : 0 < a.val) (z : Z) : Strict r (Mix a x z) (Mix a y z) := by
  apply (h.2.1 a x y y z).mp
  rw [mix_self]
  exact segment_base_strict h hxy a ha

/-- **Lemma 5.8:** indifferent alternatives can be substituted into any binary mixture. -/
theorem lemma_5_8 (h : MixtureAxioms r) {x y : Z} (hxy : Indifferent r x y)
    (a : Weight) (z : Z) : Indifferent r (Mix a x z) (Mix a y z) :=
  ⟨mix_monotone h hxy.1 a z, mix_monotone h hxy.2 a z⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Calibration on a preference segment

Kreps I, Lemma 5.9, pp. 92–93. Take the supremum of the probabilities at which
the reference alternative is weakly preferred to the mixture. Either strict
ranking at this cut would contradict endpoint continuity or its supremum property.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- An alternative lies weakly between two ordered reference alternatives. -/
def Between (r : Z → Z → Prop) (hi lo z : Z) : Prop := r hi z ∧ r z lo

/-- On a strictly ordered segment the weak preference compares the weights exactly. -/
theorem segment_compare_iff (h : MixtureAxioms r) {x y : Z} (hxy : Strict r x y)
    (s t : Weight) : r (Mix s x y) (Mix t x y) ↔ t.val ≤ s.val := by
  refine ⟨fun hw => ?_, segment_mono h hxy.1⟩
  by_contra! hn
  exact (lemma_5_7_strict h hxy hn).2 hw

/-- **Lemma 5.9:** every intermediate alternative is indifferent to a mixture of the endpoints. -/
theorem lemma_5_9 (h : MixtureAxioms r) {x y z : Z} (hz : Between r x y z) :
    ∃ a : Weight, Indifferent r z (Mix a x y) := by
  let A : Set ℝ := {v | ∃ a : Weight, a.val = v ∧ r z (Mix a x y)}
  have hxy : r x y := h.1.2 _ z _ hz.1 hz.2
  have hA0 : (0 : ℝ) ∈ A := ⟨0, rfl, by simpa only [mix_zero] using hz.2⟩
  have hbound : (1 : ℝ) ∈ upperBounds A := fun _ ⟨a, ha, _⟩ => ha ▸ a.property.2
  let a : Weight := ⟨sSup A, le_csSup ⟨1, hbound⟩ hA0, csSup_le ⟨0, hA0⟩ hbound⟩
  refine ⟨a, ?_, ?_⟩
  · by_contra hn
    have hs := (proposition_1_9a h.1.1 _ _).mpr hn
    obtain ⟨c, hc, ht⟩ := h.2.2 _ _ hs y
    let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc.1, hc.2]⟩
    have hp := (ht t (by dsimp [t]; linarith [hc.2])).1
    have hpos : 0 < a.val := by
      by_contra! hzero
      have he : a = 0 := Subtype.ext (le_antisymm hzero a.property.1)
      rw [he, mix_zero] at hn
      exact hn hz.2
    let b := WeightMean t a 0
    have he : Mix t (Mix a x y) y = Mix b x y := by
      calc
        _ = Mix t (Mix a x y) (Mix 0 x y) := by rw [mix_zero]
        _ = _ := mix_mix ..
    rw [he] at hp
    have hb : b.val ∈ upperBounds A := by
      rintro _ ⟨w, rfl, hw⟩
      by_contra! hbw
      exact hp.2 (h.1.2 z _ _ hw (segment_mono h hxy hbw.le))
    have hab : a.val ≤ b.val := csSup_le ⟨0, hA0⟩ hb
    change _ ≤ t.val * a.val + (1 - t.val) * 0 at hab
    have htt : t.val < 1 := by dsimp [t]; linarith [hc.2]
    nlinarith [mul_pos (sub_pos.mpr htt) hpos]
  · by_contra hn
    have hs := (proposition_1_9a h.1.1 _ _).mpr hn
    obtain ⟨c, hc, ht⟩ := h.2.2 _ _ hs x
    let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc.1, hc.2]⟩
    have hp := (ht t (by dsimp [t]; linarith [hc.2])).2
    have hlt : a.val < 1 := by
      by_contra! hone
      have he : a = 1 := Subtype.ext (le_antisymm a.property.2 hone)
      rw [he, mix_one] at hn
      exact hn hz.1
    let b := WeightMean t a 1
    have he : Mix t (Mix a x y) x = Mix b x y := by
      calc
        _ = Mix t (Mix a x y) (Mix 1 x y) := by rw [mix_one]
        _ = _ := mix_mix ..
    rw [he] at hp
    have hab : b.val ≤ a.val := le_csSup ⟨1, hbound⟩ (show b.val ∈ A from ⟨b, rfl, hp.1⟩)
    change t.val * a.val + (1 - t.val) * 1 ≤ _ at hab
    have htt : t.val < 1 := by dsimp [t]; linarith [hc.2]
    nlinarith [mul_pos (sub_pos.mpr htt) (sub_pos.mpr hlt)]

/-- **Lemma 5.9, uniqueness:** strict endpoints identify the calibrating probability. -/
theorem lemma_5_9_unique (h : MixtureAxioms r) {x y z : Z} (hxy : Strict r x y)
    {a b : Weight} (ha : Indifferent r z (Mix a x y)) (hb : Indifferent r z (Mix b x y)) :
    a = b := by
  apply Subtype.ext
  apply le_antisymm
  · exact (segment_compare_iff h hxy b a).mp (h.1.2 _ z _ hb.2 ha.1)
  · exact (segment_compare_iff h hxy a b).mp (h.1.2 _ z _ ha.2 hb.1)

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Affine utility calibrated between two anchors

Kreps I, Proposition 5.4, pp. 93–95. Within any interval with strictly ranked
endpoints, the unique indifferent probability represents all comparisons and
preserves mixtures. Other alternatives in the surrounding space need not be
bounded by these endpoints.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The calibrating weight whenever a reference segment contains an indifferent point. -/
noncomputable def AnchorWeight (r : Z → Z → Prop) (hi lo z : Z) : Weight := by
  classical
  exact if h : ∃ a : Weight, Indifferent r z (Mix a hi lo) then h.choose else 0

/-- On the reference interval, the chosen probability has the stated indifference property. -/
theorem anchorWeight_indifferent (h : MixtureAxioms r) {hi lo z : Z}
    (hz : Between r hi lo z) : Indifferent r z (Mix (AnchorWeight r hi lo z) hi lo) := by
  have he := lemma_5_9 h hz
  simpa [AnchorWeight, he] using he.choose_spec

/-- Give both endpoints indifferent replacements without changing the compound's rank. -/
theorem mix_congr_indifferent (h : MixtureAxioms r) {x x' y y' : Z}
    (hx : Indifferent r x x') (hy : Indifferent r y y') (a : Weight) :
    Indifferent r (Mix a x y) (Mix a x' y') := by
  apply proposition_1_9f h.1.2 (lemma_5_8 h hx a y)
  rw [mix_swap a x' y, mix_swap a x' y']
  exact lemma_5_8 h hy _ x'

/-- A preference interval is closed under every mixture. -/
theorem between_mix (h : MixtureAxioms r) {hi lo x y : Z}
    (hx : Between r hi lo x) (hy : Between r hi lo y) (a : Weight) :
    Between r hi lo (Mix a x y) := by
  have hbnd {p q p' q' : Z} (hp : r p p') (hq : r q q') : r (Mix a p q) (Mix a p' q') := by
    apply h.1.2 _ (Mix a p' q) _ (mix_monotone h hp a q)
    rw [mix_swap a p' q, mix_swap a p' q']
    exact mix_monotone h hq _ p'
  exact ⟨by simpa only [mix_self] using hbnd hx.1 hy.1,
    by simpa only [mix_self] using hbnd hx.2 hy.2⟩

/-- Anchor probabilities represent preference throughout the interval. -/
theorem anchorWeight_represents (h : MixtureAxioms r) {hi lo x y : Z} (hs : Strict r hi lo)
    (hx : Between r hi lo x) (hy : Between r hi lo y) :
    r x y ↔ (AnchorWeight r hi lo y).val ≤ (AnchorWeight r hi lo x).val := by
  obtain ⟨hx₁, hx₂⟩ := anchorWeight_indifferent h hx
  obtain ⟨hy₁, hy₂⟩ := anchorWeight_indifferent h hy
  rw [← segment_compare_iff h hs]
  exact ⟨fun hxy => h.1.2 _ y _ (h.1.2 _ x _ hx₂ hxy) hy₁,
    fun hxy => h.1.2 x _ y hx₁ (h.1.2 _ _ y hxy hy₂)⟩

/-- Anchor probabilities are affine for any pair of alternatives in the interval. -/
theorem anchorWeight_affine (h : MixtureAxioms r) {hi lo x y : Z} (hs : Strict r hi lo)
    (hx : Between r hi lo x) (hy : Between r hi lo y) (a : Weight) :
    AnchorWeight r hi lo (Mix a x y) =
      WeightMean a (AnchorWeight r hi lo x) (AnchorWeight r hi lo y) := by
  have he := mix_congr_indifferent h (anchorWeight_indifferent h hx)
    (anchorWeight_indifferent h hy) a
  rw [mix_mix] at he
  exact lemma_5_9_unique h hs (anchorWeight_indifferent h (between_mix h hx hy a)) he

/-- The bounded-anchor case of the mixture-space theorem, with explicit probability utility. -/
theorem representation_with_best_worst (h : MixtureAxioms r) {hi lo : Z} (hs : Strict r hi lo)
    (hb : ∀ z, Between r hi lo z) :
    Represents (fun z => (AnchorWeight r hi lo z).val) r ∧
      AffineInMix (fun z => (AnchorWeight r hi lo z).val) := by
  refine ⟨fun x y => anchorWeight_represents h hs (hb x) (hb y), fun a x y => ?_⟩
  exact congrArg Subtype.val (anchorWeight_affine h hs (hb x) (hb y) a)

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Calibration without global best and worst alternatives

Kreps I, pp. 94–95 and Problem 5.3, p. 118. Normalize two strictly ranked
anchors at one and zero. Alternatives between, above, and below them receive
the three values in the book's construction. Any normalized affine index on
an interval containing the three alternatives must give the same value.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- The three possible calibrations relative to an anchor at one and an anchor at zero. -/
def Calibrates (r : Z → Z → Prop) (g b z : Z) (t : ℝ) : Prop :=
  (∃ a : Weight, Indifferent r z (Mix a g b) ∧ t = a.val) ∨
  (∃ a : Weight, 0 < a.val ∧ Indifferent r g (Mix a z b) ∧ t = 1 / a.val) ∨
  (∃ a : Weight, a.val < 1 ∧ Indifferent r b (Mix a g z) ∧ t = -a.val / (1 - a.val))

/-- Problem 5.3: the three calibration cases exhaust every alternative. -/
theorem exists_calibration (h : MixtureAxioms r) {g b : Z} (hgb : Strict r g b) (z : Z) :
    ∃ t, Calibrates r g b z t := by
  by_cases hg : r g z
  · by_cases hb : r z b
    · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r g b z from ⟨hg, hb⟩)
      exact ⟨a.val, Or.inl ⟨a, ha, rfl⟩⟩
    · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r g z b from
        ⟨hgb.1, (h.1.1 b z).resolve_right hb⟩)
      have hh : a.val < 1 := by
        by_contra! hle
        have he : a = 1 := Subtype.ext (le_antisymm a.property.2 hle)
        rw [he, mix_one] at ha
        exact hgb.2 ha.1
      exact ⟨_, Or.inr (Or.inr ⟨a, hh, ha, rfl⟩)⟩
  · obtain ⟨a, ha⟩ := lemma_5_9 h (show Between r z b g from
      ⟨(h.1.1 z g).resolve_right hg, hgb.1⟩)
    have hh : 0 < a.val := by
      by_contra! hle
      have he : a = 0 := Subtype.ext (le_antisymm hle a.property.1)
      rw [he, mix_zero] at ha
      exact hgb.2 ha.2
    exact ⟨_, Or.inr (Or.inl ⟨a, hh, ha, rfl⟩)⟩

/-- A finite list and the two fixed anchors fit inside a strictly ordered pair of bounds. -/
theorem exists_preference_enclosure {T : Type*} {r : T → T → Prop}
    (hr : Rational r) {g b : T} (hgb : Strict r g b)
    (zs : List T) : ∃ H L, Strict r H L ∧ Between r H L g ∧ Between r H L b ∧
      ∀ z ∈ zs, Between r H L z := by
  induction zs with
  | nil =>
    exact ⟨g, b, hgb, ⟨complete_refl hr.1 _, hgb.1⟩,
      ⟨hgb.1, complete_refl hr.1 _⟩, by simp⟩
  | cons z zs ih =>
    obtain ⟨H, L, hHL, hg, hb, hall⟩ := ih
    obtain ⟨H', hH, hzH⟩ : ∃ H', r H' H ∧ r H' z := by
      rcases hr.1 H z with h | h
      · exact ⟨H, complete_refl hr.1 _, h⟩
      · exact ⟨z, h, complete_refl hr.1 _⟩
    obtain ⟨L', hL, hzL⟩ : ∃ L', r L L' ∧ r z L' := by
      rcases hr.1 z L with h | h
      · exact ⟨L, complete_refl hr.1 _, h⟩
      · exact ⟨z, h, complete_refl hr.1 _⟩
    have hw {w} (h : Between r H L w) : Between r H' L' w :=
      ⟨hr.2 _ _ _ hH h.1, hr.2 _ _ _ h.2 hL⟩
    refine ⟨H', L', strict_weak_trans hr.2 (weak_strict_trans hr.2 hH hHL) hL,
      hw hg, hw hb, ?_⟩
    intro w hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hzH, hzL⟩
    · exact hw (hall w hm)

/-- Representing utility on one interval, normalized at any two strictly ranked interior anchors. -/
theorem normalized_interval_utility (h : MixtureAxioms r) {H L g b : Z}
    (hHL : Strict r H L) (hg : Between r H L g) (hb : Between r H L b)
    (hgb : Strict r g b) :
    ∃ v : Z → ℝ, v g = 1 ∧ v b = 0 ∧
      (∀ x y, Between r H L x → Between r H L y → (r x y ↔ v y ≤ v x)) ∧
      (∀ a x y, Between r H L x → Between r H L y →
        v (Mix a x y) = a.val * v x + (1 - a.val) * v y) := by
  let w := fun z => (AnchorWeight r H L z).val
  have hlt : w b < w g := lt_of_not_ge
    (fun hh => hgb.2 ((anchorWeight_represents h hHL hb hg).mpr hh))
  let d := w g - w b
  have hd : 0 < d := sub_pos.mpr hlt
  refine ⟨fun z => (w z - w b) / d, div_self hd.ne', by simp, ?_, ?_⟩
  · intro x y hx hy
    simp only [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right]
    exact anchorWeight_represents h hHL hx hy
  · intro a x y hx hy
    have he : w (Mix a x y) = a.val * w x + (1 - a.val) * w y :=
      congrArg Subtype.val (anchorWeight_affine h hHL hx hy a)
    dsimp only
    rw [he]
    ring

/-- Each normalized interval utility evaluates the three global calibration cases identically. -/
theorem calibration_eq_local (h : MixtureAxioms r) {H L g b z : Z}
    (hg : Between r H L g) (hb : Between r H L b) (hz : Between r H L z)
    (v : Z → ℝ) (hg' : v g = 1) (hb' : v b = 0)
    (hv : ∀ x y, Between r H L x → Between r H L y → (r x y ↔ v y ≤ v x))
    (ha : ∀ a x y, Between r H L x → Between r H L y →
      v (Mix a x y) = a.val * v x + (1 - a.val) * v y)
    {t : ℝ} (ht : Calibrates r g b z t) : t = v z := by
  have hind {x y} (hx : Between r H L x) (hy : Between r H L y) (hxy : Indifferent r x y) :
      v x = v y := le_antisymm ((hv y x hy hx).mp hxy.2) ((hv x y hx hy).mp hxy.1)
  rcases ht with ⟨a, hi, rfl⟩ | ⟨a, hp, hi, rfl⟩ | ⟨a, hp, hi, rfl⟩
  · have he := hind hz (between_mix h hg hb a) hi
    rw [ha a g b hg hb, hg', hb'] at he
    linarith
  · have he := hind hg (between_mix h hz hb a) hi
    rw [ha a z b hz hb, hg', hb'] at he
    apply (div_eq_iff hp.ne').mpr
    linarith only [he]
  · have he := hind hb (between_mix h hg hz a) hi
    rw [ha a g z hg hz, hg', hb'] at he
    apply (div_eq_iff (sub_pos.mpr hp).ne').mpr
    linarith only [he]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Recovering a prize index from an affine lottery index

Kreps I, Proposition 5.3, pp. 95–96. Agreement on sure prizes extends to the
entire simplex. Mathlib proves closure under finite convex combinations from
binary closure by splitting off one positively weighted prize and normalizing
the remaining lottery, as in the source's support induction.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

/-- Any binary-mixture affine index has the expected-utility form on every simple lottery. -/
theorem affineInMix_eq_expectedUtility {X : Type*} {u : SimpleLottery X → ℝ}
    (hu : AffineInMix u) (p : SimpleLottery X) :
    u p = ExpectedUtility (fun x => u (PureLottery x)) p := by
  let U : X → ℝ := fun x => u (PureLottery x)
  let s : Set (SimpleLottery X) := {q | u q = ExpectedUtility U q}
  have hs : IsConvexSet ℝ s := by
    apply IsConvexSet.of_convexCombPair_mem
    intro a b ha hb hab x hx y hy
    have he : b = 1 - a := by linarith
    subst b
    let t : Weight := ⟨a, ha, by linarith⟩
    change u (Mix t x y) = ExpectedUtility U (Mix t x y)
    rw [hu, expectedUtility_affine, show u x = ExpectedUtility U x from hx,
      show u y = ExpectedUtility U y from hy]
  have hp : p.iConvexComb (fun x => PureLottery x) ∈ s := by
    apply hs.iConvexComb_mem
    intro x _
    exact (expectedUtility_pure U x).symm
  change p ∈ s
  simpa only [PureLottery, StdSimplex.iConvexComb_single] using hp

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The mixture-space and expected-utility theorems

Kreps I, Propositions 5.3–5.4 and Problem 5.3, pp. 88–96, 118. Normalize two
strictly ranked anchors. For each pair of alternatives, one bounded preference
interval contains the pair, its mixtures, and the anchors. Its normalized local
utility agrees with each globally calibrated value, proving representation and
affinity even when preferences have no best or worst alternative.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity Filter Topology

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Problem 5.3: constructing affine utility without a best or a worst alternative. -/
theorem problem_5_3 (h : MixtureAxioms r) :
    ∃ u : Z → ℝ, Represents u r ∧ AffineInMix u := by
  classical
  by_cases hex : ∃ g b, Strict r g b
  · obtain ⟨g, b, hgb⟩ := hex
    choose u hu using exists_calibration h hgb
    have pair (x y : Z) : (r x y ↔ u y ≤ u x) ∧
        ∀ a : Weight, u (Mix a x y) = a.val * u x + (1 - a.val) * u y := by
      obtain ⟨H, L, hHL, hg, hb, hall⟩ := exists_preference_enclosure h.1 hgb [x, y]
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      obtain ⟨v, hvg, hvb, hv, ha⟩ := normalized_interval_utility h hHL hg hb hgb
      have he (z : Z) (hz : Between r H L z) : u z = v z :=
        calibration_eq_local h hg hb hz v hvg hvb hv ha (hu z)
      refine ⟨by rw [he x hx, he y hy]; exact hv x y hx hy, ?_⟩
      intro a
      rw [he _ (between_mix h hx hy a), he x hx, he y hy, ha a x y hx hy]
    exact ⟨u, fun x y => (pair x y).1, fun a x y => (pair x y).2 a⟩
  · refine ⟨fun _ => 0, fun x y => ?_, by intro a x y; simp⟩
    apply iff_of_true _ le_rfl
    by_contra hn
    exact hex ⟨y, x, (proposition_1_9a h.1.1 _ _).mpr hn⟩

/-- Any affine representation satisfies the exact primitive substitution and continuity axioms. -/
theorem mixtureAxioms_of_representation {u : Z → ℝ} (hu : Represents u r)
    (ha : AffineInMix u) : MixtureAxioms r := by
  have hs (x y : Z) : Strict r x y ↔ u y < u x := by
    rw [Strict, hu x y, hu y x, not_le]
    exact ⟨And.right, fun hh => ⟨hh.le, hh⟩⟩
  refine ⟨⟨fun x y => (le_total (u y) (u x)).imp (hu x y).mpr (hu y x).mpr,
    fun x y z hxy hyz => (hu x z).mpr (((hu y z).mp hyz).trans ((hu x y).mp hxy))⟩,
    ?_, ?_⟩
  · intro a x y z w
    simp only [hs, ha a y z, ha a x z, ha a y w, ha a x w, add_lt_add_iff_right]
  · intro x y hxy z
    have hg := (hs x y).mp hxy
    have hne : ∀ᶠ a : ℝ in 𝓝 1,
        u y < a * u x + (1 - a) * u z ∧ a * u y + (1 - a) * u z < u x := by
      apply Filter.Eventually.and
      · apply (isOpen_lt continuous_const (by fun_prop)).mem_nhds
        simpa using hg
      · apply (isOpen_lt (by fun_prop) continuous_const).mem_nhds
        simpa using hg
    obtain ⟨l, b, ⟨hl, hb⟩, hh⟩ := hne.exists_Ioo_subset
    let c := (max l 0 + 1) / 2
    have hm : max l 0 < 1 := max_lt hl zero_lt_one
    have hc₀ : 0 < c := by dsimp [c]; linarith [le_max_right l 0]
    have hc₁ : c < 1 := by dsimp [c]; linarith
    refine ⟨c, ⟨hc₀, hc₁⟩, fun a hca => ?_⟩
    have hla : l < a.val := by dsimp [c] at hca; linarith [le_max_left l 0]
    simp only [hs, ha a x z, ha a y z]
    exact hh (show a.val ∈ Set.Ioo l b from ⟨hla, a.property.2.trans_lt hb⟩)

/-- **Proposition 5.4:** complete primitive characterization on a general mixture space. -/
theorem proposition_5_4 : MixtureAxioms r ↔ ∃ u : Z → ℝ, Represents u r ∧ AffineInMix u :=
  ⟨problem_5_3, fun ⟨_, hu, ha⟩ => mixtureAxioms_of_representation hu ha⟩

/-- **Proposition 5.3:** expected utility on all simple lotteries over an arbitrary prize type. -/
theorem proposition_5_3 {X : Type*} {p : SimpleLottery X → SimpleLottery X → Prop} :
    MixtureAxioms p ↔ ∃ U : X → ℝ, Represents (ExpectedUtility U) p := by
  constructor
  · intro h
    obtain ⟨u, hu, ha⟩ := proposition_5_4.mp h
    refine ⟨fun x => u (PureLottery x), fun x y => ?_⟩
    rw [← affineInMix_eq_expectedUtility ha x, ← affineInMix_eq_expectedUtility ha y]
    exact hu x y
  · rintro ⟨U, hu⟩
    exact mixtureAxioms_of_representation hu (expectedUtility_affine U)

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strict independence and the Archimedean mixture axiom

Kreps I, Proposition 5.11, pp. 100–101. This module derives the original
endpoint continuity condition from the alternative strict-independence and
intermediate-mixture conditions. The proof uses both directions of the
reference order and covers mixtures of tied endpoints.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Proposition 5.11(b′): every interior common-background mixture preserves strict preference. -/
def StrictIndependence (r : Z → Z → Prop) : Prop :=
  ∀ x y, Strict r x y → ∀ (a : Weight), 0 < a.val → a.val < 1 → ∀ z,
    Strict r (Mix a x z) (Mix a y z)

/-- Proposition 5.11(c′): a strictly intermediate alternative lies between two interior mixtures. -/
def ArchimedeanMix (r : Z → Z → Prop) : Prop :=
  ∀ x y z, Strict r x y → Strict r y z → ∃ (a b : Weight),
    (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
    Strict r (Mix a x z) y ∧ Strict r y (Mix b x z)

/-- Complementary probabilities exchange the two outcomes. -/
theorem mix_complement (a : Weight) (x y : Z) : Mix (Complement a) y x = Mix a x y :=
  (mix_swap a x y).symm

/-- Reversal preserves the strict triple axiom, with complementary probabilities. -/
theorem archimedeanMix_reverse (hc : ArchimedeanMix r) :
    ArchimedeanMix (fun x y => r y x) := by
  intro x y z hxy hyz
  obtain ⟨a, b, ha, hb, h₁, h₂⟩ := hc z y x hyz hxy
  refine ⟨Complement b, Complement a, ?_, ?_, ?_, ?_⟩
  · exact ⟨sub_pos.mpr hb.2, sub_lt_self _ hb.1⟩
  · exact ⟨sub_pos.mpr ha.2, sub_lt_self _ ha.1⟩
  · rwa [mix_complement]
  · rwa [mix_complement]

/-- Strict improvements in both components strictly improve an interior mixture. -/
theorem mix_strict_both (hr : Rational r) (hb : StrictIndependence r)
    {x x' y y' : Z} (hx : Strict r x x') (hy : Strict r y y')
    (a : Weight) (h₀ : 0 < a.val) (h₁ : a.val < 1) :
    Strict r (Mix a x y) (Mix a x' y') := by
  apply proposition_1_9h hr.2 _ (Mix a x' y) _ (hb x x' hx a h₀ h₁ y)
  rw [mix_swap a x' y, mix_swap a x' y']
  exact hb y y' hy _ (sub_pos.mpr h₁) (sub_lt_self _ h₀) x'

/-- Strict independence alone puts mixtures between weakly ordered endpoints. -/
theorem alt_segment_bounds (hr : Rational r) (hb : StrictIndependence r)
    {x y : Z} (hxy : r x y) (a : Weight) : r x (Mix a x y) ∧ r (Mix a x y) y := by
  by_cases h₀ : a.val = 0
  · rw [show a = 0 from Subtype.ext h₀, mix_zero]
    exact ⟨hxy, complete_refl hr.1 _⟩
  by_cases h₁ : a.val = 1
  · rw [show a = 1 from Subtype.ext h₁, mix_one]
    exact ⟨complete_refl hr.1 _, hxy⟩
  have hp := lt_of_le_of_ne a.property.1 (Ne.symm h₀)
  have hl := lt_of_le_of_ne a.property.2 h₁
  constructor
  · by_contra hn
    have hs := (proposition_1_9a hr.1 _ _).mpr hn
    have bad := mix_strict_both hr hb hs (strict_weak_trans hr.2 hs hxy) a hp hl
    rw [mix_self] at bad
    exact bad.2 bad.1
  · by_contra hn
    have hs := (proposition_1_9a hr.1 _ _).mpr hn
    have bad := mix_strict_both hr hb (weak_strict_trans hr.2 hxy hs) hs a hp hl
    rw [mix_self] at bad
    exact bad.2 bad.1

/-- Reducing the probability of the first endpoint multiplies its two weights. -/
theorem mix_toward_baseline (a t s : Weight) (he : a.val * t.val = s.val) (x y : Z) :
    Mix a (Mix t x y) y = Mix s x y := by
  calc
    _ = Mix a (Mix t x y) (Mix 0 x y) := by rw [mix_zero]
    _ = Mix (WeightMean a t 0) x y := mix_mix ..
    _ = _ := by
      apply congrArg (fun v => Mix v x y)
      apply Subtype.ext
      simpa [WeightMean] using he

/-- Ordered endpoints give weak monotonicity in the probability under strict independence. -/
theorem alt_segment_mono (hr : Rational r) (hb : StrictIndependence r) {x y : Z}
    (hxy : r x y) (s t : Weight) (hst : s.val ≤ t.val) : r (Mix t x y) (Mix s x y) := by
  by_cases h₀ : t.val = 0
  · have he : s = t := Subtype.ext (le_antisymm hst (h₀ ▸ s.property.1))
    rw [he]
    exact complete_refl hr.1 _
  have hp := lt_of_le_of_ne t.property.1 (Ne.symm h₀)
  let a : Weight := ⟨s.val / t.val, div_nonneg s.property.1 hp.le, (div_le_one hp).mpr hst⟩
  have he := mix_toward_baseline a t s (div_mul_cancel₀ _ hp.ne') x y
  exact he ▸ (alt_segment_bounds hr hb (alt_segment_bounds hr hb hxy t).2 a).1

/-- Some threshold makes mixtures near the better outcome strictly better than the lower one. -/
theorem alt_near_better (hr : Rational r) (hb : StrictIndependence r) (hc : ArchimedeanMix r)
    {x y : Z} (hxy : Strict r x y) (z : Z) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ a : Weight, c < a.val → Strict r (Mix a x z) y := by
  by_cases hzx : r z x
  · refine ⟨1 / 2, by constructor <;> norm_num, fun a _ => ?_⟩
    rw [mix_swap]
    exact weak_strict_trans hr.2 (alt_segment_bounds hr hb hzx _).2 hxy
  have hxz := (proposition_1_9a hr.1 _ _).mpr hzx
  by_cases hzy : r z y
  · refine ⟨1 / 2, by constructor <;> norm_num, fun a ha => ?_⟩
    by_cases he : a.val = 1
    · rwa [show a = 1 from Subtype.ext he, mix_one]
    have hp := hb x z hxz a (by linarith) (lt_of_le_of_ne a.property.2 he) z
    rw [mix_self] at hp
    exact strict_weak_trans hr.2 hp hzy
  · obtain ⟨a, _, ha, _, hs, _⟩ := hc x y z hxy ((proposition_1_9a hr.1 _ _).mpr hzy)
    exact ⟨a.val, ha, fun d hd => weak_strict_trans hr.2
      (alt_segment_mono hr hb hxz.1 a d hd.le) hs⟩

/-- The two-sided endpoint condition follows from the alternative axioms. -/
theorem alt_mixtureContinuous (hr : Rational r) (hb : StrictIndependence r)
    (hc : ArchimedeanMix r) : MixtureContinuous r := by
  intro x y hxy z
  obtain ⟨l, hl, h₁⟩ := alt_near_better hr hb hc hxy z
  have hr' : Rational (fun x y => r y x) :=
    ⟨fun a b => (hr.1 b a), fun a b c h₁ h₂ => hr.2 c b a h₂ h₁⟩
  have hb' : StrictIndependence (fun x y => r y x) :=
    fun a b hh t hp hl w => hb b a hh t hp hl w
  obtain ⟨m, hm, h₂⟩ := alt_near_better hr' hb' (archimedeanMix_reverse hc)
    (show Strict (fun x y => r y x) y x from hxy) z
  exact ⟨max l m, ⟨hl.1.trans_le (le_max_left _ _), max_lt hl.2 hm.2⟩,
    fun a ha => ⟨h₁ a ((le_max_left _ _).trans_lt ha), h₂ a ((le_max_right _ _).trans_lt ha)⟩⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equivalence of the two mixture axiom systems

Kreps I, Proposition 5.11, pp. 100–101. A small move toward the common
background strictly improves or worsens a tied endpoint when that background
has a different rank. Endpoint continuity then prevents any strict comparison
between mixtures of initially tied alternatives.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Nested mixtures with the same baseline commute in the two weights. -/
theorem mix_shared_baseline_comm (a t : Weight) (x z : Z) :
    Mix t (Mix a x z) z = Mix a (Mix t x z) z := by
  let w : Weight := ⟨t.val * a.val, mul_nonneg t.property.1 a.property.1,
    (mul_le_mul_of_nonneg_left a.property.2 t.property.1).trans (by simpa using t.property.2)⟩
  exact (mix_toward_baseline t a w rfl x z).trans
    (mix_toward_baseline a t w (mul_comm _ _) x z).symm

/-- Strict independence and endpoint continuity preserve ties under common mixtures. -/
theorem alt_no_strict_of_indifferent (hr : Rational r) (hb : StrictIndependence r)
    (hc : MixtureContinuous r) {x y : Z} (he : Indifferent r x y)
    (a : Weight) (ha₀ : 0 < a.val) (ha₁ : a.val < 1) (z : Z) :
    ¬Strict r (Mix a x z) (Mix a y z) := by
  intro hs
  obtain ⟨c, hc', ht⟩ := hc _ _ hs z
  let t : Weight := ⟨(c + 1) / 2, by constructor <;> linarith [hc'.1, hc'.2]⟩
  have hct : c < t.val := by dsimp [t]; linarith [hc'.2]
  have ht₀ : 0 < (Complement t).val := by dsimp [Complement, t]; linarith [hc'.2]
  have ht₁ : (Complement t).val < 1 := by dsimp [Complement, t]; linarith [hc'.1]
  obtain ⟨hleft, hright⟩ := ht t hct
  rw [mix_shared_baseline_comm] at hleft hright
  by_cases hxz : r x z
  · by_cases hzx : r z x
    · have hyz := hr.2 y x z he.2 hxz
      exact hs.2 (hr.2 _ z _ (alt_segment_bounds hr hb hyz a).2
        (hr.2 z x _ hzx (alt_segment_bounds hr hb hxz a).1))
    · have hx := (proposition_1_9a hr.1 _ _).mpr hzx
      have hd := hb x z hx (Complement t) ht₀ ht₁ x
      rw [mix_self, mix_complement] at hd
      exact hleft.2 (hb y _ (weak_strict_trans hr.2 he.2 hd) a ha₀ ha₁ z).1
  · have hzy := strict_weak_trans hr.2 ((proposition_1_9a hr.1 _ _).mpr hxz) he.1
    have hd := hb z y hzy (Complement t) ht₀ ht₁ y
    rw [mix_complement, mix_self] at hd
    exact hright.2 (hb _ x (strict_weak_trans hr.2 hd he.2) a ha₀ ha₁ z).1

/-- At each interior weight, strict comparisons in a common mixture reflect the input ranking. -/
theorem alt_mix_strict_iff (hr : Rational r) (hb : StrictIndependence r)
    (hc : MixtureContinuous r) (a : Weight) (ha₀ : 0 < a.val) (ha₁ : a.val < 1)
    (x y z : Z) : Strict r (Mix a x z) (Mix a y z) ↔ Strict r x y := by
  refine ⟨fun hs => ?_, fun hh => hb x y hh a ha₀ ha₁ z⟩
  apply (proposition_1_9a hr.1 _ _).mpr
  intro hyx
  by_cases hxy : r x y
  · exact alt_no_strict_of_indifferent hr hb hc ⟨hxy, hyx⟩ a ha₀ ha₁ z hs
  · exact hs.2 (hb y x ⟨hyx, hxy⟩ a ha₀ ha₁ z).1

/-- **Proposition 5.11:** the alternative pair of axioms is equivalent to the original pair. -/
theorem proposition_5_11 (hr : Rational r) :
    (BackgroundIndependent r ∧ MixtureContinuous r) ↔ StrictIndependence r ∧ ArchimedeanMix r := by
  constructor
  · rintro ⟨hb, hc⟩
    have h : MixtureAxioms r := ⟨hr, hb, hc⟩
    refine ⟨fun _ _ hxy a hp _ z => mix_strict h hxy a hp z, ?_⟩
    intro x y z hxy hyz
    obtain ⟨l, hl, h₁⟩ := hc x y hxy z
    obtain ⟨m, hm, h₂⟩ := hc y z hyz x
    let a : Weight := ⟨(l + 1) / 2, by constructor <;> linarith [hl.1, hl.2]⟩
    let b : Weight := ⟨(m + 1) / 2, by constructor <;> linarith [hm.1, hm.2]⟩
    refine ⟨a, Complement b, ?_, ?_, (h₁ a (by dsimp [a]; linarith [hl.2])).1, ?_⟩
    · dsimp [a]
      constructor <;> linarith [hl.1, hl.2]
    · dsimp [b, Complement]
      constructor <;> linarith [hm.1, hm.2]
    · rw [mix_complement]
      exact (h₂ b (by dsimp [b]; linarith [hm.2])).2
  · rintro ⟨hb, hc⟩
    have hc' := alt_mixtureContinuous hr hb hc
    refine ⟨?_, hc'⟩
    intro a x y z w
    by_cases h0 : a.val = 0
    · rw [show a = 0 from Subtype.ext h0, mix_zero, mix_zero, mix_zero, mix_zero]
      simp [Strict]
    by_cases h1 : a.val = 1
    · rw [show a = 1 from Subtype.ext h1, mix_one, mix_one, mix_one, mix_one]
    have hp := lt_of_le_of_ne a.property.1 (Ne.symm h0)
    have hl := lt_of_le_of_ne a.property.2 h1
    exact (alt_mix_strict_iff hr hb hc' a hp hl x y z).trans
      (alt_mix_strict_iff hr hb hc' a hp hl x y w).symm

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local comparisons and uniqueness of additive state utilities

Kreps I, pp. 104–108. Comparing acts that differ only in state `s` isolates that
state's utility difference. This identifies the state-specific additive constants
and gives the local comparison used to recover subjective probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- When acts agree off one state, their total utility difference is local to that state. -/
theorem stateAdditiveValue_difference (U : S → X → ℝ) (s : S) (h g : StateAct S X)
    (he : ∀ t, t ≠ s → h t = g t) :
    StateAdditiveValue U h - StateAdditiveValue U g = U s (h s) - U s (g s) := by
  classical
  simp only [StateAdditiveValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single s
  · intro t _ ht
    rw [he t ht, sub_self]
  · simp

/-- Representing rankings on acts by a sum identifies every one-state comparison. -/
theorem stateAdditive_local_comparison (U : S → X → ℝ) {r : StateAct S X → StateAct S X → Prop}
    (hU : ∀ h g, r h g ↔ StateAdditiveValue U g ≤ StateAdditiveValue U h)
    (s : S) (h g : StateAct S X) (he : ∀ t, t ≠ s → h t = g t) :
    r h g ↔ U s (g s) ≤ U s (h s) := by
  rw [hU]
  have hd := stateAdditiveValue_difference U s h g he
  constructor <;> intro hr <;> linarith

/-- A common affine scale for total utilities fixes the differences in every state. -/
theorem stateUtility_difference_of_affine (U V : S → X → ℝ) (A B : ℝ)
    (ha : ∀ h, StateAdditiveValue V h = A * StateAdditiveValue U h + B)
    (s : S) (x y : X) : V s x - V s y = A * (U s x - U s y) := by
  classical
  let g : StateAct S X := fun _ => y
  let h := Function.update g s x
  have he : ∀ t, t ≠ s → h t = g t := fun t ht => Function.update_of_ne ht x g
  have hu := stateAdditiveValue_difference U s h g he
  have hv := stateAdditiveValue_difference V s h g he
  rw [ha h, ha g] at hv
  simp only [h, g, Function.update_self] at hu hv
  rw [← hu]
  linarith

/-- Proposition 5.12's uniqueness formula, including the sum of the state shifts. -/
theorem stateUtility_shifts_of_affine (U V : S → X → ℝ) (A B : ℝ)
    (ha : ∀ h, StateAdditiveValue V h = A * StateAdditiveValue U h + B) (base : X) :
    ∃ b : S → ℝ, (∀ s x, V s x = A * U s x + b s) ∧ ∑ s, b s = B := by
  refine ⟨fun s => V s base - A * U s base, ?_, ?_⟩
  · intro s x
    have hd := stateUtility_difference_of_affine U V A B ha s x base
    linarith
  · have hc := ha (fun _ => base)
    simp only [StateAdditiveValue] at hc
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith

/-- Condition (f) of Proposition 5.13 compares each one-state change to constant acts. -/
def StateIndependentComparisons (r : StateAct S X → StateAct S X → Prop) : Prop :=
  ∀ (s : S) (h g : StateAct S X), (∀ t, t ≠ s → h t = g t) →
    (r (fun _ => h s) (fun _ => g s) ↔ r h g)

/-- A strictly positive probability vector makes local and constant comparisons agree. -/
theorem subjectiveActValue_stateIndependent (p : S → ℝ) (hp : ∀ s, 0 < p s)
    (hp₁ : ∑ s, p s = 1) (U : X → ℝ)
    {r : StateAct S X → StateAct S X → Prop}
    (hr : ∀ h g, r h g ↔ SubjectiveActValue p U g ≤ SubjectiveActValue p U h) :
    StateIndependentComparisons r := by
  intro s h g he
  have hs := stateAdditive_local_comparison (fun t x => p t * U x) hr s h g he
  rw [hr, hs]
  simp only [SubjectiveActValue, ← Finset.sum_mul, hp₁, one_mul]
  exact (mul_le_mul_iff_right₀ (hp s)).symm

/-- Constant acts recover the unweighted outcome utility for any normalized prior. -/
theorem subjectiveActValue_constant (p : S → ℝ) (hp : ∑ s, p s = 1) (U : X → ℝ) (x : X) :
    SubjectiveActValue p U (fun _ => x) = U x := by
  simp only [SubjectiveActValue, ← Finset.sum_mul, hp, one_mul]

/-- Nonconstant prizes identify the state probabilities from affine-equivalent total values. -/
theorem subjectiveProbabilities_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) (A B : ℝ) (hA : 0 < A)
    (ha : ∀ h, SubjectiveActValue q V h = A * SubjectiveActValue p U h + B)
    {x y : X} (hne : U x ≠ U y) : q = p := by
  have hconst (z : X) : V z = A * U z + B := by
    simpa only [subjectiveActValue_constant q hq, subjectiveActValue_constant p hp] using
      ha (fun _ => z)
  funext s
  have hd := stateUtility_difference_of_affine (fun t z => p t * U z)
    (fun t z => q t * V z) A B ha s x y
  rw [hconst x, hconst y] at hd
  have hn : A * (U x - U y) ≠ 0 := mul_ne_zero hA.ne' (sub_ne_zero.mpr hne)
  apply (mul_left_inj' hn).mp
  linarith only [hd]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Horse lotteries and state-dependent expected utility

Kreps I, Proposition 5.12, pp. 102–105. Every state delivers a simple roulette
lottery on the common prize space. An affine utility on horse lotteries is the
sum of state-specific expected utilities after subtracting its reference value.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity

variable {S X Z : Type*}

/-- A horse lottery specifies a roulette lottery for every possible state. -/
abbrev HorseLottery (S X : Type*) := S → SimpleLottery X

/-- Mixtures of acts operate separately in every state. -/
theorem mix_act_apply [ConvexSpace ℝ Z] (a : Weight) (h g : S → Z) (s : S) :
    Mix a h g s = Mix a (h s) (g s) := by simp [Mix]

/-- Equation (5.6), the sum over states of their expected prize utilities. -/
noncomputable def HorseValue [Fintype S] (U : S → X → ℝ) (h : HorseLottery S X) : ℝ :=
  StateAdditiveValue (fun s => ExpectedUtility (U s)) h

/-- State-dependent expected utility is affine on lotteries over acts. -/
theorem horseValue_affine [Fintype S] (U : S → X → ℝ) : AffineInMix (HorseValue U) := by
  intro a h g
  simp only [HorseValue, StateAdditiveValue, mix_act_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => expectedUtility_affine (U s) a (h s) (g s)

/-- A single-state contribution of an affine utility is affine on roulette lotteries. -/
theorem stateIncrement_affine [DecidableEq S] [ConvexSpace ℝ Z] {u : (S → Z) → ℝ}
    (hu : AffineInMix u) (base : S → Z) (s : S) : AffineInMix (StateIncrement u base s) := by
  intro a x y
  have he : Function.update base s (Mix a x y) =
      Mix a (Function.update base s x) (Function.update base s y) := by
    funext t
    rw [mix_act_apply]
    by_cases h : t = s
    · subst t
      simp
    · simp [Function.update_of_ne h, mix_self]
  simp only [StateIncrement, he]
  rw [hu]
  ring

/-- An affine index, normalized to zero at a reference act, has the state-additive EU form. -/
theorem horseValue_of_affine [Fintype S] [DecidableEq S] {u : HorseLottery S X → ℝ}
    (hu : AffineInMix u) (base h : HorseLottery S X) :
    u h - u base = HorseValue (fun s x => StateIncrement u base s (PureLottery x)) h := by
  let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
  have hsym (x y : SimpleLottery X) : Mix a x y = Mix a y x := by
    have he : Complement a = a := by ext; norm_num [a, Complement]
    rw [mix_swap a x y, he]
  have hmid (f g : HorseLottery S X) :
      2 * u (fun s => Mix a (f s) (g s)) = u f + u g := by
    have he : (fun s => Mix a (f s) (g s)) = Mix a f g :=
      funext fun s => (mix_act_apply a f g s).symm
    rw [he, hu]
    dsimp [a]
    ring
  rw [stateAct_decomposition (Mix a) hsym u hmid base h]
  unfold HorseValue StateAdditiveValue
  exact Finset.sum_congr rfl fun s _ => affineInMix_eq_expectedUtility
    (stateIncrement_affine hu base s) (h s)

/-- The state utilities can be recovered from any affine representation, including empty domains. -/
theorem horseRepresentation_of_affine [Fintype S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {u : HorseLottery S X → ℝ}
    (hur : Represents u r) (hu : AffineInMix u) : ∃ U : S → X → ℝ, Represents (HorseValue U) r := by
  classical
  cases isEmpty_or_nonempty (HorseLottery S X) with
  | inl he => exact ⟨fun _ _ => 0, fun h _ => isEmptyElim h⟩
  | inr he =>
    obtain ⟨base⟩ := he
    refine ⟨fun s x => StateIncrement u base s (PureLottery x), fun h g => ?_⟩
    rw [hur, ← horseValue_of_affine hu base h, ← horseValue_of_affine hu base g]
    exact (sub_le_sub_iff_right _).symm

/-- The uniqueness part of Proposition 5.12 gives one scale and one intercept per state. -/
theorem proposition_5_12_unique [Fintype S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {U V : S → X → ℝ}
    (hU : Represents (HorseValue U) r) (hV : Represents (HorseValue V) r) :
    ∃ A > 0, ∃ B : ℝ, ∃ b : S → ℝ, (∀ h, HorseValue V h = A * HorseValue U h + B) ∧
      (∀ s x, V s x = A * U s x + b s) ∧ ∑ s, b s = B := by
  cases isEmpty_or_nonempty X with
  | inl he =>
    have huv : V = U := by ext s x; exact isEmptyElim x
    subst V
    exact ⟨1, zero_lt_one, 0, fun _ => 0, by simp, fun s x => isEmptyElim x, by simp⟩
  | inr he =>
    obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
      (horseValue_affine U) (horseValue_affine V)
    have hdet (h : StateAct S X) : StateAdditiveValue V h = A * StateAdditiveValue U h + B := by
      simpa only [HorseValue, StateAdditiveValue, expectedUtility_pure] using
        ha (fun s => PureLottery (h s))
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨b, hb, hs⟩ := stateUtility_shifts_of_affine U V A B hdet x
    exact ⟨A, hA, B, b, ha, hb, hs⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Subjective probabilities and state-independent prize utility

Kreps I, Proposition 5.13, pp. 106–108. The comparison of constant acts with
single-state changes forces all state utilities onto a common positive affine scale.
Normalizing these scales gives a strictly positive probability distribution on a
nonempty finite state space. Nonconstant utility identifies its probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- Probability mass one makes expectation commute with affine changes of prize units. -/
theorem expectedUtility_affine_transform (U : X → ℝ) (A B : ℝ) (q : SimpleLottery X) :
    ExpectedUtility (fun x => A * U x + B) q = A * ExpectedUtility U q + B := by
  classical
  have ht : ∑ x ∈ q.weights.support, q.weights x = 1 := q.total
  unfold ExpectedUtility Finsupp.sum
  calc
    _ = ∑ x ∈ q.weights.support, (A * (q.weights x * U x) + q.weights x * B) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ht, one_mul]

/-- Equation (5.8), subjective expectation over states of objective roulette expectations. -/
noncomputable def SubjectiveHorseValue (p : S → ℝ) (U : X → ℝ) (h : HorseLottery S X) : ℝ :=
  SubjectiveActValue p (ExpectedUtility U) h

/-- The subjective index is the state-dependent index with prize utility scaled by probability. -/
theorem subjectiveHorseValue_eq_horseValue (p : S → ℝ) (U : X → ℝ) :
    SubjectiveHorseValue p U = HorseValue (fun s x => p s * U x) := by
  funext h
  apply Finset.sum_congr rfl
  intro s _
  simpa only [add_zero] using (expectedUtility_affine_transform U (p s) 0 (h s)).symm

/-- Subjective expected utility is affine under objective mixtures of acts. -/
theorem subjectiveHorseValue_affine (p : S → ℝ) (U : X → ℝ) :
    AffineInMix (SubjectiveHorseValue p U) := by
  rw [subjectiveHorseValue_eq_horseValue]
  exact horseValue_affine _

/-- Under condition (f), each state's expected utility represents the ranking of constant acts. -/
theorem constantActs_represented_in_each_state {r : HorseLottery S X → HorseLottery S X → Prop}
    {U : S → X → ℝ} (hr : Represents (HorseValue U) r) (hi : StateIndependentComparisons r)
    (s : S) : Represents (ExpectedUtility (U s)) (fun x y => r (fun _ => x) (fun _ => y)) := by
  classical
  intro x y
  let g : HorseLottery S X := fun _ => y
  let h : HorseLottery S X := Function.update g s x
  have he : ∀ t, t ≠ s → h t = g t := fun _ ht => Function.update_of_ne ht x g
  have hc := (hi s h g he).trans (stateAdditive_local_comparison
    (fun t => ExpectedUtility (U t)) hr s h g he)
  simpa only [h, g, Function.update_self] using hc

/-- The source's normalization of state-specific utility scales into subjective probabilities. -/
theorem subjectiveRepresentation_of_stateIndependent [Nonempty S]
    {r : HorseLottery S X → HorseLottery S X → Prop} {V : S → X → ℝ}
    (hr : Represents (HorseValue V) r) (hi : StateIndependentComparisons r) :
    ∃ (p : S → ℝ) (U : X → ℝ), (∀ s, 0 < p s) ∧ ∑ s, p s = 1 ∧
      Represents (SubjectiveHorseValue p U) r := by
  classical
  let t : S := Classical.arbitrary S
  have hrat (s : S) := constantActs_represented_in_each_state hr hi s
  choose a ha b hab using fun s => proposition_5_4_unique (hrat t) (hrat s)
    (expectedUtility_affine (V t)) (expectedUtility_affine (V s))
  let N := ∑ s, a s
  have hN : 0 < N := Finset.sum_pos (fun s _ => ha s) Finset.univ_nonempty
  let p : S → ℝ := fun s => a s / N
  let U : X → ℝ := fun x => N * V t x
  have hv (h : HorseLottery S X) :
      HorseValue V h = SubjectiveHorseValue p U h + ∑ s, b s := by
    unfold HorseValue StateAdditiveValue SubjectiveHorseValue SubjectiveActValue
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    have he : ExpectedUtility U (h s) = N * ExpectedUtility (V t) (h s) := by
      simpa only [add_zero, U] using expectedUtility_affine_transform (V t) N 0 (h s)
    change ExpectedUtility (V s) (h s) = p s * ExpectedUtility U (h s) + b s
    rw [hab s, he]
    dsimp only [p]
    field_simp [hN.ne']
  refine ⟨p, U, fun s => div_pos (ha s) hN, ?_, fun h g => ?_⟩
  · change ∑ s, a s / N = 1
    rw [← Finset.sum_div, div_self hN.ne']
  · rw [hr, hv, hv]
    exact add_le_add_iff_right _

/-- Two subjective representations have positive affine-equivalent prize indices. -/
theorem subjective_prize_utility_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) {r : HorseLottery S X → HorseLottery S X → Prop}
    (hU : Represents (SubjectiveHorseValue p U) r) (hV : Represents (SubjectiveHorseValue q V) r) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, V x = A * U x + B := by
  obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
    (subjectiveHorseValue_affine p U) (subjectiveHorseValue_affine q V)
  refine ⟨A, hA, B, fun x => ?_⟩
  simpa only [SubjectiveHorseValue, subjectiveActValue_constant _ hp,
    subjectiveActValue_constant _ hq, expectedUtility_pure] using ha (fun _ => PureLottery x)

/-- Nonconstant prize utility identifies the probabilities, even when some outcomes are tied. -/
theorem subjective_probabilities_unique (p q : S → ℝ) (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (U V : X → ℝ) {r : HorseLottery S X → HorseLottery S X → Prop}
    (hU : Represents (SubjectiveHorseValue p U) r) (hV : Represents (SubjectiveHorseValue q V) r)
    {x y : X} (hne : U x ≠ U y) : q = p := by
  obtain ⟨A, hA, B, ha⟩ := proposition_5_4_unique hU hV
    (subjectiveHorseValue_affine p U) (subjectiveHorseValue_affine q V)
  apply subjectiveProbabilities_unique p q hp hq (ExpectedUtility U) (ExpectedUtility V) A B hA ha
    (x := PureLottery x) (y := PureLottery y)
  simpa only [expectedUtility_pure] using hne

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two Anscombe–Aumann representations

Kreps I, Propositions 5.12 and 5.13, pp. 102–108. The mixture axioms give a
state-additive expected utility. Adding comparisons of constant and single-state
acts gives a common prize utility and strictly positive subjective probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S] {r : HorseLottery S X → HorseLottery S X → Prop}

/-- Proposition 5.12. The primitive axioms are equivalent to state-additive expected utility. -/
theorem proposition_5_12 : MixtureAxioms r ↔ ∃ U : S → X → ℝ, Represents (HorseValue U) r := by
  constructor
  · intro h
    obtain ⟨u, hr, ha⟩ := proposition_5_4.mp h
    exact horseRepresentation_of_affine hr ha
  · rintro ⟨U, hr⟩
    exact proposition_5_4.mpr ⟨_, hr, horseValue_affine U⟩

/-- Proposition 5.13. State independence gives full-support subjective expected utility. -/
theorem proposition_5_13 [Nonempty S] : MixtureAxioms r ∧ StateIndependentComparisons r ↔
    ∃ (p : S → ℝ) (U : X → ℝ), (∀ s, 0 < p s) ∧ ∑ s, p s = 1 ∧
      Represents (SubjectiveHorseValue p U) r := by
  constructor
  · rintro ⟨h, hi⟩
    obtain ⟨V, hV⟩ := proposition_5_12.mp h
    exact subjectiveRepresentation_of_stateIndependent hV hi
  · rintro ⟨p, U, hp, hsum, hr⟩
    exact ⟨proposition_5_4.mpr ⟨_, hr, subjectiveHorseValue_affine p U⟩,
      subjectiveActValue_stateIndependent p hp hsum (ExpectedUtility U) hr⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Mixtures of Borel probability measures

Kreps I, Proposition 5.10, pp. 98–100. A finite mixture of probability measures is
an actual measure with total mass one. Evaluation on every measurable event
identifies its convex-space structure. Weak convergence is Mathlib's topology
of convergence of integrals against bounded continuous functions.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity
open scoped ENNReal BoundedContinuousFunction

variable {X I : Type*} [MeasurableSpace X]

/-- A finite convex combination of probability measures, with its unit mass proved. -/
noncomputable def MeasureCombination (w : SimpleLottery I) (f : I → ProbabilityMeasure X) :
    ProbabilityMeasure X :=
  ⟨∑ i ∈ w.weights.support, ENNReal.ofReal (w.weights i) • (f i : Measure X), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => w.nonneg i)]
    change ENNReal.ofReal (w.weights.sum (fun _ v => v)) = 1
    rw [w.total, ENNReal.ofReal_one]⟩⟩

/-- The probability of an event is the weighted average of its component probabilities. -/
theorem measureCombination_event (w : SimpleLottery I) (f : I → ProbabilityMeasure X) (T : Set X) :
    (MeasureCombination w f : Measure X).real T =
      w.iConvexComb (fun i => (f i : Measure X).real T) := by
  rw [measureReal_def, MeasureCombination, ProbabilityMeasure.coe_mk, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (w.nonneg _), iConvexComb_eq_sum,
    Finsupp.sum, smul_eq_mul, measureReal_def]

/-- Event evaluations distinguish probability measures. -/
theorem probabilityMeasure_ext_real {p q : ProbabilityMeasure X}
    (h : ∀ T, (p : Measure X).real T = (q : Measure X).real T) : p = q := by
  apply ProbabilityMeasure.toMeasure_injective
  ext T
  rw [← ofReal_measureReal (measure_ne_top (p : Measure X) T),
    ← ofReal_measureReal (measure_ne_top (q : Measure X) T), h T]

/-- The finite-barycenter structure for Borel probability measures used by Proposition 5.10. -/
@[instance_reducible] noncomputable def BorelConvexSpace (X : Type*) [MeasurableSpace X] :
    ConvexSpace ℝ (ProbabilityMeasure X) := .mk (fun w => MeasureCombination w id)
  (by
    intro p
    apply probabilityMeasure_ext_real
    intro T
    rw [measureCombination_event, iConvexComb_single]
    rfl)
  (by
    intro w
    apply probabilityMeasure_ext_real
    intro T
    simp only [measureCombination_event, id_eq, iConvexComb_map]
    simpa only [id_eq, iConvexComb_id'] using
      iConvexComb_assoc w id (fun p : ProbabilityMeasure X => (p : Measure X).real T))

attribute [local instance] BorelConvexSpace

/-- Mixing Borel measures takes the same real weighted average of every event's probabilities. -/
theorem borelMix_event (a : Weight) (p q : ProbabilityMeasure X) (T : Set X) :
    ((Mix a p q : ProbabilityMeasure X) : Measure X).real T =
      a.val * (p : Measure X).real T + (1 - a.val) * (q : Measure X).real T := by
  unfold Mix convexCombPair
  rw [show ∀ w : SimpleLottery (ProbabilityMeasure X),
    (w.sConvexComb : ProbabilityMeasure X) = MeasureCombination w id from fun _ => rfl]
  rw [measureCombination_event, iConvexComb, StdSimplex.map_duple]
  exact convexCombPair_eq_sum _ _ _ _ _ _ _

/-- The simple lottery regarded as its discrete Borel probability distribution. -/
noncomputable def AtomicProbability (p : SimpleLottery X) : ProbabilityMeasure X :=
  MeasureCombination p diracProba

/-- Bounded continuous test functions integrate linearly over any finite mixture. -/
theorem integral_measureCombination [TopologicalSpace X] [OpensMeasurableSpace X]
    (w : SimpleLottery I) (f : I → ProbabilityMeasure X) (g : X →ᵇ ℝ) :
    ∫ x, g x ∂(MeasureCombination w f : Measure X) =
      w.iConvexComb (fun i => ∫ x, g x ∂(f i : Measure X)) := by
  change (∫ x, g x ∂(∑ i ∈ w.weights.support,
    ENNReal.ofReal (w.weights i) • (f i : Measure X))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (w.nonneg _), smul_eq_mul,
      iConvexComb_eq_sum, Finsupp.sum]
  · intro i _
    exact (g.integrable (f i : Measure X)).smul_measure ENNReal.ofReal_ne_top

/-- The integral of a test function against a simple distribution agrees with finite expectation. -/
theorem integral_atomicProbability [TopologicalSpace X] [OpensMeasurableSpace X]
    (p : SimpleLottery X) (g : X →ᵇ ℝ) :
    ∫ x, g x ∂(AtomicProbability p : Measure X) = ExpectedUtility g p := by
  rw [AtomicProbability, integral_measureCombination]
  simp only [diracProba, ProbabilityMeasure.coe_mk,
    integral_dirac' _ _ g.continuous.stronglyMeasurable, iConvexComb_eq_sum, smul_eq_mul,
    ExpectedUtility]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite atomic and compact-density probability laws

Kreps I, pp. 97–98. The source's weighted components are a nonnegative finite
atom vector and a nonnegative compactly supported continuous density. The
formula on every measurable set describes an actual Borel probability measure.
Singleton masses recover the atom vector. Integrals over measurable sets recover
the continuous component. The resulting domain is convex under measure mixtures.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity
open scoped ENNReal

attribute [local instance] BorelConvexSpace

/-- Evaluate a finite vector of atomic masses against any real test function. -/
noncomputable def AtomicFunctional (u : ℝ → ℝ) : (ℝ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ u

/-- Evaluation of a singleton indicator gives its atom mass. -/
theorem atomicFunctional_singleton (w : ℝ →₀ ℝ) (x : ℝ) :
    AtomicFunctional (({x} : Set ℝ).indicator (fun _ => 1)) w = w x := by
  classical
  change w.sum (fun y t => t * ({x} : Set ℝ).indicator (fun _ => 1) y) = _
  rw [Finsupp.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Set.indicator, hy]
  · simp

/-- A law on all measurable events, using its weighted finite atoms and weighted density. -/
structure AtomicDensityPresentation (p : ProbabilityMeasure ℝ) (w : ℝ →₀ ℝ) (f : ℝ → ℝ) : Prop where
  /-- Each atom has nonnegative mass. -/
  atoms_nonneg : 0 ≤ w
  /-- The weighted density is continuous. -/
  continuous : Continuous f
  /-- Its support stays in some compact set depending on the law. -/
  compact : HasCompactSupport f
  /-- The density is nonnegative everywhere. -/
  density_nonneg : ∀ x, 0 ≤ f x
  /-- Every event has its finite atomic mass plus its continuous-density integral. -/
  event : ∀ T : Set ℝ, MeasurableSet T → (p : Measure ℝ).real T =
    AtomicFunctional (T.indicator (fun _ => 1)) w + ∫ x in T, f x

/-- Individual atoms are exactly the singleton probabilities of the underlying measure. -/
theorem atomicDensity_singleton {p : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p w f) (x : ℝ) : (p : Measure ℝ).real {x} = w x := by
  rw [h.event {x} (measurableSet_singleton x), atomicFunctional_singleton]
  simp

/-- Both weighted components of an actual law are uniquely determined, also at mixture endpoints. -/
theorem atomicDensity_unique {p : ProbabilityMeasure ℝ} {v w : ℝ →₀ ℝ} {f g : ℝ → ℝ}
    (h : AtomicDensityPresentation p v f) (k : AtomicDensityPresentation p w g) :
    v = w ∧ f = g := by
  have he : v = w := Finsupp.ext fun x =>
    (atomicDensity_singleton h x).symm.trans (atomicDensity_singleton k x)
  subst w
  refine ⟨rfl, (h.continuous.ae_eq_iff_eq (μ := volume) k.continuous).mp ?_⟩
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (h.continuous.integrable_of_hasCompactSupport h.compact)
    (k.continuous.integrable_of_hasCompactSupport k.compact)
  intro T hT _
  linarith [h.event T hT, k.event T hT]

/-- Finite atomic mass and density mass add to one. -/
theorem atomicDensity_normalized {p : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p w f) :
    AtomicFunctional (fun _ => 1) w + ∫ x, f x = 1 := by
  simpa using (h.event Set.univ MeasurableSet.univ).symm

/-- Both weighted components mix by the same convex coefficients as the underlying measures. -/
theorem atomicDensity_mix (a : Weight) {p q : ProbabilityMeasure ℝ}
    {v w : ℝ →₀ ℝ} {f g : ℝ → ℝ}
    (h : AtomicDensityPresentation p v f) (k : AtomicDensityPresentation q w g) :
    AtomicDensityPresentation (Mix a p q) (a.val • v + (1 - a.val) • w)
      (fun x => a.val * f x + (1 - a.val) * g x) := by
  have ha := a.property.1
  have hb := sub_nonneg.mpr a.property.2
  refine ⟨add_nonneg (smul_nonneg ha h.atoms_nonneg) (smul_nonneg hb k.atoms_nonneg),
    (continuous_const.mul h.continuous).add (continuous_const.mul k.continuous), ?_,
    fun x => add_nonneg (mul_nonneg ha (h.density_nonneg x)) (mul_nonneg hb (k.density_nonneg x)),
    ?_⟩
  · exact (h.compact.mul_left (f := fun _ => a.val)).add
      (k.compact.mul_left (f := fun _ => 1 - a.val))
  · intro T hT
    have hfi : Integrable f volume := h.continuous.integrable_of_hasCompactSupport h.compact
    have hgi : Integrable g volume := k.continuous.integrable_of_hasCompactSupport k.compact
    rw [borelMix_event, h.event T hT, k.event T hT,
      integral_add (hfi.integrableOn.const_mul _) (hgi.integrableOn.const_mul _),
      integral_const_mul, integral_const_mul, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring

/-- The exact domain of Borel probabilities admitting a finite atomic and compact-density split. -/
def AtomicDensityDomain : Set (ProbabilityMeasure ℝ) :=
  {p | ∃ (w : ℝ →₀ ℝ) (f : ℝ → ℝ), AtomicDensityPresentation p w f}

/-- The domain in the printed example is closed under mixtures of its actual measures. -/
theorem atomicDensityDomain_isConvex : IsConvexSet ℝ AtomicDensityDomain := by
  apply IsConvexSet.of_convexCombPair_mem
  rintro a b ha hb hab p ⟨v, f, hf⟩ q ⟨w, g, hg⟩
  have he : b = 1 - a := by linarith
  subst b
  let t : Weight := ⟨a, ha, by linarith⟩
  exact ⟨_, _, atomicDensity_mix t hf hg⟩

/-- The convex structure on the source domain is inherited from Borel probability measures. -/
noncomputable abbrev atomicDensityConvexSpace : ConvexSpace ℝ AtomicDensityDomain :=
  .subtype _ atomicDensityDomain_isConvex

/-- The source functional equals one plus the atomic expectation of `x - 1`. -/
noncomputable def AtomicDensityIndex (p : AtomicDensityDomain) : ℝ :=
  AtomicFunctional (fun x => x - 1) (Classical.choose p.property) + 1

/-- The value can use any presentation because singleton masses determine the weighted atoms. -/
theorem atomicDensityIndex_eq (p : AtomicDensityDomain) {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p.val w f) :
    AtomicDensityIndex p = AtomicFunctional (fun x => x - 1) w + 1 := by
  obtain ⟨g, hg⟩ := Classical.choose_spec p.property
  rw [AtomicDensityIndex, (atomicDensity_unique hg h).1]

/-- The source formula at atomic fraction `a` and ordinary simple lottery `q`. -/
theorem atomicDensityIndex_scaled (p : AtomicDensityDomain) (q : SimpleLottery ℝ) (a : ℝ)
    {f : ℝ → ℝ} (h : AtomicDensityPresentation p.val (a • q.weights) f) :
    AtomicDensityIndex p = a * ExpectedUtility id q + (1 - a) := by
  have he : AtomicFunctional (fun x => x - 1) q.weights = ExpectedUtility id q - 1 := by
    change (∑ x ∈ q.weights.support, q.weights x * (x - 1)) =
      (∑ x ∈ q.weights.support, q.weights x * x) - 1
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [show ∑ x ∈ q.weights.support, q.weights x = 1 from q.total]
  rw [atomicDensityIndex_eq p h, map_smul, he, smul_eq_mul]
  ring

/-- Finite mixtures preserve the weighted discrete plus continuous index. -/
theorem atomicDensityIndex_affine : @AffineInMix _ atomicDensityConvexSpace AtomicDensityIndex := by
  let _ := atomicDensityConvexSpace
  intro a p q
  obtain ⟨v, f, hf⟩ := p.property
  obtain ⟨w, g, hg⟩ := q.property
  have he : (Mix a p q).val = Mix a p.val q.val := subtypeVal_convexCombPair _
    atomicDensityDomain_isConvex a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
    (by ring) p q
  have hp := atomicDensity_mix a hf hg
  rw [← he] at hp
  rw [atomicDensityIndex_eq _ hp, atomicDensityIndex_eq _ hf, atomicDensityIndex_eq _ hg,
    map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The model with weighted atomic mean and constant continuous value meets all three axioms. -/
theorem atomicDensityIndex_mixtureAxioms :
    @MixtureAxioms _ atomicDensityConvexSpace (UtilityPref AtomicDensityIndex) :=
  @mixtureAxioms_of_representation _ atomicDensityConvexSpace _ _ (fun _ _ => Iff.rfl)
    atomicDensityIndex_affine

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A mixture-affine utility with no expected prize utility

Kreps I, pp. 97–98. Purely atomic laws have their ordinary monetary expectation.
Purely continuous laws have value one. The example compares two dollars for
sure with a continuous probability supported on the entire interval [3,4].
Finite lotteries force any proposed prize index to be positive affine in money.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped ENNReal

/-- Every simple lottery is a member of the example's domain with zero continuous density. -/
theorem atomicProbability_presentation (q : SimpleLottery ℝ) :
    AtomicDensityPresentation (AtomicProbability q) q.weights (fun _ => 0) := by
  refine ⟨q.nonneg, continuous_const, ?_, fun _ => le_rfl, ?_⟩
  · simp [HasCompactSupport]
  · intro T hT
    have hd (x : ℝ) : (diracProba x : Measure ℝ).real T = T.indicator (fun _ => 1) x := by
      classical
      by_cases hx : x ∈ T <;> simp [diracProba, measureReal_def, Measure.dirac_apply' _ hT, hx]
    rw [AtomicProbability, measureCombination_event, iConvexComb_eq_sum]
    simp only [hd, integral_zero, add_zero, AtomicFunctional, Finsupp.linearCombination_apply]

/-- Embed a finite monetary roulette in the actual space of Borel probability laws. -/
noncomputable def AtomicLaw (q : SimpleLottery ℝ) : AtomicDensityDomain :=
  ⟨AtomicProbability q, q.weights, fun _ => 0, atomicProbability_presentation q⟩

/-- On the purely atomic slice the printed index is the expected monetary payoff. -/
theorem atomicDensityIndex_atomic (q : SimpleLottery ℝ) :
    AtomicDensityIndex (AtomicLaw q) = ExpectedUtility id q := by
  have h : AtomicDensityPresentation (AtomicLaw q).val ((1 : ℝ) • q.weights) (fun _ => 0) := by
    simpa [AtomicLaw] using atomicProbability_presentation q
  simpa using atomicDensityIndex_scaled (AtomicLaw q) q 1 h

/-- Integration against a discrete law is finite expectation even for unbounded prize utility. -/
theorem integral_atomicLaw (q : SimpleLottery ℝ) (U : ℝ → ℝ) :
    ∫ x, U x ∂((AtomicLaw q).val : Measure ℝ) = ExpectedUtility U q := by
  change (∫ x, U x ∂(∑ i ∈ q.weights.support,
    ENNReal.ofReal (q.weights i) • (diracProba i : Measure ℝ))) = _
  rw [integral_finsetSum_measure]
  · simp [ExpectedUtility, Finsupp.sum, integral_smul_measure, diracProba,
      ENNReal.toReal_ofReal (q.nonneg _)]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The Borel probability with the supplied nonnegative unit-integral density. -/
noncomputable def DensityProbability (f : ℝ → ℝ) (hi : Integrable f volume)
    (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1) : ProbabilityMeasure ℝ := by
  refine ⟨volume.withDensity (fun x => ENNReal.ofReal (f x)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf), hn, ENNReal.ofReal_one]

/-- The probability with this compact continuous density has no atomic component. -/
theorem densityProbability_presentation (f : ℝ → ℝ) (hc : Continuous f)
    (hk : HasCompactSupport f) (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1) :
    AtomicDensityPresentation
      (DensityProbability f (hc.integrable_of_hasCompactSupport hk) hf hn) 0 f := by
  refine ⟨le_rfl, hc, hk, hf, ?_⟩
  intro T hT
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))).real T = _
  rw [measureReal_def, withDensity_apply _ hT,
    ← ofReal_integral_eq_lintegral_ofReal
      (hc.integrable_of_hasCompactSupport (μ := volume) hk).integrableOn (Eventually.of_forall hf),
    ENNReal.toReal_ofReal (integral_nonneg hf), map_zero, zero_add]

/-- A smooth bump whose support closure is exactly the literal interval [3,4]. -/
noncomputable def ThreeFourBump : ContDiffBump (7 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalized compact density in the comparison is supported precisely on [3,4]. -/
theorem threeFour_support : tsupport (ThreeFourBump.normed volume) = Set.Icc 3 4 := by
  rw [ThreeFourBump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  norm_num [ThreeFourBump]

/-- The continuous-density probability competing with the sure two dollars. -/
noncomputable def ThreeFourLaw : AtomicDensityDomain :=
  ⟨DensityProbability (ThreeFourBump.normed volume) ThreeFourBump.integrable_normed
    ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed,
    0, ThreeFourBump.normed volume, densityProbability_presentation _
      ThreeFourBump.continuous_normed ThreeFourBump.hasCompactSupport_normed
      ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed⟩

/-- All prizes paid by the continuous law lie almost surely between three and four dollars. -/
theorem threeFourLaw_range : ∀ᵐ x ∂(ThreeFourLaw.val : Measure ℝ), x ∈ Set.Icc 3 4 := by
  apply (ae_withDensity_iff ThreeFourBump.continuous_normed.measurable.ennreal_ofReal).mpr
  apply Eventually.of_forall
  intro x hx
  rw [← threeFour_support]
  apply subset_tsupport _
  intro h
  exact hx (by simp [h])

/-- The source index assigns the continuous law one and ranks two dollars for sure above it. -/
theorem atomicDensity_literal_values : AtomicDensityIndex ThreeFourLaw = 1 ∧
    AtomicDensityIndex (AtomicLaw (PureLottery 2)) = 2 := by
  constructor
  · rw [atomicDensityIndex_eq ThreeFourLaw (densityProbability_presentation _
      ThreeFourBump.continuous_normed ThreeFourBump.hasCompactSupport_normed
      ThreeFourBump.nonneg_normed ThreeFourBump.integral_normed), map_zero, zero_add]
  · rw [atomicDensityIndex_atomic, expectedUtility_pure]
    rfl

/-- The mixture-axiom preferences on this domain have no expected prize utility. -/
theorem atomicDensity_no_expectedUtility : ¬∃ U : ℝ → ℝ,
    Represents (fun p : AtomicDensityDomain => ∫ x, U x ∂(p.val : Measure ℝ))
      (UtilityPref AtomicDensityIndex) := by
  rintro ⟨U, hU⟩
  have hfinite : Represents (ExpectedUtility U) (UtilityPref (ExpectedUtility id)) := by
    intro p q
    have he := hU (AtomicLaw p) (AtomicLaw q)
    simpa only [UtilityPref, atomicDensityIndex_atomic, integral_atomicLaw] using he
  obtain ⟨a, ha, b, hab⟩ := proposition_5_3_unique
    (r := UtilityPref (ExpectedUtility id)) (U := id) (fun _ _ => Iff.rfl) hfinite
  have heU : U = fun x => a * x + b := funext hab
  have hint : Integrable U (ThreeFourLaw.val : Measure ℝ) := by
    rw [heU]
    apply Integrable.of_bound (by fun_prop) (4 * a + |b|)
    filter_upwards [threeFourLaw_range] with x hx
    rw [Real.norm_eq_abs]
    calc
      |a * x + b| ≤ |a * x| + |b| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (mul_nonneg ha.le (by linarith [hx.1]))]; nlinarith [hx.2]
  have hmin : a * 3 + b ≤ ∫ x, U x ∂(ThreeFourLaw.val : Measure ℝ) := by
    have hle : ∀ᵐ x ∂(ThreeFourLaw.val : Measure ℝ), a * 3 + b ≤ U x := by
      filter_upwards [threeFourLaw_range] with x hx
      rw [hab x]
      change a * 3 + b ≤ a * x + b
      exact add_le_add_left (mul_le_mul_of_nonneg_left hx.1 ha.le) _
    simpa using integral_mono_ae (integrable_const _) hint hle
  obtain ⟨hd, hs⟩ := atomicDensity_literal_values
  have h := (hU (AtomicLaw (PureLottery 2)) ThreeFourLaw).mp
    (show AtomicDensityIndex ThreeFourLaw ≤ AtomicDensityIndex (AtomicLaw (PureLottery 2)) by
      rw [hd, hs]; norm_num)
  dsimp only at h
  rw [integral_atomicLaw, expectedUtility_pure, hab 2] at h
  change _ ≤ a * 2 + b at h
  linarith

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Normalizing the two components of the mixed-law example

Kreps I, pp. 97–98. Each member of the example's domain is an actual mixture
of a simple probability and a normalized continuous compact density, including
the endpoints. At zero weight a normalized component can be chosen arbitrarily.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity

attribute [local instance] BorelConvexSpace

/-- Testing a finite mass vector against one gives its total mass. -/
theorem atomicFunctional_one (w : ℝ →₀ ℝ) :
    AtomicFunctional (fun _ => 1) w = w.sum (fun _ t => t) := by
  simp [AtomicFunctional, Finsupp.linearCombination_apply]

/-- Split a finite nonnegative mass vector into total mass times a probability lottery. -/
theorem atomicWeights_normalize (w : ℝ →₀ ℝ) (hw : 0 ≤ w) :
    ∃ q : SimpleLottery ℝ, w = AtomicFunctional (fun _ => 1) w • q.weights := by
  classical
  let a := AtomicFunctional (fun _ => 1) w
  have hs : (∑ x ∈ w.support, w x) = a := (atomicFunctional_one w).symm
  have ha : 0 ≤ a := hs ▸ Finset.sum_nonneg fun i _ => hw i
  by_cases hz : a = 0
  · refine ⟨PureLottery 0, ?_⟩
    change w = a • _
    rw [hz, zero_smul]
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ w.support) => hw i)).mp
      (hs.trans hz)
    ext i
    by_cases hi : i ∈ w.support
    · exact hsum i hi
    · exact Finsupp.notMem_support_iff.mp hi
  · let q : SimpleLottery ℝ := {
      weights := a⁻¹ • w
      nonneg := smul_nonneg (inv_nonneg.mpr ha) hw
      total := by
        rw [← atomicFunctional_one, map_smul, smul_eq_mul]
        exact inv_mul_cancel₀ hz }
    refine ⟨q, ?_⟩
    change w = a • (a⁻¹ • w)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- Normalize a nonnegative compact density, selecting any unit density at zero total mass. -/
theorem compactDensity_normalize {f : ℝ → ℝ} (hc : Continuous f) (hk : HasCompactSupport f)
    (hf : ∀ x, 0 ≤ f x) :
    ∃ v : ℝ → ℝ, Continuous v ∧ HasCompactSupport v ∧ (∀ x, 0 ≤ v x) ∧
      (∫ x, v x = 1) ∧ ∀ x, f x = (∫ t, f t) * v x := by
  let m := ∫ x, f x
  have hm : 0 ≤ m := integral_nonneg hf
  by_cases hz : m = 0
  · have he := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hf)
        (hc.integrable_of_hasCompactSupport (μ := volume) hk)).mp hz
    have hzero : f = 0 := (hc.ae_eq_iff_eq volume continuous_zero).mp he
    refine ⟨ThreeFourBump.normed volume, ThreeFourBump.continuous_normed,
      ThreeFourBump.hasCompactSupport_normed, ThreeFourBump.nonneg_normed,
      ThreeFourBump.integral_normed, ?_⟩
    intro x
    change f x = m * _
    simp [hzero, hz]
  · refine ⟨fun x => m⁻¹ * f x, continuous_const.mul hc,
      hk.mul_left (f := fun _ => m⁻¹), fun x => mul_nonneg (inv_nonneg.mpr hm) (hf x), ?_, ?_⟩
    · rw [integral_const_mul]
      exact inv_mul_cancel₀ hz
    · intro x
      change f x = m * (m⁻¹ * f x)
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- Matching weighted atom vectors and densities imply equality of the actual Borel laws. -/
theorem atomicDensityPresentation_ext {p q : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (hp : AtomicDensityPresentation p w f) (hq : AtomicDensityPresentation q w f) : p = q := by
  apply ProbabilityMeasure.toMeasure_injective
  ext T hT
  rw [← ofReal_measureReal (measure_ne_top (p : Measure ℝ) T),
    ← ofReal_measureReal (measure_ne_top (q : Measure ℝ) T), hp.event T hT, hq.event T hT]

/-- Exactly the laws in the example have the printed mixture of two normalized probabilities. -/
theorem atomicDensityDomain_iff_mixture (p : ProbabilityMeasure ℝ) :
    p ∈ AtomicDensityDomain ↔ ∃ (a : Weight) (q : SimpleLottery ℝ) (f : ℝ → ℝ)
      (hc : Continuous f) (hk : HasCompactSupport f) (hf : ∀ x, 0 ≤ f x) (hn : ∫ x, f x = 1),
      p = Mix a (AtomicProbability q) (DensityProbability f
        (hc.integrable_of_hasCompactSupport hk) hf hn) := by
  constructor
  · rintro ⟨w, g, h⟩
    let t := AtomicFunctional (fun _ => 1) w
    have ht : 0 ≤ t := by
      change 0 ≤ AtomicFunctional _ w
      rw [atomicFunctional_one]
      exact Finset.sum_nonneg fun i _ => h.atoms_nonneg i
    have hsum : t + (∫ x, g x) = 1 := atomicDensity_normalized h
    have hm : 0 ≤ ∫ x, g x := integral_nonneg h.density_nonneg
    let a : Weight := ⟨t, ht, by linarith⟩
    obtain ⟨q, hq⟩ := atomicWeights_normalize w h.atoms_nonneg
    obtain ⟨f, hc, hk, hf, hn, he⟩ :=
      compactDensity_normalize h.continuous h.compact h.density_nonneg
    refine ⟨a, q, f, hc, hk, hf, hn, atomicDensityPresentation_ext h ?_⟩
    have H := atomicDensity_mix a (atomicProbability_presentation q)
      (densityProbability_presentation f hc hk hf hn)
    have hw : a.val • q.weights + (1 - a.val) • (0 : ℝ →₀ ℝ) = w := by
      simpa only [smul_zero, add_zero] using hq.symm
    have hd : (fun x => a.val * 0 + (1 - a.val) * f x) = g := by
      funext x
      have ht' : 1 - a.val = ∫ t, g t := by change 1 - t = _; linarith
      simpa only [mul_zero, zero_add, ht'] using (he x).symm
    rw [hw, hd] at H
    exact H
  · rintro ⟨a, q, f, hc, hk, hf, hn, rfl⟩
    exact ⟨_, _, atomicDensity_mix a (atomicProbability_presentation q)
      (densityProbability_presentation f hc hk hf hn)⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Approximating Borel probabilities by lotteries of finite support

Kreps I, pp. 98–99. Approximating the identity map pointwise by measurable simple
functions induces a sequence of finite lotteries. The probabilities are the
actual masses of their fibers. Bounded convergence proves weak convergence.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped ENNReal Topology BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

attribute [local instance] BorelConvexSpace

/-- An indexed combination is the convex-space barycenter of its mapped weights. -/
theorem measureCombination_eq_barycenter {I : Type*} (w : SimpleLottery I)
    (f : I → ProbabilityMeasure X) : MeasureCombination w f = (w.map f).sConvexComb := by
  apply probabilityMeasure_ext_real
  intro T
  change _ = (MeasureCombination (w.map f) id : Measure X).real T
  simp only [measureCombination_event, iConvexComb_map, id_eq]

/-- Any binary-affine index respects arbitrary finite barycenters. -/
theorem affineInMix_barycenter {Z : Type*} [ConvexSpace ℝ Z] {u : Z → ℝ}
    (hu : AffineInMix u) (w : SimpleLottery Z) : u w.sConvexComb = ExpectedUtility u w := by
  have hf : AffineInMix (fun p : SimpleLottery Z => u p.sConvexComb) := by
    intro a p q
    change u (Mix a p q).sConvexComb = _
    rw [Mix, sConvexComb_convexCombPair]
    exact hu a p.sConvexComb q.sConvexComb
  simpa only [PureLottery, sConvexComb_single] using affineInMix_eq_expectedUtility hf w

/-- On a discrete probability, an affine index sums its values on the sure prizes. -/
theorem affineInMix_atomicProbability {u : ProbabilityMeasure X → ℝ} (hu : AffineInMix u)
    (p : SimpleLottery X) :
    u (AtomicProbability p) = ExpectedUtility (fun x => u (diracProba x)) p := by
    rw [AtomicProbability, measureCombination_eq_barycenter, affineInMix_barycenter hu,
      expectedUtility_eq_affineMap, expectedUtility_eq_affineMap, StdSimplex.affineMapMk_apply,
      StdSimplex.affineMapMk_apply, iConvexComb_map]

/-- The fiber probabilities on the finite range of a simple function sum to one. -/
noncomputable def ImageWeights (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    SimpleLottery f.range := {
    weights := Finsupp.equivFunOnFinite.symm (fun t => (μ : Measure X).real (f ⁻¹' {t.val}))
    nonneg := fun _ => ENNReal.toReal_nonneg
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change ∑ t : f.range, (μ : Measure X).real (f ⁻¹' {t.val}) = 1
      rw [Finset.sum_coe_sort f.range (fun t => (μ : Measure X).real (f ⁻¹' {t}))]
      simp only [measureReal_def, ← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
        f.sum_range_measure_preimage_singleton, measure_univ, ENNReal.toReal_one] }

/-- The lottery of outputs of a measurable simple function under a probability measure. -/
noncomputable def SimpleImageLottery (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    SimpleLottery X := (ImageWeights μ f).map Subtype.val

/-- The finite image lottery has exactly the pushforward probability law. -/
theorem simpleImageLottery_law [MeasurableSingletonClass X] (μ : ProbabilityMeasure X)
    (f : SimpleFunc X X) : AtomicProbability (SimpleImageLottery μ f) = μ.map f := by
  classical
  let w := ImageWeights μ f
  have he : AtomicProbability (SimpleImageLottery μ f) =
      MeasureCombination w (fun t => diracProba t.val) := by
    apply probabilityMeasure_ext_real
    intro T
    simp only [AtomicProbability, SimpleImageLottery, measureCombination_event, iConvexComb_map]
    rfl
  rw [he]
  apply ProbabilityMeasure.toMeasure_injective
  change w.weights.sum (fun t v => ENNReal.ofReal v • Measure.dirac t.val) =
    (μ : Measure X).map f
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ t : f.range, ENNReal.ofReal ((μ : Measure X).real (f ⁻¹' {t.val})) •
    Measure.dirac t.val = _
  simp only [ofReal_measureReal (measure_ne_top _ _)]
  rw [Finset.sum_coe_sort f.range (fun t => (μ : Measure X) (f ⁻¹' {t}) • Measure.dirac t)]
  exact ((Measure.ae_mem_finset_iff_map_eq_sum_dirac f.aemeasurable).mp
    (Eventually.of_forall f.mem_range_self)).symm

/-- Every Borel law on a second-countable metric prize space is a weak limit of simple lotteries. -/
theorem exists_simpleLotteries_tendsto [PseudoMetricSpace X]
    [SecondCountableTopology X] [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (μ : ProbabilityMeasure X) : ∃ p : ℕ → SimpleLottery X,
      Tendsto (fun n => AtomicProbability (p n)) atTop (𝓝 μ) := by
  have hf : StronglyMeasurable (id : X → X) := continuous_id.stronglyMeasurable
  refine ⟨fun n => SimpleImageLottery μ (hf.approx n), ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [simpleImageLottery_law, ProbabilityMeasure.toMeasure_map]
  simp_rw [integral_map (SimpleFunc.aemeasurable _) g.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
  · exact fun n => (g.continuous.measurable.comp (hf.approx n).measurable).aestronglyMeasurable
  · exact integrable_const _
  · exact fun n => Eventually.of_forall (fun x => g.norm_coe_le_norm (hf.approx n x))
  · exact Eventually.of_forall fun x => g.continuous.continuousAt.tendsto.comp (hf.tendsto_approx x)

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Weak continuity and bounded affine utility

Kreps I, Proposition 5.10, pp. 98–100. Open strict contours make an affine
representation continuous, since it takes every value between its attainable
levels. Weak continuity on the entire probability space forces boundedness:
vanishing weights on arbitrarily distant utility values contradict continuity.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped Topology BoundedContinuousFunction

variable {Z X : Type*}

/-- The two strict contour sets at each fixed alternative are open. -/
def OpenStrictSections [TopologicalSpace Z] (r : Z → Z → Prop) : Prop :=
  ∀ z, IsOpen {x | Strict r x z} ∧ IsOpen {x | Strict r z x}

/-- An affine utility attains each scalar strictly between two attainable values. -/
theorem affine_attains_between [ConvexSpace ℝ Z] {u : Z → ℝ} (hu : AffineInMix u)
    {x y : Z} {c : ℝ} (hx : u x ≤ c) (hy : c ≤ u y) (hxy : u x < u y) :
    ∃ z, u z = c := by
  have hd := sub_pos.mpr hxy
  let a : Weight := ⟨(c - u x) / (u y - u x),
    div_nonneg (sub_nonneg.mpr hx) hd.le, (div_le_one hd).mpr (by linarith)⟩
  have he : a.val * (u y - u x) = c - u x := div_mul_cancel₀ _ hd.ne'
  exact ⟨Mix a y x, by rw [hu]; linarith only [he]⟩

/-- Open strict sections characterize continuity of any mixture-affine representing index. -/
theorem openStrictSections_iff_continuous [TopologicalSpace Z] [ConvexSpace ℝ Z]
    {r : Z → Z → Prop} {u : Z → ℝ} (hr : Represents u r) (ha : AffineInMix u) :
    OpenStrictSections r ↔ Continuous u := by
  have hs (x y) : Strict r x y ↔ u y < u x := by
    simp only [Strict, hr x y, hr y x, lt_iff_le_not_ge]
  constructor
  · intro ho
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_order.mpr
    constructor
    · intro c hc
      by_cases hy : ∃ y, u y ≤ c
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨z, rfl⟩ := affine_attains_between ha hy hc.le (hy.trans_lt hc)
        have he := (ho z).1.mem_nhds ((hs x z).mpr hc)
        filter_upwards [he] with t ht using (hs t z).mp ht
      · exact Eventually.of_forall fun t => lt_of_not_ge (fun h => hy ⟨t, h⟩)
    · intro c hc
      by_cases hy : ∃ y, c ≤ u y
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨z, rfl⟩ := affine_attains_between ha hc.le hy (hc.trans_le hy)
        have he := (ho z).2.mem_nhds ((hs z x).mpr hc)
        filter_upwards [he] with t ht using (hs z t).mp ht
      · exact Eventually.of_forall fun t => lt_of_not_ge (fun h => hy ⟨t, h⟩)
  · intro hc z
    simp only [hs]
    exact ⟨isOpen_lt continuous_const hc, isOpen_lt hc continuous_const⟩

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

attribute [local instance] BorelConvexSpace

/-- Integrating a bounded continuous utility is affine under mixing probability measures. -/
theorem integral_affineInMix (g : X →ᵇ ℝ) :
    AffineInMix (fun p : ProbabilityMeasure X => ∫ x, g x ∂(p : Measure X)) := by
  intro a p q
  change (∫ x, g x ∂(MeasureCombination (StdSimplex.duple p q a.property.1
    (sub_nonneg.mpr a.property.2) (by ring)) id : Measure X)) = _
  rw [integral_measureCombination, iConvexComb, StdSimplex.map_duple]
  exact convexCombPair_eq_sum _ _ _ _ _ _ _

/-- A sequence of arbitrarily varying probability measures can receive vanishing mixture weight. -/
theorem weakMix_tendsto (p : ProbabilityMeasure X) (q : ℕ → ProbabilityMeasure X)
    (w : ℕ → Weight) (hw : Tendsto (fun n => (w n).val) atTop (𝓝 0)) :
    Tendsto (fun n => Mix (w n) (q n) p) atTop (𝓝 p) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let v (m : ProbabilityMeasure X) := ∫ x, g x ∂(m : Measure X)
  have hb : IsBoundedUnder (· ≤ ·) atTop (norm ∘ (fun n => v (q n))) :=
    isBoundedUnder_of ⟨‖g‖, fun n => g.norm_integral_le_norm (q n : Measure X)⟩
  have hzero := isBoundedUnder_le_mul_tendsto_zero hb hw
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).sub hw
  have hlim := hzero.add (hone.mul_const (v p))
  convert hlim using 1
  · funext n
    change v (Mix (w n) (q n) p) = _
    rw [show v (Mix (w n) (q n) p) = _ from integral_affineInMix g (w n) (q n) p]
    dsimp [v]
    ring
  · simp [v]

/-- A continuous affine index on all probability measures has bounded range. -/
theorem continuous_affine_bounded {u : ProbabilityMeasure X → ℝ}
    (hc : Continuous u) (ha : AffineInMix u) : ∃ C : ℝ, ∀ p, |u p| ≤ C := by
  classical
  by_cases hi : Nonempty (ProbabilityMeasure X)
  · obtain ⟨p⟩ := hi
    suffices hb : ∃ C : ℝ, ∀ q, |u q - u p| ≤ C by
      obtain ⟨C, hC⟩ := hb
      refine ⟨C + |u p|, fun q => ?_⟩
      calc
        |u q| = |u q - u p + u p| := by rw [sub_add_cancel]
        _ ≤ |u q - u p| + |u p| := abs_add_le _ _
        _ ≤ _ := add_le_add_left (hC q) _
    by_contra! h
    choose q hq using fun n : ℕ => h ((n : ℝ) + 1)
    let w (n : ℕ) : Weight := ⟨1 / ((n : ℝ) + 1), by positivity,
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
    have hl := hc.continuousAt.tendsto.comp
      (weakMix_tendsto p q w tendsto_one_div_add_atTop_nhds_zero_nat)
    obtain ⟨n, hn⟩ := (hl.eventually (Metric.ball_mem_nhds (u p) zero_lt_one)).exists
    change dist (u (Mix (w n) (q n) p)) (u p) < 1 at hn
    rw [Real.dist_eq, ha, show (w n).val * u (q n) + (1 - (w n).val) * u p - u p =
      (w n).val * (u (q n) - u p) by ring, abs_mul, abs_of_nonneg (w n).property.1] at hn
    have hd : 0 < (n : ℝ) + 1 := by positivity
    change 1 / ((n : ℝ) + 1) * |u (q n) - u p| < 1 at hn
    rw [one_div_mul_eq_div, div_lt_one hd] at hn
    exact (hq n).not_gt hn
  · exact ⟨0, fun p => (hi ⟨p⟩).elim⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Expected utility on all Borel probability measures

Kreps I, Proposition 5.10, pp. 98–100. The proof works on second-countable metric
prize spaces with their Borel sets, including finite-dimensional real space and
its nonnegative orthant. Utility on prizes is evaluated at Dirac laws. Weak
continuity and approximation extend its integral representation to every law.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity Filter
open scoped Topology BoundedContinuousFunction

attribute [local instance] BorelConvexSpace

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSingletonClass X]

/-- An affine weakly continuous index is the expectation of its values on Dirac laws. -/
theorem borel_index_is_integral {u : ProbabilityMeasure X → ℝ} (hc : Continuous u)
    (ha : AffineInMix u) : ∃ U : X →ᵇ ℝ, (∀ x, U x = u (diracProba x)) ∧
      ∀ p : ProbabilityMeasure X, u p = ∫ x, U x ∂(p : Measure X) := by
  obtain ⟨C, hC⟩ := continuous_affine_bounded hc ha
  let U : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => u (diracProba x), hc.comp continuous_diracProba⟩ (C + C) (by
      intro x y
      change |u (diracProba x) - u (diracProba y)| ≤ C + C
      exact (abs_sub _ _).trans (add_le_add (hC _) (hC _)))
  refine ⟨U, fun _ => rfl, fun p => ?_⟩
  obtain ⟨q, hq⟩ := exists_simpleLotteries_tendsto p
  have h₁ := hc.continuousAt.tendsto.comp hq
  have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U).continuousAt
    |>.tendsto.comp hq
  have he (n : ℕ) : u (AtomicProbability (q n)) =
      ∫ x, U x ∂(AtomicProbability (q n) : Measure X) := by
    rw [affineInMix_atomicProbability ha, integral_atomicProbability]
    rfl
  exact tendsto_nhds_unique (h₁.congr (fun n => he n)) h₂

/-- Proposition 5.10. Weak continuity and the mixture axioms characterize bounded continuous EU. -/
theorem proposition_5_10 {r : ProbabilityMeasure X → ProbabilityMeasure X → Prop} :
    MixtureAxioms r ∧ OpenStrictSections r ↔
      ∃ U : X →ᵇ ℝ, Represents (fun p : ProbabilityMeasure X => ∫ x, U x ∂(p : Measure X)) r := by
  constructor
  · rintro ⟨hm, hw⟩
    obtain ⟨u, hr, ha⟩ := proposition_5_4.mp hm
    have hc := (openStrictSections_iff_continuous hr ha).mp hw
    obtain ⟨U, _, he⟩ := borel_index_is_integral hc ha
    exact ⟨U, fun p q => by simpa only [← he p, ← he q] using hr p q⟩
  · rintro ⟨U, hr⟩
    have ha := integral_affineInMix U
    exact ⟨proposition_5_4.mpr ⟨_, hr, ha⟩, (openStrictSections_iff_continuous hr ha).mpr
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U)⟩

/-- The proposition applies to Borel laws on the book's full Euclidean commodity space. -/
theorem proposition_5_10_euclidean (k : ℕ) {r : ProbabilityMeasure (Fin k → ℝ) →
    ProbabilityMeasure (Fin k → ℝ) → Prop} :
    MixtureAxioms r ∧ OpenStrictSections r ↔
      ∃ U : (Fin k → ℝ) →ᵇ ℝ, Represents (fun p : ProbabilityMeasure (Fin k → ℝ) =>
        ∫ x, U x ∂(p : Measure (Fin k → ℝ))) r := proposition_5_10

/-- The proposition also applies on the closed nonnegative orthant, including its boundary. -/
theorem proposition_5_10_orthant (k : ℕ) :
    let X := {x : Fin k → ℝ // 0 ≤ x}
    ∀ r : ProbabilityMeasure X → ProbabilityMeasure X → Prop,
      MixtureAxioms r ∧ OpenStrictSections r ↔
        ∃ U : X →ᵇ ℝ, Represents (fun p : ProbabilityMeasure X => ∫ x, U x ∂(p : Measure X)) r :=
  fun _ => proposition_5_10

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite lottery diagrams

Kreps I, Definition 5.2 and Figures 5.2–5.11, pp. 85–117. Branches can lead
to the same prize. Pushing the branch probabilities forward adds their masses
and produces a finitely supported lottery on the original prize space.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- A finite branch table carries nonnegative probabilities summing to one. -/
structure BranchTable (n : ℕ) where
  /-- The probability written on each branch. -/
  mass : Fin n → ℝ
  /-- Each branch has nonnegative probability. -/
  nonnegative : ∀ i, 0 ≤ mass i
  /-- The probabilities sum to one. -/
  normalized : ∑ i, mass i = 1

/-- The probability distribution on the branch indices themselves. -/
noncomputable def BranchTable.distribution {n : ℕ} (p : BranchTable n) :
    Convexity.StdSimplex ℝ (Fin n) where
  weights := Finsupp.equivFunOnFinite.symm p.mass
  nonneg := fun i => by simpa using p.nonnegative i
  total := by simpa [Finsupp.sum_fintype] using p.normalized

/-- The actual prize lottery, with all branches leading to the same prize merged. -/
noncomputable def BranchTable.lottery {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) : Convexity.StdSimplex ℝ X := p.distribution.map prize

/-- Evaluation of a lottery diagram at any utility, before collecting equal prizes. -/
noncomputable def BranchTable.value {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) : ℝ := ∑ i, p.mass i * U (prize i)

/-- Summing utility on the reduced prize distribution gives exactly the diagram's value. -/
theorem BranchTable.lottery_value {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) :
    (p.lottery prize).weights.sum (fun x t => t * U x) = p.value prize U := by
  classical
  unfold BranchTable.lottery
  rw [Convexity.StdSimplex.weights_map, Finsupp.sum_mapDomain_index (by simp)
    (by intro b x y; exact add_mul x y (U b))]
  simp [BranchTable.distribution, Finsupp.sum_fintype, BranchTable.value]

/-- A diagram can be evaluated directly through the chapter's expected-utility interface. -/
theorem expectedUtility_branchLottery {n : ℕ} {X : Type*} (p : BranchTable n)
    (prize : Fin n → X) (U : X → ℝ) :
    ExpectedUtility U (p.lottery prize) = p.value prize U := p.lottery_value prize U

/-- The probability table for a sure prize. -/
def CertainBranch : BranchTable 1 := ⟨![1], by intro i; fin_cases i; norm_num,
  by norm_num [Fin.sum_univ_succ]⟩

/-- A two-branch lottery with an arbitrary admissible first probability. -/
noncomputable def TwoBranches (a : ℝ) (ha : a ∈ Set.Icc 0 1) : BranchTable 2 :=
  ⟨![a, 1 - a], by intro i; fin_cases i <;> simp [ha.1, ha.2], by simp [Fin.sum_univ_two]⟩

/-- The value of a sure prize is its utility. -/
theorem certainBranch_value {X : Type*} (x : X) (U : X → ℝ) :
    CertainBranch.value (fun _ => x) U = U x := by
  simp [BranchTable.value, CertainBranch]

/-- A two-branch diagram gives the usual binary expectation formula. -/
theorem twoBranches_value {X : Type*} (a : ℝ) (ha : a ∈ Set.Icc 0 1)
    (x y : X) (U : X → ℝ) :
    (TwoBranches a ha).value ![x, y] U = a * U x + (1 - a) * U y := by
  simp [TwoBranches, BranchTable.value, Fin.sum_univ_two]

/-- Three labeled branches with explicitly certified probabilities. -/
noncomputable def ThreeBranches (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : BranchTable 3 :=
  ⟨![a, b, c], by intro i; fin_cases i <;> assumption,
    by simpa [Fin.sum_univ_succ, add_assoc] using h⟩

/-- The evaluation rule for a three-branch diagram, including repeated prizes. -/
theorem threeBranches_value {X : Type*} (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : a + b + c = 1) (x y z : X) (U : X → ℝ) :
    (ThreeBranches a b c ha hb hc h).value ![x, y, z] U =
      a * U x + b * U y + c * U z := by
  simp [BranchTable.value, ThreeBranches, Fin.sum_univ_succ, add_assoc]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Framing, Allais, Ellsberg, portfolio effects and timing

Kreps I, Section 5.5, pp. 110–116. These results check the mathematical
implications of each experiment. A reported frequency of human choices is
empirical evidence. The portfolio comparison uses a constructed illustration.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- A binary cash lottery paying `x` and `y` at the specified odds. -/
noncomputable def BinaryCash (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (x y : ℝ) : SimpleLottery ℝ :=
  (TwoBranches a ha).lottery ![x, y]

/-- Value of the two cash prizes for an arbitrary numerical utility. -/
theorem binaryCash_expectedUtility (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (x y : ℝ) (U : ℝ → ℝ) :
    ExpectedUtility U (BinaryCash a ha x y) = a * U x + (1 - a) * U y := by
  rw [BinaryCash, expectedUtility_branchLottery]
  exact twoBranches_value a ha x y U

/-- Both the sure and the risky choices on p. 111 give exactly the same terminal cash laws. -/
theorem framing_cash_laws :
    PureLottery (400 : ℝ) = PureLottery (600 - 200 : ℝ) ∧
    BinaryCash (2 / 3) (by constructor <;> norm_num) 600 0 =
      BinaryCash (2 / 3) (by constructor <;> norm_num) (600 - 0) (600 - 600) := by
  norm_num

/-- Preferences on terminal monetary laws cannot reverse the two equivalent presentations. -/
theorem framing_no_strict_reversal (r : SimpleLottery ℝ → SimpleLottery ℝ → Prop) :
    ¬(Strict r (PureLottery 400) (BinaryCash (2 / 3) (by constructor <;> norm_num) 600 0) ∧
      Strict r (BinaryCash (2 / 3) (by constructor <;> norm_num) (600 - 0) (600 - 600))
        (PureLottery (600 - 200))) := by
  rw [← framing_cash_laws.1, ← framing_cash_laws.2]
  exact fun h => h.1.2 h.2.1

/-- The four Figure 5.9 lotteries in order `A`, `B`, `A'`, `B'`. -/
noncomputable def AllaisLotteries : Fin 4 → SimpleLottery ℝ :=
  ![(ThreeBranches (33 / 100) (66 / 100) (1 / 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).lottery ![27500, 24000, 0],
    PureLottery 24000, BinaryCash (33 / 100) (by constructor <;> norm_num) 27500 0,
    BinaryCash (34 / 100) (by constructor <;> norm_num) 24000 0]

/-- The two Allais comparisons have exactly the same expected-utility difference. -/
theorem allais_difference (U : ℝ → ℝ) :
    ExpectedUtility U (AllaisLotteries 0) - ExpectedUtility U (AllaisLotteries 1) =
    ExpectedUtility U (AllaisLotteries 2) - ExpectedUtility U (AllaisLotteries 3) := by
  simp [AllaisLotteries, expectedUtility_branchLottery, threeBranches_value, expectedUtility_pure,
    binaryCash_expectedUtility]
  ring

/-- The reported strict pair `B > A` and `A' > B'` excludes every expected utility. -/
theorem allais_no_expectedUtility : ¬∃ U : ℝ → ℝ,
    ExpectedUtility U (AllaisLotteries 1) > ExpectedUtility U (AllaisLotteries 0) ∧
    ExpectedUtility U (AllaisLotteries 2) > ExpectedUtility U (AllaisLotteries 3) := by
  rintro ⟨U, h, h'⟩
  linarith [allais_difference U]

/-- The Ellsberg acts on the red, blue and green states, in order `A`, `B`, `A'`, `B'`. -/
def EllsbergBets : Fin 4 → Fin 3 → ℝ :=
  ![![100, 0, 0], ![0, 100, 0], ![100, 0, 100], ![0, 100, 100]]

/-- For every possible blue count from zero to 200, this is the corresponding urn law. -/
noncomputable def EllsbergUrn (blue : ℕ) (h : blue ≤ 200) : BranchTable 3 :=
  ThreeBranches (1 / 3) (blue / 300) ((200 - (blue : ℝ)) / 300) (by norm_num)
    (by positivity) (by
      have h' : (blue : ℝ) ≤ 200 := by exact_mod_cast h
      linarith) (by ring)

/-- The known probabilities are one third for red and two thirds for blue or green. -/
theorem ellsberg_known_odds (blue : ℕ) (h : blue ≤ 200) :
    (EllsbergUrn blue h).mass 0 = 1 / 3 ∧
    (EllsbergUrn blue h).mass 1 + (EllsbergUrn blue h).mass 2 = 2 / 3 := by
  constructor <;> simp [EllsbergUrn, ThreeBranches]
  ring

/-- The two Ellsberg gaps coincide for arbitrary subjective probabilities and prize utility. -/
theorem ellsberg_difference (p : Fin 3 → ℝ) (U : ℝ → ℝ) :
    SubjectiveActValue p U (EllsbergBets 0) - SubjectiveActValue p U (EllsbergBets 1) =
    SubjectiveActValue p U (EllsbergBets 2) - SubjectiveActValue p U (EllsbergBets 3) := by
  simp [SubjectiveActValue, EllsbergBets, Fin.sum_univ_succ]
  ring

/-- The reported strict reversal excludes subjective expected utility for every assignment. -/
theorem ellsberg_no_subjectiveUtility : ¬∃ (p : Fin 3 → ℝ) (U : ℝ → ℝ),
    SubjectiveActValue p U (EllsbergBets 0) > SubjectiveActValue p U (EllsbergBets 1) ∧
    SubjectiveActValue p U (EllsbergBets 3) > SubjectiveActValue p U (EllsbergBets 2) := by
  rintro ⟨p, U, h, h'⟩
  linarith [ellsberg_difference p U]

/-- The Ellsberg reversal violates Savage's Sure-Thing Principle directly on acts. -/
theorem ellsberg_not_sureThing {r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop}
    (h : Strict r (EllsbergBets 0) (EllsbergBets 1))
    (h' : Strict r (EllsbergBets 3) (EllsbergBets 2)) : ¬SureThing r := by
  intro hS
  apply h'.2
  apply (hS {0, 1} (EllsbergBets 0) (EllsbergBets 2) (EllsbergBets 1) (EllsbergBets 3)
    (by intro s hs; fin_cases s <;> norm_num [EllsbergBets] at *)
    (by intro s hs; fin_cases s <;> norm_num [EllsbergBets] at *)).mp h.1

/-- Identical investment payoffs can be valued differently when combined with existing wealth. -/
theorem portfolio_dependence_example :
    ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) 0 100) =
      ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) 100 0) ∧
    ExpectedUtility Real.sqrt (BinaryCash (1 / 2) (by constructor <;> norm_num) (0 + 100)
      (100 + 0)) > ExpectedUtility Real.sqrt
        (BinaryCash (1 / 2) (by constructor <;> norm_num) (0 + 0) (100 + 100)) := by
  have h : Real.sqrt 200 < 20 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  norm_num [binaryCash_expectedUtility]
  linarith

/-- The narrow terminal-prize model values each p. 115 timing variant by this same comparison. -/
theorem delayedCoin_value_iff (U : ℝ → ℝ) :
    ExpectedUtility U (PureLottery 20000) ≤ ExpectedUtility U
        (BinaryCash (1 / 2) (by constructor <;> norm_num) 100000 0) ↔
      2 * U 20000 ≤ U 100000 + U 0 := by
  rw [expectedUtility_pure, binaryCash_expectedUtility]
  constructor <;> intro h <;> linarith

/-- Coin offer with draw, disclosure and payment dates (months) and monetary consequences. -/
structure TimedCoinOffer where
  /-- Month of the actual coin toss. -/
  draw : ℕ
  /-- Month in which the consumer learns its outcome. -/
  disclosure : ℕ
  /-- Month in which the terminal amount is paid. -/
  payment : ℕ
  /-- Payoff after heads. -/
  heads : ℝ
  /-- Payoff after tails. -/
  tails : ℝ

/-- The three timing arrangements on p. 115 differ in when the fair toss occurs or is disclosed. -/
def PrintedCoinOffers : Fin 3 → TimedCoinOffer :=
  ![⟨0, 0, 12, 100000, 0⟩, ⟨12, 12, 12, 100000, 0⟩, ⟨0, 12, 12, 100000, 0⟩]

/-- All three contracts give the identical terminal law and comparison against the sure payment. -/
theorem printedCoinOffers_compare (i : Fin 3) (U : ℝ → ℝ) :
    let c := PrintedCoinOffers i
    ExpectedUtility U (PureLottery 20000) ≤ ExpectedUtility U
        (BinaryCash (1 / 2) (by constructor <;> norm_num) c.heads c.tails) ↔
      2 * U 20000 ≤ U 100000 + U 0 := by
  fin_cases i <;> exact delayedCoin_value_iff U

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Compound lotteries and the order of randomization

Kreps I, Figures 5.5–5.7, pp. 87, 102–103, and the steak/chicken comparison
on p. 106. The numerical reductions are proved as equalities of probability
distributions on prizes. Distributions on entire acts retain their correlations.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- An indicator payoff recovers the mass of the corresponding prize. -/
theorem expectedUtility_indicator {X : Type*} [DecidableEq X] (p : SimpleLottery X) (x : X) :
    ExpectedUtility (fun y => if y = x then 1 else 0) p = p.weights x := by
  classical
  unfold ExpectedUtility
  rw [Finsupp.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- Equality of all expected utilities separates actual prize distributions. -/
theorem lottery_eq_of_all_values {X : Type*} {p q : SimpleLottery X}
    (h : ∀ U : X → ℝ, ExpectedUtility U p = ExpectedUtility U q) : p = q := by
  classical
  apply Convexity.StdSimplex.ext
  ext x
  simpa only [expectedUtility_indicator] using h (fun y => if y = x then 1 else 0)

/-- Four explicit masses for the reduced lottery in Figure 5.5. -/
noncomputable def Figure55Reduced : BranchTable 4 :=
  ⟨![1 / 2, 1 / 30, 1 / 5, 4 / 15], by intro i; fin_cases i <;> norm_num,
    by norm_num [Fin.sum_univ_succ]⟩

/-- Figure 5.5 combines two lottery diagrams, merging their common prize. -/
theorem figure55_reduction :
    Mix ⟨1 / 3, by constructor <;> norm_num⟩
        ((ThreeBranches (3 / 10) (1 / 10) (6 / 10) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).lottery (![0, 1, 2] : Fin 3 → Fin 4))
        ((TwoBranches (3 / 5) (by constructor <;> norm_num)).lottery ![0, 3]) =
      Figure55Reduced.distribution := by
  apply lottery_eq_of_all_values
  intro U
  rw [expectedUtility_affine U, expectedUtility_branchLottery, expectedUtility_branchLottery,
    expectedUtility_eq_sum]
  norm_num [Figure55Reduced, BranchTable.distribution, ThreeBranches, TwoBranches,
    BranchTable.value, Fin.sum_univ_succ]
  ring

/-- Figure 5.6(a,c): the same deterministic act as statewise sure roulette prizes. -/
theorem figure56_deterministic (U : ℝ → ℝ) (s : Fin 3) :
    ExpectedUtility U (PureLottery ((![1, -2, 0] : Fin 3 → ℝ) s)) =
      U ((![1, -2, 0] : Fin 3 → ℝ) s) := expectedUtility_pure _ _

/-- Figure 5.6(b), also the first lottery in Figure 5.7. -/
noncomputable def Figure57First : HorseLottery (Fin 3) ℝ :=
  ![PureLottery (-2), BinaryCash (1 / 2) (by constructor <;> norm_num) 3 1,
    BinaryCash (1 / 3) (by constructor <;> norm_num) 6 (-4)]

/-- The second Figure 5.7 lottery. -/
noncomputable def Figure57Second : HorseLottery (Fin 3) ℝ :=
  ![BinaryCash (1 / 2) (by constructor <;> norm_num) (-2) 5, PureLottery 5,
    BinaryCash (1 / 2) (by constructor <;> norm_num) 6 3]

/-- Statewise reduced probabilities printed in the final panel of Figure 5.7. -/
noncomputable def Figure57Reduced : HorseLottery (Fin 3) ℝ :=
  ![BinaryCash (7 / 8) (by constructor <;> norm_num) (-2) 5,
    (ThreeBranches (3 / 8) (3 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![3, 1, 5],
    (ThreeBranches (3 / 8) (1 / 2) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![6, -4, 3]]

/-- Figure 5.7 is an equality of horse-race lotteries, including repeated prizes in each state. -/
theorem figure57_reduction :
    Mix ⟨3 / 4, by constructor <;> norm_num⟩ Figure57First Figure57Second = Figure57Reduced := by
  funext s
  rw [mix_act_apply]
  apply lottery_eq_of_all_values
  intro U
  rw [expectedUtility_affine U]
  fin_cases s <;> norm_num [Figure57First, Figure57Second, Figure57Reduced, expectedUtility_pure,
    binaryCash_expectedUtility, expectedUtility_branchLottery, threeBranches_value] <;> ring

/-- A deterministic steak/chicken menu across two states, with true denoting steak. -/
noncomputable def DinnerAct (a b : Bool) : HorseLottery (Fin 2) Bool := ![PureLottery a,
  PureLottery b]

/-- Mixtures of matching dinners and mixtures of opposite dinners coincide state by state. -/
theorem dinner_horses_first :
    Mix ⟨1 / 2, by constructor <;> norm_num⟩ (DinnerAct true true) (DinnerAct false false) =
      Mix ⟨1 / 2, by constructor <;> norm_num⟩ (DinnerAct true false) (DinnerAct false true) := by
  funext s
  simp only [mix_act_apply]
  fin_cases s
  · rfl
  · apply lottery_eq_of_all_values
    intro U
    rw [expectedUtility_affine U, expectedUtility_affine U]
    simp [DinnerAct, expectedUtility_pure]
    ring

/-- A state-complementary prize value on an entire deterministic dinner plan. -/
def MatchingDinnerValue (h : Fin 2 → Bool) : ℝ := if h 0 = h 1 then 1 else 0

/-- Roulette first can distinguish the two joint laws that horses-first mixing identifies. -/
theorem dinner_roulette_first :
    ExpectedUtility MatchingDinnerValue
      ((TwoBranches (1 / 2) (by constructor <;> norm_num)).lottery
        ![(![true, true] : Fin 2 → Bool), ![false, false]]) = 1 ∧
    ExpectedUtility MatchingDinnerValue
      ((TwoBranches (1 / 2) (by constructor <;> norm_num)).lottery
        ![(![true, false] : Fin 2 → Bool), ![false, true]]) = 0 := by
  norm_num [expectedUtility_branchLottery, twoBranches_value, MatchingDinnerValue]

/-- The joint dinner-plan payoff cannot be expressed by a sum of two single-state payoffs. -/
theorem dinner_not_stateAdditive :
    ¬∃ U : Fin 2 → Bool → ℝ, ∀ h, MatchingDinnerValue h = StateAdditiveValue U h := by
  rintro ⟨U, h⟩
  have a := h ![true, true]
  have b := h ![false, false]
  have c := h ![true, false]
  have d := h ![false, true]
  norm_num [MatchingDinnerValue, StateAdditiveValue, Fin.sum_univ_two] at a b c d
  linarith

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Simple acts on an algebra of state events

Kreps I, Problem 5.6, pp. 119–122. An act factors through a finite partition
whose cells belong to the given algebra. Intersections supply common refinements.
This works for arbitrary state and prize types and allows empty partition cells.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity MeasureTheory

variable {S X Y Z : Type*} {A : Set (Set S)}

/-- A finite partition representation with an algebra event for each cell. -/
def IsEventSimple (A : Set (Set S)) (h : S → X) : Prop :=
  ∃ (n : ℕ) (cell : S → Fin n) (outcome : Fin n → X),
    (∀ i, {s | cell s = i} ∈ A) ∧ ∀ s, h s = outcome (cell s)

/-- A partition indexed by any finite type can be renumbered by consecutive natural numbers. -/
theorem isEventSimple_of_partition {I : Type*} [Finite I] (cell : S → I) (outcome : I → X)
    (hc : ∀ i, {s | cell s = i} ∈ A) : IsEventSimple A (fun s => outcome (cell s)) := by
  classical
  let _ := Fintype.ofFinite I
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun s => e (cell s), fun i => outcome (e.symm i), ?_, ?_⟩
  · intro i
    convert hc (e.symm i) using 1
    ext s
    exact e.eq_symm_apply.symm
  · intro s
    simp

/-- A constant act has the one-cell partition. -/
theorem isEventSimple_const (hA : IsSetAlgebra A) (x : X) : IsEventSimple A (fun _ => x) := by
  apply isEventSimple_of_partition (fun _ : S => ()) (fun _ => x)
  intro i
  simpa using hA.univ_mem

/-- A pointwise binary operation on simple acts uses the intersection of their partition cells. -/
theorem isEventSimple_map₂ (hA : IsSetAlgebra A) {h : S → X} {g : S → Y}
    (hh : IsEventSimple A h) (hg : IsEventSimple A g) (f : X → Y → Z) :
    IsEventSimple A (fun s => f (h s) (g s)) := by
  obtain ⟨n, c, v, hc, hv⟩ := hh
  obtain ⟨m, d, w, hd, hw⟩ := hg
  have hcell (i : Fin n × Fin m) :
      {s | (c s, d s) = i} = {s | c s = i.1} ∩ {s | d s = i.2} := by
    ext s
    simp [Prod.ext_iff]
  have H := isEventSimple_of_partition (fun s => (c s, d s)) (fun i => f (v i.1) (w i.2))
    (fun i => hcell i ▸ hA.inter_mem (hc i.1) (hd i.2))
  simpa only [hv, hw] using H

/-- Indicators of algebra events are simple functions. -/
theorem isEventSimple_indicator (hA : IsSetAlgebra A) {E : Set S} (hE : E ∈ A) :
    IsEventSimple A (fun s => @decide (s ∈ E) (Classical.propDecidable _)) := by
  classical
  have hc (i : Bool) : {s | decide (s ∈ E) = i} ∈ A := by
    cases i
    · convert hA.compl_mem hE using 1
      ext s
      simp
    · simpa using hE
  simpa using isEventSimple_of_partition (fun s => decide (s ∈ E)) id hc

/-- Pasting any two simple acts across an algebra event produces another simple act. -/
theorem isEventSimple_paste (hA : IsSetAlgebra A) {E : Set S} (hE : E ∈ A)
    {h g : S → X} (hh : IsEventSimple A h) (hg : IsEventSimple A g) :
    IsEventSimple A (fun s => @ite X (s ∈ E) (Classical.propDecidable _) (h s) (g s)) := by
  classical
  have H := isEventSimple_map₂ hA (isEventSimple_indicator hA hE)
    (isEventSimple_map₂ hA hh hg Prod.mk) (fun b (q : X × X) => if b then q.1 else q.2)
  simpa using H

/-- The space of doubly simple acts: finite algebra partitions and finitely supported prizes. -/
abbrev EventAct (A : Set (Set S)) (X : Type*) := {h : S → SimpleLottery X // IsEventSimple A h}

/-- Any algebra-simple act can be mixed state by state with any other such act. -/
theorem eventAct_isConvex (hA : IsSetAlgebra A) :
    IsConvexSet ℝ {h : S → SimpleLottery X | IsEventSimple A h} := by
  apply IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab h hh g hg
  have H := isEventSimple_map₂ hA hh hg (convexCombPair a b ha hb hab)
  change IsEventSimple A (convexCombPair a b ha hb hab h g)
  simpa only [← Pi.convexCombPair_apply] using H

/-- The actual mixture-space structure on the source's doubly simple acts. -/
noncomputable abbrev eventActConvexSpace (hA : IsSetAlgebra A) :
    ConvexSpace ℝ (EventAct A X) := .subtype _ (eventAct_isConvex hA)

/-- A roulette lottery offered independently of the state. -/
noncomputable def EventConstant (hA : IsSetAlgebra A) (q : SimpleLottery X) : EventAct A X :=
  ⟨fun _ => q, isEventSimple_const hA q⟩

/-- Replace the reference lottery on an arbitrary event by the corresponding part of an act. -/
noncomputable def EventCut (hA : IsSetAlgebra A) (base : SimpleLottery X)
    (E : Set S) (hE : E ∈ A) (h : EventAct A X) : EventAct A X := by
  classical
  exact ⟨fun s => if s ∈ E then h.val s else base,
    isEventSimple_paste hA hE h.property (isEventSimple_const hA base)⟩

/-- Membership in an event chooses the act's value, with baseline on its complement. -/
theorem eventCut_apply (hA : IsSetAlgebra A) (base : SimpleLottery X)
    (E : Set S) (hE : E ∈ A) (h : EventAct A X) (s : S) [Decidable (s ∈ E)] :
    (EventCut hA base E hE h).val s = if s ∈ E then h.val s else base := by
  classical
  by_cases hs : s ∈ E <;> simp [EventCut, hs]

/-- The convex-space instance mixes the actual conditional roulette lotteries pointwise. -/
theorem eventAct_mix_apply (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) (s : S) :
    letI := eventActConvexSpace (X := X) hA
    (Mix a h g).val s = Mix a (h.val s) (g.val s) := by
  let _ := eventActConvexSpace (X := X) hA
  calc
    _ = Mix a h.val g.val s := congrFun (subtypeVal_convexCombPair _
      (eventAct_isConvex hA) a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
      (by ring) h g) s
    _ = _ := mix_act_apply a h.val g.val s

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Event contributions of affine utility on simple acts

Kreps I, Problem 5.6(a–c), pp. 120–121. A midpoint identity splits the value
increment on disjoint events. Induction gives the formula for every finite
partition, including further refinements within cells. Preferences satisfy
Savage's Sure-Thing Principle on the given algebra.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- Statewise mixture of two doubly simple acts on the fixed algebra. -/
noncomputable def EventMix (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) :
    EventAct A X := @Mix _ (eventActConvexSpace hA) a h g

/-- The mixture at a state is its ordinary roulette mixture. -/
theorem eventMix_apply (hA : IsSetAlgebra A) (a : Weight) (h g : EventAct A X) (s : S) :
    (EventMix hA a h g).val s = Mix a (h.val s) (g.val s) := eventAct_mix_apply hA a h g s

/-- Binary mixture affinity on the actual simple-act domain. -/
def EventAffine (hA : IsSetAlgebra A) (F : EventAct A X → ℝ) : Prop :=
  ∀ a h g, F (EventMix hA a h g) = a.val * F h + (1 - a.val) * F g

/-- **Problem 5.6(a):** primitive mixture axioms give a representing affine functional. -/
theorem problem_5_6a (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop) :
    @MixtureAxioms _ (eventActConvexSpace hA) r ↔ ∃ F, Represents F r ∧ EventAffine hA F :=
  @proposition_5_4 _ (eventActConvexSpace hA) r

/-- The value contributed on an event relative to the constant reference act. -/
noncomputable def EventContribution (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (h : EventAct A X) : ℝ :=
  F (EventCut hA base E hE h) - F (EventConstant hA base)

/-- Equal events have equal contributions, independently of the proofs of admissibility. -/
theorem eventContribution_congr_event (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) {E D : Set S} (hE : E ∈ A) (hD : D ∈ A) (h : EventAct A X)
    (he : E = D) : EventContribution hA F b E hE h = EventContribution hA F b D hD h := by
  subst D
  rfl

/-- An empty event makes no change to the reference act. -/
theorem eventContribution_empty (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) (h : EventAct A X) :
    EventContribution hA F b ∅ hA.empty_mem h = 0 := by
  have he : EventCut hA b ∅ hA.empty_mem h = EventConstant hA b := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply, EventConstant]
  simp [EventContribution, he]

/-- On the universal event the contribution is the act's entire value increment. -/
theorem eventContribution_univ (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) (h : EventAct A X) :
    EventContribution hA F b Set.univ hA.univ_mem h = F h - F (EventConstant hA b) := by
  have he : EventCut hA b Set.univ hA.univ_mem h = h := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply]
  simp [EventContribution, he]

/-- Contributions agree whenever the underlying acts agree on the event. -/
theorem eventContribution_congr_act (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (b : SimpleLottery X) {E : Set S} (hE : E ∈ A) (h g : EventAct A X)
    (he : ∀ s ∈ E, h.val s = g.val s) :
    EventContribution hA F b E hE h = EventContribution hA F b E hE g := by
  classical
  have hc : EventCut hA b E hE h = EventCut hA b E hE g := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E
    · simp [eventCut_apply, hs, he s hs]
    · simp [eventCut_apply, hs]
  simp only [EventContribution, hc]

/-- Affine utility adds increments on arbitrary disjoint algebra events. -/
theorem eventContribution_union (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (b : SimpleLottery X) {E D : Set S}
    (hE : E ∈ A) (hD : D ∈ A) (hd : Disjoint E D) (h : EventAct A X) :
    EventContribution hA F b (E ∪ D) (hA.union_mem hE hD) h =
      EventContribution hA F b E hE h + EventContribution hA F b D hD h := by
  classical
  let a : Weight := ⟨1 / 2, by constructor <;> norm_num⟩
  have hsym (x y : SimpleLottery X) : Mix a x y = Mix a y x := by
    have hc : Complement a = a := by ext; norm_num [Complement, a]
    rw [mix_swap a x y, hc]
  have he : EventMix hA a (EventCut hA b E hE h) (EventCut hA b D hD h) =
      EventMix hA a (EventCut hA b (E ∪ D) (hA.union_mem hE hD) h) (EventConstant hA b) := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E
    · have ht : s ∉ D := Set.disjoint_left.mp hd hs
      simp [eventMix_apply, eventCut_apply, EventConstant, hs, ht]
    · by_cases ht : s ∈ D <;> simp [eventMix_apply, eventCut_apply, EventConstant, hs, ht, hsym]
  have h₁ := ha a (EventCut hA b E hE h) (EventCut hA b D hD h)
  have h₂ := ha a (EventCut hA b (E ∪ D) (hA.union_mem hE hD) h) (EventConstant hA b)
  rw [he] at h₁
  dsimp only [a] at h₁ h₂
  unfold EventContribution
  linarith

/-- The union of a finite family of partition cells is an algebra event. -/
theorem partitionUnion_mem {I : Type*} (hA : IsSetAlgebra A) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (T : Finset I) : {s | c s ∈ T} ∈ A := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hA.empty_mem
  | @insert i T _ ih =>
    convert hA.union_mem (hc i) ih using 1
    ext s
    simp

/-- The contribution on any finite union of cells is the sum of the cell contributions. -/
theorem eventContribution_partitionUnion {I : Type*} (hA : IsSetAlgebra A)
    {F : EventAct A X → ℝ} (ha : EventAffine hA F) (b : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (T : Finset I) (h : EventAct A X) :
    EventContribution hA F b {s | c s ∈ T} (partitionUnion_mem hA c hc T) h =
      ∑ i ∈ T, EventContribution hA F b {s | c s = i} (hc i) h := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, eventContribution_congr_event hA F b _ hA.empty_mem h (by ext; simp),
      eventContribution_empty]
  | @insert i T hi ih =>
    have he : {s | c s ∈ insert i T} = {s | c s = i} ∪ {s | c s ∈ T} := by ext; simp
    have hd : Disjoint {s | c s = i} {s | c s ∈ T} := by
      apply Set.disjoint_left.mpr
      intro s hs ht
      exact hi (hs ▸ ht)
    rw [eventContribution_congr_event hA F b _ (hA.union_mem (hc i)
      (partitionUnion_mem hA c hc T)) h he,
      eventContribution_union hA ha b (hc i) (partitionUnion_mem hA c hc T) hd,
      ih, Finset.sum_insert hi]

/-- **Problem 5.6(b):** finite-partition additivity also covers every further cell refinement. -/
theorem problem_5_6b {I : Type*} [Fintype I] (hA : IsSetAlgebra A)
    {F : EventAct A X → ℝ} (ha : EventAffine hA F) (b : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (h : EventAct A X) :
    F h - F (EventConstant hA b) = ∑ i, EventContribution hA F b {s | c s = i} (hc i) h := by
  have he : {s | c s ∈ (Finset.univ : Finset I)} = Set.univ := by ext; simp
  rw [← eventContribution_univ hA F b h,
    ← eventContribution_congr_event hA F b (partitionUnion_mem hA c hc Finset.univ) _ h he]
  exact eventContribution_partitionUnion hA ha b c hc _ h

/-- Splitting at an event and its complement exactly decomposes the value increment. -/
theorem eventContribution_complement (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (b : SimpleLottery X) {E : Set S} (hE : E ∈ A) (h : EventAct A X) :
    F h - F (EventConstant hA b) = EventContribution hA F b E hE h +
      EventContribution hA F b Eᶜ (hA.compl_mem hE) h := by
  rw [← eventContribution_union hA ha b hE (hA.compl_mem hE) disjoint_compl_right,
    eventContribution_congr_event hA F b _ hA.univ_mem h (Set.union_compl_self E),
    eventContribution_univ]

/-- **Problem 5.6(c):** replacement of common off-event consequences preserves the ranking. -/
theorem problem_5_6c (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (b : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) (f g f' g' : EventAct A X)
    (hin : ∀ s ∈ E, f.val s = f'.val s ∧ g.val s = g'.val s)
    (hout : ∀ s ∉ E, f.val s = g.val s ∧ f'.val s = g'.val s) : r f g ↔ r f' g' := by
  obtain ⟨F, hFr, hFa⟩ := (problem_5_6a hA r).mp hr
  have a := eventContribution_complement hA hFa b hE f
  have c := eventContribution_complement hA hFa b hE g
  have a' := eventContribution_complement hA hFa b hE f'
  have c' := eventContribution_complement hA hFa b hE g'
  have di := eventContribution_congr_act hA F b hE f f' (fun s hs => (hin s hs).1)
  have dj := eventContribution_congr_act hA F b hE g g' (fun s hs => (hin s hs).2)
  have ei := eventContribution_congr_act hA F b (hA.compl_mem hE) f g (fun s hs => (hout s hs).1)
  have ej := eventContribution_congr_act hA F b (hA.compl_mem hE) f' g' (fun s hs => (hout s hs).2)
  rw [hFr, hFr]
  constructor <;> intro h <;> linarith

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Conditional utility and finitely additive subjective odds

Kreps I, Problem 5.6(d,e), pp. 121–122. Conditional utility values every
roulette on an event relative to a constant reference. Its value at a globally
normalized better prize is finitely additive. Nonnegativity follows from its
*conditional* weak preference on every event.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- Value increment when roulette `q` replaces the reference roulette throughout one event. -/
noncomputable def EventLotteryIndex (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (q : SimpleLottery X) : ℝ :=
  EventContribution hA F base E hE (EventConstant hA q)

/-- Replacing a lottery by itself anywhere leaves the reference value unchanged. -/
theorem eventLotteryIndex_base (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) {E : Set S} (hE : E ∈ A) :
    EventLotteryIndex hA F base E hE base = 0 := by
  classical
  have he : EventCut hA base E hE (EventConstant hA base) = EventConstant hA base := by
    apply Subtype.ext
    funext s
    simp [eventCut_apply, EventConstant]
  simp [EventLotteryIndex, EventContribution, he]

/-- Conditional utility is itself affine on roulette lotteries. -/
theorem eventLotteryIndex_affine (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) {E : Set S} (hE : E ∈ A) :
    AffineInMix (EventLotteryIndex hA F base E hE) := by
  classical
  intro a p q
  have he : EventCut hA base E hE (EventConstant hA (Mix a p q)) =
      EventMix hA a (EventCut hA base E hE (EventConstant hA p))
        (EventCut hA base E hE (EventConstant hA q)) := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ E <;> simp [eventMix_apply, eventCut_apply, EventConstant, hs, mix_self]
  simp only [EventLotteryIndex, EventContribution, he]
  rw [ha a _ _]
  ring

/-- Event-specific prize utility is obtained by inserting a sure prize on that event. -/
noncomputable def EventPrizeUtility (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (x : X) : ℝ :=
  EventLotteryIndex hA F base E hE (PureLottery x)

/-- Every conditional roulette is evaluated by its event-specific expected prize utility. -/
theorem eventLotteryIndex_expectedUtility (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) {E : Set S} (hE : E ∈ A)
    (q : SimpleLottery X) :
    EventLotteryIndex hA F base E hE q = ExpectedUtility (EventPrizeUtility hA F base E hE) q :=
  affineInMix_eq_expectedUtility (eventLotteryIndex_affine hA ha base hE) q

/-- **Problem 5.6(d):** sum the event-specific expectations over any finite presentation. -/
theorem problem_5_6d {I : Type*} [Fintype I] (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    (ha : EventAffine hA F) (base : SimpleLottery X) (c : S → I)
    (hc : ∀ i, {s | c s = i} ∈ A) (q : I → SimpleLottery X) (h : EventAct A X)
    (hh : ∀ s, h.val s = q (c s)) :
    F h - F (EventConstant hA base) =
      ∑ i, ExpectedUtility (EventPrizeUtility hA F base {s | c s = i} (hc i)) (q i) := by
  rw [problem_5_6b hA ha base c hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eventLotteryIndex_expectedUtility hA ha]
  apply eventContribution_congr_act
  intro s hs
  change h.val s = q i
  rw [hh s, show c s = i from hs]

/-- The eventwise ranking takes identical reference consequences outside the event. -/
def EventRanking (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop)
    (base : SimpleLottery X) (E : Set S) (hE : E ∈ A) (q t : SimpleLottery X) : Prop :=
  r (EventCut hA base E hE (EventConstant hA q)) (EventCut hA base E hE (EventConstant hA t))

/-- Subtracting the common reference value preserves every conditional comparison. -/
theorem eventLotteryIndex_represents (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (base : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) :
    Represents (EventLotteryIndex hA F base E hE) (EventRanking hA r base E hE) := by
  intro q t
  unfold EventRanking EventLotteryIndex EventContribution
  rw [hF, sub_le_sub_iff_right]

/-- The conditional ranking on every event satisfies the three primitive mixture axioms. -/
theorem eventRanking_mixtureAxioms (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (base : SimpleLottery X)
    {E : Set S} (hE : E ∈ A) : MixtureAxioms (EventRanking hA r base E hE) := by
  obtain ⟨F, hFr, hFa⟩ := (problem_5_6a hA r).mp hr
  exact mixtureAxioms_of_representation (eventLotteryIndex_represents hA hFr base hE)
    (eventLotteryIndex_affine hA hFa base hE)

/-- The source's calibrated event weight, defined for every algebra event. -/
noncomputable def EventProbability (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base good : SimpleLottery X) (E : A) : ℝ := EventLotteryIndex hA F base E.val E.property good

/-- An event is null for the calibrating pair when the decision maker is indifferent on it. -/
def CalibrationNull (hA : IsSetAlgebra A) (r : EventAct A X → EventAct A X → Prop)
    (base good : SimpleLottery X) (E : A) : Prop :=
  Indifferent (EventRanking hA r base E.val E.property) good base

/-- A real-valued finitely additive probability on an event algebra. -/
def FinitelyAdditiveProbability (hA : IsSetAlgebra A) (p : A → ℝ) : Prop :=
  (∀ E, p E ∈ Set.Icc 0 1) ∧ p ⟨Set.univ, hA.univ_mem⟩ = 1 ∧ p ⟨∅, hA.empty_mem⟩ = 0 ∧
    ∀ E D : A, Disjoint E.val D.val →
      p ⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ = p E + p D

/-- Zero calibrated weight is exactly indifference on the event. -/
theorem eventProbability_zero_iff_null (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r)
    (base good : SimpleLottery X) (E : A) :
    EventProbability hA F base good E = 0 ↔ CalibrationNull hA r base good E := by
  have hr := eventLotteryIndex_represents hA hF base E.property
  unfold EventProbability CalibrationNull Indifferent
  rw [hr, hr, eventLotteryIndex_base]
  exact ⟨fun he => ⟨he.ge, he.le⟩, fun he => le_antisymm he.2 he.1⟩

/-- **Problem 5.6(e):** conditional weak preference makes the normalized weights probabilities. -/
theorem problem_5_6e (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (ha : EventAffine hA F)
    (base good : SimpleLottery X) (hn : F (EventConstant hA good) - F (EventConstant hA base) = 1)
    (hw : ∀ E : A, EventRanking hA r base E.val E.property good base) :
    FinitelyAdditiveProbability hA (EventProbability hA F base good) ∧
      ∀ E, EventProbability hA F base good E = 0 ↔ CalibrationNull hA r base good E := by
  let p := EventProbability hA F base good
  have whole : p ⟨Set.univ, hA.univ_mem⟩ = 1 :=
    (eventContribution_univ hA F base (EventConstant hA good)).trans hn
  have add (E D : A) (hd : Disjoint E.val D.val) :
      p ⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ = p E + p D :=
    eventContribution_union hA ha base E.property D.property hd (EventConstant hA good)
  have hnon (E : A) : 0 ≤ p E := by
    have h := (eventLotteryIndex_represents hA hF base E.property good base).mp (hw E)
    rwa [eventLotteryIndex_base] at h
  refine ⟨⟨fun E => ⟨hnon E, ?_⟩, whole, eventContribution_empty hA F base _, add⟩,
    eventProbability_zero_iff_null hA hF base good⟩
  let D : A := ⟨E.valᶜ, hA.compl_mem E.property⟩
  have hsum := add E D disjoint_compl_right
  have hset : (⟨E.val ∪ D.val, hA.union_mem E.property D.property⟩ : A) =
      ⟨Set.univ, hA.univ_mem⟩ := Subtype.ext (Set.union_compl_self _)
  rw [hset, whole] at hsum
  linarith [hnon D]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A common utility and subjective probabilities on an event algebra

Kreps I, Problem 5.6(e,f), pp. 121–122. Constant acts determine the common prize
utility. On each nonnull event affine uniqueness identifies the proportionality
factor by the two calibrating prizes. On null events indifference makes all
conditional expected utilities zero. The representation is independent of
the chosen finite partition and starts from the primitive mixture axioms.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory

variable {S X : Type*} {A : Set (Set S)}

/-- A strict pair can be normalized to zero and one within the primitive representation. -/
theorem eventRepresentation_normalized (hA : IsSetAlgebra A)
    {r : EventAct A X → EventAct A X → Prop} (hr : @MixtureAxioms _ (eventActConvexSpace hA) r)
    (b g : SimpleLottery X) (hs : Strict r (EventConstant hA g) (EventConstant hA b)) :
    ∃ F, Represents F r ∧ EventAffine hA F ∧
      F (EventConstant hA b) = 0 ∧ F (EventConstant hA g) = 1 := by
  let _ := eventActConvexSpace (X := X) hA
  obtain ⟨u, hur, hua⟩ := (problem_5_6a hA r).mp hr
  let lo := u (EventConstant hA b)
  let hi := u (EventConstant hA g)
  have hh : lo < hi := lt_of_not_ge (fun h => hs.2 ((hur _ _).mpr h))
  let a := (hi - lo)⁻¹
  have ha : 0 < a := inv_pos.mpr (sub_pos.mpr hh)
  have ht := positive_affine_representation hur hua a (-(a * lo)) ha
  refine ⟨_, ht.1, ht.2, by dsimp only [lo]; ring, ?_⟩
  change a * hi + -(a * lo) = 1
  calc
    _ = (hi - lo)⁻¹ * (hi - lo) := by dsimp only [a]; ring
    _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hh.ne')

/-- The source's null and common-ranking assumptions for conditional roulette lotteries. -/
def EventIndependentRankings (hA : IsSetAlgebra A)
    (r : EventAct A X → EventAct A X → Prop) (base good : SimpleLottery X) : Prop :=
  (∀ E : A, CalibrationNull hA r base good E → ∀ x : X,
    Indifferent (EventRanking hA r base E.val E.property) (PureLottery x) base) ∧
  ∀ E : A, ¬CalibrationNull hA r base good E → ∀ q t,
    EventRanking hA r base E.val E.property q t ↔ r (EventConstant hA q) (EventConstant hA t)

/-- The full-event index equals the original constant-act value less the common baseline. -/
theorem eventLotteryIndex_univ (hA : IsSetAlgebra A) (F : EventAct A X → ℝ)
    (base q : SimpleLottery X) : EventLotteryIndex hA F base Set.univ hA.univ_mem q =
      F (EventConstant hA q) - F (EventConstant hA base) :=
  eventContribution_univ hA F base (EventConstant hA q)

/-- Local utility equals event probability times the global roulette index, also on null events. -/
theorem eventLotteryIndex_factor (hA : IsSetAlgebra A) {F : EventAct A X → ℝ}
    {r : EventAct A X → EventAct A X → Prop} (hF : Represents F r) (ha : EventAffine hA F)
    (base good : SimpleLottery X) (hn : F (EventConstant hA good) - F (EventConstant hA base) = 1)
    (hi : EventIndependentRankings hA r base good) (E : A) (q : SimpleLottery X) :
    EventLotteryIndex hA F base E.val E.property q = EventProbability hA F base good E *
      EventLotteryIndex hA F base Set.univ hA.univ_mem q := by
  let G := EventLotteryIndex hA F base Set.univ hA.univ_mem
  let L := EventLotteryIndex hA F base E.val E.property
  have hr := eventLotteryIndex_represents hA hF base E.property
  have hLb : L base = 0 := eventLotteryIndex_base hA F base E.property
  have hGb : G base = 0 := eventLotteryIndex_base hA F base hA.univ_mem
  have hGg : G good = 1 := (eventLotteryIndex_univ hA F base good).trans hn
  by_cases hnull : CalibrationNull hA r base good E
  · have hz := (eventProbability_zero_iff_null hA hF base good E).mpr hnull
    have pure_zero (x : X) : EventPrizeUtility hA F base E.val E.property x = 0 := by
      have hpx := hi.1 E hnull x
      have he : L (PureLottery x) = L base :=
        le_antisymm ((hr _ _).mp hpx.2) ((hr _ _).mp hpx.1)
      exact he.trans hLb
    rw [hz, zero_mul, eventLotteryIndex_expectedUtility hA ha]
    simp [ExpectedUtility, pure_zero]
  · have hcmp (x y : SimpleLottery X) : G x ≤ G y ↔ L x ≤ L y := by
      change EventLotteryIndex hA F base Set.univ hA.univ_mem x ≤
        EventLotteryIndex hA F base Set.univ hA.univ_mem y ↔ _
      rw [eventLotteryIndex_univ, eventLotteryIndex_univ, sub_le_sub_iff_right]
      exact (hF _ _).symm.trans ((hi.2 E hnull y x).symm.trans (hr y x))
    obtain ⟨a, _, t, ht⟩ := affineInMix_unique (eventLotteryIndex_affine hA ha base hA.univ_mem)
      (eventLotteryIndex_affine hA ha base E.property) hcmp
    have hb : L base = a * G base + t := ht base
    have hg : L good = a * G good + t := ht good
    rw [hLb, hGb, mul_zero, zero_add] at hb
    rw [hGg, mul_one, ← hb, add_zero] at hg
    change L q = L good * G q
    exact (ht q).trans (by change a * G q + t = L good * G q; rw [← hb, hg, add_zero])

/-- **Problem 5.6(f):** primitive preferences on doubly simple acts admit finitely additive SEU. -/
theorem problem_5_6f (hA : IsSetAlgebra A) {r : EventAct A X → EventAct A X → Prop}
    (hr : @MixtureAxioms _ (eventActConvexSpace hA) r) (b g : X)
    (hs : Strict r (EventConstant hA (PureLottery g)) (EventConstant hA (PureLottery b)))
    (hw : ∀ E : A, EventRanking hA r (PureLottery b) E.val E.property (PureLottery g)
      (PureLottery b))
    (hi : EventIndependentRankings hA r (PureLottery b) (PureLottery g)) :
    ∃ (p : A → ℝ) (U : X → ℝ) (V : EventAct A X → ℝ),
      FinitelyAdditiveProbability hA p ∧ Represents V r ∧
      (∀ E, p E = 0 ↔ CalibrationNull hA r (PureLottery b) (PureLottery g) E) ∧
      ∀ (h : EventAct A X) (n : ℕ) (c : S → Fin n) (hc : ∀ i, {s | c s = i} ∈ A)
        (q : Fin n → SimpleLottery X), (∀ s, h.val s = q (c s)) →
          V h = ∑ i, p ⟨{s | c s = i}, hc i⟩ * ExpectedUtility U (q i) := by
  let base := PureLottery b
  let good := PureLottery g
  obtain ⟨F, hFr, hFa, hb, hg⟩ := eventRepresentation_normalized hA hr base good hs
  have hn : F (EventConstant hA good) - F (EventConstant hA base) = 1 := by rw [hb, hg, sub_zero]
  obtain ⟨hp, hz⟩ := problem_5_6e hA hFr hFa base good hn hw
  refine ⟨EventProbability hA F base good, EventPrizeUtility hA F base Set.univ hA.univ_mem,
    F, hp, hFr, hz, ?_⟩
  intro h n c hc q hh
  have H := problem_5_6d hA hFa base c hc q h hh
  rw [hb, sub_zero] at H
  rw [H]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eventLotteryIndex_expectedUtility hA hFa, ← eventLotteryIndex_expectedUtility hA hFa]
  exact eventLotteryIndex_factor hA hFr hFa base good hn hi ⟨_, hc i⟩ (q i)

/-- Omitting conditional nonnegativity admits signed unit-mass weights, even under the axioms. -/
theorem event_sign_counterexample :
    ∃ F : HorseLottery (Fin 2) Bool → ℝ, MixtureAxioms (UtilityPref F) ∧
      F (fun _ => PureLottery false) = 0 ∧ F (fun _ => PureLottery true) = 1 ∧
      F ![PureLottery true, PureLottery false] = -1 := by
  let U : Fin 2 → Bool → ℝ := ![fun b => if b then -1 else 0, fun b => if b then 2 else 0]
  refine ⟨HorseValue U, mixtureAxioms_of_representation (fun _ _ => Iff.rfl)
    (horseValue_affine U), ?_⟩
  norm_num [HorseValue, StateAdditiveValue, U, expectedUtility_pure, Fin.sum_univ_two]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The countably additive extension in the invitation on page 122

We take a sigma-algebra of state events. The explicit extra continuity condition
is continuity of the evaluated calibrated acts along increasing event sequences.
It gives a countably additive probability on the given sigma-algebra. Integrating
statewise roulette utility recovers every finite-partition formula. Dominated
convergence extends the values along approximations of richer acts.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Filter
open scoped ENNReal Topology

variable {S X : Type*} [MeasurableSpace S]

/-- The family of events in the specified sigma-algebra. -/
def SigmaEvents (S : Type*) [MeasurableSpace S] : Set (Set S) := {E | MeasurableSet E}

/-- The measurable events satisfy the event-algebra assumptions of Problem 5.6. -/
theorem sigmaEvents_isSetAlgebra : IsSetAlgebra (SigmaEvents S) :=
  ⟨MeasurableSet.empty, fun _ h => MeasurableSet.compl h, fun _ _ h g => MeasurableSet.union h g⟩

/-- Continuity from below for the event probabilities calibrated from preferences. -/
def EventWeightContinuous (p : SigmaEvents S → ℝ) : Prop :=
  ∀ (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n)), Monotone E →
    Tendsto (fun n => p ⟨E n, he n⟩) atTop (𝓝 (p ⟨⋃ n, E n, MeasurableSet.iUnion he⟩))

/-- The union of the first `n` events of a sequence. -/
def InitialEventUnion (E : ℕ → Set S) (n : ℕ) : Set S := ⋃ i : Fin n, E i

/-- A successor initial union adds exactly one event. -/
theorem initialEventUnion_succ {Y : Type*} (E : ℕ → Set Y) (n : ℕ) :
    InitialEventUnion E (n + 1) = InitialEventUnion E n ∪ E n := by
  ext s
  simp only [InitialEventUnion, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i.val < n
    · exact Or.inl ⟨⟨i.val, h⟩, hi⟩
    · have he : i.val = n := by omega
      exact Or.inr (he ▸ hi)
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hi⟩

/-- Finite additivity and continuity from below give countable additivity on disjoint sequences. -/
theorem eventWeight_hasSum (p : SigmaEvents S → ℝ)
    (hp : FinitelyAdditiveProbability sigmaEvents_isSetAlgebra p) (hc : EventWeightContinuous p)
    (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    HasSum (fun n => p ⟨E n, he n⟩) (p ⟨⋃ n, E n, MeasurableSet.iUnion he⟩) := by
  classical
  have hm (n) : MeasurableSet (InitialEventUnion E n) := MeasurableSet.iUnion fun i => he i.val
  have hi : Monotone (InitialEventUnion E) := monotone_nat_of_le_succ fun n => by
    rw [initialEventUnion_succ]
    exact Set.subset_union_left
  have hall : (⋃ n, InitialEventUnion E n) = ⋃ n, E n := by
    ext s
    simp only [InitialEventUnion, Set.mem_iUnion]
    exact ⟨fun ⟨_, i, h⟩ => ⟨i.val, h⟩, fun ⟨n, h⟩ => ⟨n + 1, Fin.last n, h⟩⟩
  have hv (n) : p ⟨InitialEventUnion E n, hm n⟩ =
      ∑ i ∈ Finset.range n, p ⟨E i, he i⟩ := by
    induction n with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      convert hp.2.2.1 using 1
      apply congrArg p
      apply Subtype.ext
      simp [InitialEventUnion]
    | succ n ih =>
      have hdis : Disjoint (InitialEventUnion E n) (E n) := by
        apply Set.disjoint_left.mpr
        intro s hs h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        exact Set.disjoint_left.mp (hd (ne_of_lt i.isLt)) hi h
      have hh := hp.2.2.2 ⟨InitialEventUnion E n, hm n⟩ ⟨E n, he n⟩ hdis
      rw [Finset.sum_range_succ, ← ih, ← hh]
      exact congrArg p (Subtype.ext (initialEventUnion_succ E n))
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => (hp.1 ⟨E n, he n⟩).1)]
  have h := hc (InitialEventUnion E) hm hi
  have hlast : (⟨⋃ n, InitialEventUnion E n, MeasurableSet.iUnion hm⟩ : SigmaEvents S) =
      ⟨⋃ n, E n, MeasurableSet.iUnion he⟩ := Subtype.ext hall
  simpa only [hv, hlast] using h

/-- The calibrated probabilities define an actual countably additive probability measure. -/
theorem probabilityMeasure_of_eventContinuity (p : SigmaEvents S → ℝ)
    (hp : FinitelyAdditiveProbability sigmaEvents_isSetAlgebra p) (hc : EventWeightContinuous p) :
    ∃ μ : ProbabilityMeasure S, ∀ E : SigmaEvents S, (μ : Measure S).real E.val = p E := by
  let m : ∀ E : Set S, MeasurableSet E → ℝ≥0∞ := fun E h => ENNReal.ofReal (p ⟨E, h⟩)
  have hzero : m ∅ MeasurableSet.empty = 0 := by simp [m, hp.2.2.1]
  have hsum {E : ℕ → Set S} (he : ∀ n, MeasurableSet (E n))
      (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
      m (⋃ n, E n) (MeasurableSet.iUnion he) = ∑' n, m (E n) (he n) := by
    have hs := eventWeight_hasSum p hp hc E he hd
    change ENNReal.ofReal _ = ∑' n, ENNReal.ofReal _
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => (hp.1 ⟨E n, he n⟩).1) hs.summable]
  let μ := Measure.ofMeasurable m hzero (fun {_} he hd => hsum he hd)
  have happ (E : SigmaEvents S) : μ E.val = ENNReal.ofReal (p E) :=
    Measure.ofMeasurable_apply E.val E.property
  have hmass : μ Set.univ = 1 := by
    rw [happ ⟨Set.univ, MeasurableSet.univ⟩, hp.2.1, ENNReal.ofReal_one]
  refine ⟨⟨μ, ⟨hmass⟩⟩, fun E => ?_⟩
  change (μ E.val).toReal = p E
  rw [happ, ENNReal.toReal_ofReal (hp.1 E).1]

/-- Continuity of calibrated event bets supplies continuity from below for their probabilities. -/
theorem probabilityMeasure_of_calibratedActs {F : EventAct (SigmaEvents S) X → ℝ}
    {r : EventAct (SigmaEvents S) X → EventAct (SigmaEvents S) X → Prop}
    (hF : Represents F r) (ha : EventAffine sigmaEvents_isSetAlgebra F)
    (b g : SimpleLottery X)
    (hn : F (EventConstant sigmaEvents_isSetAlgebra g) -
      F (EventConstant sigmaEvents_isSetAlgebra b) = 1)
    (hw : ∀ E : SigmaEvents S, EventRanking sigmaEvents_isSetAlgebra r b E.val E.property g b)
    (hc : ∀ (E : ℕ → Set S) (he : ∀ n, MeasurableSet (E n)), Monotone E →
      Tendsto (fun n => F (EventCut sigmaEvents_isSetAlgebra b (E n) (he n)
        (EventConstant sigmaEvents_isSetAlgebra g))) atTop
        (𝓝 (F (EventCut sigmaEvents_isSetAlgebra b (⋃ n, E n) (MeasurableSet.iUnion he)
          (EventConstant sigmaEvents_isSetAlgebra g))))) :
    ∃ μ : ProbabilityMeasure S, ∀ E : SigmaEvents S, (μ : Measure S).real E.val =
      EventProbability sigmaEvents_isSetAlgebra F b g E := by
  apply probabilityMeasure_of_eventContinuity _
    (problem_5_6e sigmaEvents_isSetAlgebra hF ha b g hn hw).1
  intro E he hm
  exact (hc E he hm).sub (tendsto_const_nhds (x := F (EventConstant sigmaEvents_isSetAlgebra b)))

/-- The integral of a simple state payoff is its finite partition-weighted sum. -/
theorem integral_partition_value {I : Type*} [Fintype I] (μ : ProbabilityMeasure S)
    (c : S → I) (he : ∀ i, MeasurableSet {s | c s = i}) (v : I → ℝ) :
    (∫ s, v (c s) ∂(μ : Measure S)) = ∑ i, (μ : Measure S).real {s | c s = i} * v i := by
  classical
  have hsum (s : S) : v (c s) = ∑ i, ({t | c t = i} : Set S).indicator (fun _ => v i) s := by
    simp [Set.indicator]
  simp_rw [hsum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (he i), setIntegral_const, smul_eq_mul]
  · intro i _
    exact (integrable_const _).indicator (he i)

/-- On every doubly simple act the integral extension equals the finite subjective EU formula. -/
theorem integral_simpleHorseValue {I : Type*} [Fintype I] (μ : ProbabilityMeasure S)
    (U : X → ℝ) (h : EventAct (SigmaEvents S) X) (c : S → I)
    (hc : ∀ i, MeasurableSet {s | c s = i}) (q : I → SimpleLottery X)
    (hh : ∀ s, h.val s = q (c s)) :
    (∫ s, ExpectedUtility U (h.val s) ∂(μ : Measure S)) =
      ∑ i, (μ : Measure S).real {s | c s = i} * ExpectedUtility U (q i) := by
  simpa only [hh] using integral_partition_value μ c hc (fun i => ExpectedUtility U (q i))

/-- Dominated almost-everywhere approximation extends these integrals to more general acts. -/
theorem simpleHorseValue_tendsto (μ : ProbabilityMeasure S) (U : X → ℝ)
    (h : S → SimpleLottery X) (g : ℕ → EventAct (SigmaEvents S) X) (bound : S → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (fun s => ExpectedUtility U ((g n).val s)) (μ : Measure S))
    (hb : Integrable bound (μ : Measure S))
    (hdom : ∀ n, ∀ᵐ s ∂(μ : Measure S), ‖ExpectedUtility U ((g n).val s)‖ ≤ bound s)
    (hlim : ∀ᵐ s ∂(μ : Measure S), Tendsto (fun n => ExpectedUtility U ((g n).val s)) atTop
      (𝓝 (ExpectedUtility U (h s)))) :
    Tendsto (fun n => ∫ s, ExpectedUtility U ((g n).val s) ∂(μ : Measure S)) atTop
      (𝓝 (∫ s, ExpectedUtility U (h s) ∂(μ : Measure S))) :=
  tendsto_integral_of_dominated_convergence bound hm hb hdom hlim

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Lotteries over entire subsets and lotteries over inclusion marginals

Kreps I, Problem 5.5, pp. 118–119. A binary roulette is affinely parameterized
by its probability of inclusion. Arbitrary set utility extends to lotteries of
subsets. On the cube of marginal inclusion probabilities an affine index has an
additive restriction to the deterministic vertices after normalizing its origin.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The inclusion probability of a binary lottery lies in the unit interval. -/
noncomputable def InclusionProbability (p : SimpleLottery Bool) : Weight :=
  ⟨p.weights true, p.nonneg true, p.weights_apply_le_one true⟩

/-- The unique Bernoulli lottery having the chosen inclusion probability. -/
noncomputable def InclusionLottery (a : Weight) : SimpleLottery Bool :=
  Convexity.StdSimplex.duple true false a.property.1 (sub_nonneg.mpr a.property.2) (by ring)

/-- The Bernoulli law has precisely its specified marginal. -/
theorem inclusionProbability_lottery (a : Weight) :
    InclusionProbability (InclusionLottery a) = a := by
  apply Subtype.ext
  simp [InclusionProbability, InclusionLottery]

/-- Its inclusion probability determines the entire binary lottery. -/
theorem inclusionLottery_probability (p : SimpleLottery Bool) :
    InclusionLottery (InclusionProbability p) = p := by
  apply Convexity.StdSimplex.ext
  ext b
  have ht := p.total_of_fintype
  rw [Fintype.sum_bool] at ht
  cases b <;> simp [InclusionProbability, InclusionLottery]
  linarith

/-- Binary roulette marginals mix coordinatewise by the affine formula prescribed on the cube. -/
theorem inclusionProbability_mix (a : Weight) (p q : SimpleLottery Bool) :
    (InclusionProbability (Mix a p q)).val =
      a.val * (InclusionProbability p).val + (1 - a.val) * (InclusionProbability q).val :=
  lottery_mix_weight a p q true

/-- A deterministic subset has inclusion probabilities zero or one at every coordinate. -/
noncomputable def SubsetVertex {X : Type*} [DecidableEq X] (z : Finset X) :
    HorseLottery X Bool := fun x => if x ∈ z then PureLottery true else PureLottery false

/-- The map from subsets really gives their pointwise characteristic probabilities. -/
theorem subsetVertex_probability {X : Type*} [DecidableEq X] (z : Finset X) (x : X) :
    (InclusionProbability (SubsetVertex z x)).val = if x ∈ z then 1 else 0 := by
  by_cases hx : x ∈ z <;> simp [SubsetVertex, InclusionProbability, PureLottery, hx]

/-- Any utility on whole subsets extends to a mixture-affine utility on lotteries of subsets. -/
theorem subsetLottery_extension {X : Type*} (U : Finset X → ℝ) :
    AffineInMix (ExpectedUtility U) ∧ ∀ z, ExpectedUtility U (PureLottery z) = U z :=
  ⟨expectedUtility_affine U, expectedUtility_pure U⟩

/-- Normalizing an affine marginal utility at the empty subset gives additive item values. -/
theorem subsetMargin_additive {X : Type*} [Finite X] [DecidableEq X]
    {F : HorseLottery X Bool → ℝ} (hF : AffineInMix F) :
    ∃ U : X → ℝ, ∀ z : Finset X, F (SubsetVertex z) - F (SubsetVertex ∅) = ∑ x ∈ z, U x := by
  let _ := Fintype.ofFinite X
  let b : HorseLottery X Bool := fun _ => PureLottery false
  have hbase : SubsetVertex (∅ : Finset X) = b := by ext x; simp [SubsetVertex, b]
  let U : X → ℝ := fun x => StateIncrement F b x (PureLottery true)
  refine ⟨U, fun z => ?_⟩
  rw [hbase, horseValue_of_affine hF b (SubsetVertex z)]
  unfold HorseValue StateAdditiveValue
  calc
    _ = ∑ x, (if x ∈ z then U x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ z
      · simp [SubsetVertex, hx, expectedUtility_pure, U]
      · simp [SubsetVertex, hx, expectedUtility_pure, StateIncrement, b]
    _ = _ := by simp

/-- An explicit joint value on two objects violates item additivity, even up to a constant. -/
theorem wholeSubset_utility_nonadditive :
    ¬∃ (U : Bool → ℝ) (B : ℝ), ∀ z : Finset Bool,
      (if z = {true, false} then (1 : ℝ) else 0) = B + ∑ x ∈ z, U x := by
  rintro ⟨U, B, h⟩
  have a := h ∅
  have b := h {true}
  have c := h {false}
  have d := h {true, false}
  have e₀ : (∅ : Finset Bool) ≠ {true, false} := by decide
  have e₁ : ({true} : Finset Bool) ≠ {true, false} := by decide
  have e₂ : ({false} : Finset Bool) ≠ {true, false} := by decide
  norm_num [e₀, e₁, e₂] at a b c d
  linarith

/-- The affine index on the entire marginal cube is linear in the inclusion probabilities. -/
theorem subsetMargin_cube_value {X : Type*} [Fintype X] [DecidableEq X]
    {F : HorseLottery X Bool → ℝ} (hF : AffineInMix F) :
    ∃ U : X → ℝ, ∀ q : X → Weight,
      F (fun x => InclusionLottery (q x)) - F (SubsetVertex ∅) = ∑ x, (q x).val * U x := by
  let b : HorseLottery X Bool := fun _ => PureLottery false
  have hbase : SubsetVertex (∅ : Finset X) = b := by ext x; simp [SubsetVertex, b]
  let U : X → ℝ := fun x => StateIncrement F b x (PureLottery true)
  refine ⟨U, fun q => ?_⟩
  rw [hbase, horseValue_of_affine hF b]
  apply Finset.sum_congr rfl
  intro i _
  change ExpectedUtility (fun x => StateIncrement F b i (PureLottery x)) (InclusionLottery (q i)) =
    (q i).val * U i
  rw [expectedUtility_eq_sum, Fintype.sum_bool]
  simp [InclusionLottery, U, StateIncrement, b]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The five calculations in Problem 5.1

Kreps I, pp. 116–117, Figures 5.10–5.11. The horse-race acts return actual
finitely supported roulette lotteries. Rational inequalities for the square
roots certify the comparisons involving fourth powers without rounding a value.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The three monetary lotteries in Problem 5.1(a), in their printed order. -/
noncomputable def Problem51Money : Fin 3 → Convexity.StdSimplex ℝ ℝ :=
  ![CertainBranch.lottery (fun _ => 10000),
    (TwoBranches (1 / 3) (by constructor <;> norm_num)).lottery ![3600, 14400],
    (ThreeBranches (1 / 5) (1 / 5) (3 / 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![0, 10000, 22500]]

/-- The square-root expected utility of the `i`th printed money lottery. -/
noncomputable def Problem51MoneyValue (i : Fin 3) : ℝ :=
  (Problem51Money i).weights.sum (fun x t => t * Real.sqrt x)

/-- **Problem 5.1(a):** the third lottery is preferred, and the first two tie at 100. -/
theorem problem_5_1a : Problem51MoneyValue 0 = 100 ∧ Problem51MoneyValue 1 = 100 ∧
    Problem51MoneyValue 2 = 110 := by
  norm_num [Problem51MoneyValue, Problem51Money, BranchTable.lottery_value, certainBranch_value,
    twoBranches_value, threeBranches_value]

/-- The two-good bundles in the three acts of Figure 5.10, indexed by act and state. -/
def Figure510Act : Fin 3 → Fin 3 → ℝ × ℝ :=
  ![![(1, 4), (3, 12), (7, 7)], ![(4, 4), (2, 20), (10, 0)], fun _ => (5, 5)]

/-- The three state-dependent utilities used in parts (b) and (d). -/
noncomputable def Figure510Utility : Fin 3 → (ℝ × ℝ) → ℝ :=
  ![fun x => Real.sqrt (x.1 * x.2), fun x => 3 / 5 * min x.1 x.2,
    fun x => 2 / 5 * (x.1 + x.2)]

/-- The probabilities one-half, three-tenths and one-fifth in parts (c) and (e). -/
noncomputable def Figure510Prob : BranchTable 3 :=
  ThreeBranches (1 / 2) (3 / 10) (1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The state-independent geometric fourth root, evaluated on the nonnegative prizes. -/
noncomputable def Figure510CommonUtility (x : ℝ × ℝ) : ℝ := Real.sqrt (Real.sqrt (x.1 * x.2))

/-- On these prizes the nested square root is exactly the printed exponent `0.25`. -/
theorem figure510CommonUtility_eq_rpow {x : ℝ × ℝ} (hx : 0 ≤ x.1 * x.2) :
    Figure510CommonUtility x = (x.1 * x.2) ^ (1 / 4 : ℝ) := by
  unfold Figure510CommonUtility
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- The state-additive value of each Figure 5.10 act in part (b). -/
noncomputable def Figure510AdditiveValue (a : Fin 3) : ℝ :=
  ∑ s, Figure510Utility s (Figure510Act a s)

/-- **Problem 5.1(b):** the third act is best, the first second and the second last. -/
theorem problem_5_1b : Figure510AdditiveValue 0 = 47 / 5 ∧
    Figure510AdditiveValue 1 = 46 / 5 ∧ Figure510AdditiveValue 2 = 12 := by
  norm_num [Figure510AdditiveValue, Figure510Utility, Figure510Act, Fin.sum_univ_succ]

/-- The subjective expected utility in part (c), with a common prize utility across states. -/
noncomputable def Figure510SubjectiveValue (a : Fin 3) : ℝ :=
  Figure510Prob.value (Figure510Act a) Figure510CommonUtility

/-- Exact radical values of the three acts under subjective expected utility. -/
theorem figure510_subjective_values :
    Figure510SubjectiveValue 0 = Real.sqrt 2 / 2 + 3 * Real.sqrt 6 / 10 + Real.sqrt 7 / 5 ∧
    Figure510SubjectiveValue 1 = 1 + 3 * Real.sqrt (Real.sqrt 40) / 10 ∧
    Figure510SubjectiveValue 2 = Real.sqrt 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Figure510SubjectiveValue, Figure510Prob, BranchTable.value,
    ThreeBranches,
    Figure510Act, Figure510CommonUtility, Fin.sum_univ_succ] <;> ring

/-- Small rational enclosures used to certify the strict numerical rankings. -/
theorem figure510_root_bounds :
    (14 / 10 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 142 / 100 ∧
    (24 / 10 : ℝ) < Real.sqrt 6 ∧ Real.sqrt 6 < 245 / 100 ∧
    (26 / 10 : ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < 265 / 100 ∧
    (223 / 100 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 12 < 347 / 100 ∧
    Real.sqrt (Real.sqrt 40) < 26 / 10 := by
  have hs : Real.sqrt 40 < 676 / 100 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rw [Real.lt_sqrt (by norm_num)]; norm_num
          | rw [Real.sqrt_lt' (by norm_num)]; norm_num <;> linarith

/-- **Problem 5.1(c):** the strict ranking is again third, first, second. -/
theorem problem_5_1c : Figure510SubjectiveValue 2 > Figure510SubjectiveValue 0 ∧
    Figure510SubjectiveValue 0 > Figure510SubjectiveValue 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := figure510_subjective_values
  obtain ⟨a, b, c, d, e, f, g, _, i⟩ := figure510_root_bounds
  constructor <;> linarith

/-- The left act in Figure 5.11 gives a roulette lottery conditional on each state. -/
noncomputable def Figure511Left : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ) :=
  ![(TwoBranches (1 / 5) (by constructor <;> norm_num)).lottery ![(1, 4), (3, 12)],
    CertainBranch.lottery (fun _ => (7, 7)),
    (ThreeBranches (1 / 5) (7 / 20) (9 / 20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).lottery ![(2, 2), (6, 24), (0, 0)]]

/-- The right act in Figure 5.11 gives the sure bundle `(5,5)` in every state. -/
noncomputable def Figure511Right : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ) :=
  fun _ => CertainBranch.lottery (fun _ => (5, 5))

/-- Sum of the three conditional expected utilities of a horse-race lottery. -/
noncomputable def Figure511Value (U : Fin 3 → (ℝ × ℝ) → ℝ)
    (h : Fin 3 → Convexity.StdSimplex ℝ (ℝ × ℝ)) : ℝ :=
  ∑ s, (h s).weights.sum (fun x a => a * U s x)

/-- **Problem 5.1(d):** the left horse-race lottery has strictly higher additive utility. -/
theorem problem_5_1d : Figure511Value Figure510Utility Figure511Left = 348 / 25 ∧
    Figure511Value Figure510Utility Figure511Right = 12 := by
  norm_num [Figure511Value, Figure510Utility, Figure511Left, Figure511Right,
    Fin.sum_univ_succ, BranchTable.lottery_value, certainBranch_value, twoBranches_value,
    threeBranches_value]

/-- Weight each state's common prize utilities by its subjective probability. -/
noncomputable def Figure511WeightedUtility (s : Fin 3) (x : ℝ × ℝ) : ℝ :=
  Figure510Prob.mass s * Figure510CommonUtility x

/-- Exact radical values of both horse-race lotteries under subjective expected utility. -/
theorem figure511_subjective_values :
    Figure511Value Figure511WeightedUtility Figure511Left =
      (Real.sqrt 2 / 5 + 4 * Real.sqrt 6 / 5) / 2 + 3 * Real.sqrt 7 / 10 +
        (Real.sqrt 2 / 5 + 7 * Real.sqrt 12 / 20) / 5 ∧
    Figure511Value Figure511WeightedUtility Figure511Right = Real.sqrt 5 := by
  constructor <;> norm_num [Figure511Value, Figure511WeightedUtility, Figure510Prob, ThreeBranches,
    Figure510CommonUtility, Figure511Left, Figure511Right, BranchTable.value, TwoBranches,
    CertainBranch, Fin.sum_univ_succ, BranchTable.lottery_value] <;> ring

/-- **Problem 5.1(e):** with common fourth-root utility the right lottery is strictly preferred. -/
theorem problem_5_1e : Figure511Value Figure511WeightedUtility Figure511Right >
    Figure511Value Figure511WeightedUtility Figure511Left := by
  obtain ⟨hl, hr⟩ := figure511_subjective_values
  obtain ⟨_, a, _, b, _, c, d, e, _⟩ := figure510_root_bounds
  linarith

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Representations on alternative prize spaces

Kreps I, Problems 5.1(d,e), 5.4 and 5.5, pp. 117–119. These interfaces connect
the numerical trees to the chapter's representations and specialize the mixture
theorem to roulette-first acts, whole subsets and marginal inclusion probabilities.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The score computed from each Figure 5.11 tree is Equation (5.6). -/
theorem figure511Value_eq_horseValue (U : Fin 3 → (ℝ × ℝ) → ℝ) (h : HorseLottery (Fin 3) (ℝ × ℝ)) :
    Figure511Value U h = HorseValue U h := rfl

/-- The probability-weighted score of part (e) is Equation (5.8) on the very same trees. -/
theorem figure511Value_eq_subjective (h : HorseLottery (Fin 3) (ℝ × ℝ)) :
    Figure511Value Figure511WeightedUtility h =
      SubjectiveHorseValue Figure510Prob.mass Figure510CommonUtility h := by
  rw [subjectiveHorseValue_eq_horseValue]
  rfl

/-- **Problem 5.4:** roulette first gives expected utility with entire acts as prizes. -/
theorem problem_5_4 {S X : Type*} {r : SimpleLottery (S → X) → SimpleLottery (S → X) → Prop} :
    MixtureAxioms r ↔ ∃ U : (S → X) → ℝ, Represents (ExpectedUtility U) r := proposition_5_3

/-- **Problem 5.5, whole subsets:** each subset can have its own prize utility. -/
theorem problem_5_5_whole {X : Type*}
    {r : SimpleLottery (Finset X) → SimpleLottery (Finset X) → Prop} :
    MixtureAxioms r ↔ ∃ U : Finset X → ℝ, Represents (ExpectedUtility U) r := proposition_5_3

/-- Every prescribed utility on subsets gives such a lottery ranking, also on degenerate subsets. -/
theorem subsetUtility_unrestricted {X : Type*} (U : Finset X → ℝ) :
    MixtureAxioms (UtilityPref (ExpectedUtility U)) ∧
      ∀ a b, UtilityPref (ExpectedUtility U) (PureLottery a) (PureLottery b) ↔ U b ≤ U a := by
  refine ⟨proposition_5_3.mpr ⟨U, fun _ _ => Iff.rfl⟩, ?_⟩
  intro a b
  simp [UtilityPref, expectedUtility_pure]

/-- **Problem 5.5, marginals:** the primitive axioms give an item-additive ranking on subsets. -/
theorem problem_5_5_marginals {X : Type*} [Finite X] [DecidableEq X]
    {r : HorseLottery X Bool → HorseLottery X Bool → Prop} (hr : MixtureAxioms r) :
    ∃ U : X → ℝ, ∀ a b : Finset X, r (SubsetVertex a) (SubsetVertex b) ↔
      ∑ x ∈ b, U x ≤ ∑ x ∈ a, U x := by
  obtain ⟨F, hFr, hFa⟩ := proposition_5_4.mp hr
  obtain ⟨U, hu⟩ := subsetMargin_additive hFa
  refine ⟨U, fun a b => ?_⟩
  rw [hFr, ← hu a, ← hu b, sub_le_sub_iff_right]

/-- A represented preference compares distinct utility levels strictly. -/
theorem strict_of_exerciseValue {Y : Type*} {r : Y → Y → Prop} {u : Y → ℝ}
    (hr : Represents u r) {x y : Y} (h : u y < u x) : Strict r x y :=
  ⟨(hr x y).mpr h.le, fun hy => h.not_ge ((hr y x).mp hy)⟩

/-- Part (a) ranks the actual monetary lotteries, including the exact indifference. -/
theorem problem_5_1a_preference {r : SimpleLottery ℝ → SimpleLottery ℝ → Prop}
    (hr : Represents (ExpectedUtility Real.sqrt) r) :
    Strict r (Problem51Money 2) (Problem51Money 0) ∧
    Indifferent r (Problem51Money 0) (Problem51Money 1) := by
  obtain ⟨h₀, h₁, h₂⟩ := problem_5_1a
  refine ⟨strict_of_exerciseValue hr ?_, (hr _ _).mpr ?_, (hr _ _).mpr ?_⟩
  · change Problem51MoneyValue 0 < Problem51MoneyValue 2
    linarith
  · change Problem51MoneyValue 1 ≤ Problem51MoneyValue 0
    linarith
  · change Problem51MoneyValue 0 ≤ Problem51MoneyValue 1
    linarith

/-- Part (b) ranks the deterministic acts under the state-dependent representation. -/
theorem problem_5_1b_preference {r : StateAct (Fin 3) (ℝ × ℝ) → StateAct (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (StateAdditiveValue Figure510Utility) r) :
    Strict r (Figure510Act 2) (Figure510Act 0) ∧ Strict r (Figure510Act 0) (Figure510Act 1) := by
  obtain ⟨a, b, c⟩ := problem_5_1b
  refine ⟨strict_of_exerciseValue hr ?_, strict_of_exerciseValue hr ?_⟩
  · change Figure510AdditiveValue 0 < Figure510AdditiveValue 2
    linarith
  · change Figure510AdditiveValue 1 < Figure510AdditiveValue 0
    linarith

/-- Part (c) yields the same strict order under the common subjective utility. -/
theorem problem_5_1c_preference {r : StateAct (Fin 3) (ℝ × ℝ) → StateAct (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (SubjectiveActValue Figure510Prob.mass Figure510CommonUtility) r) :
    Strict r (Figure510Act 2) (Figure510Act 0) ∧ Strict r (Figure510Act 0) (Figure510Act 1) :=
  ⟨strict_of_exerciseValue hr problem_5_1c.1, strict_of_exerciseValue hr problem_5_1c.2⟩

/-- Part (d) gives strict preference for the left horse-race lottery. -/
theorem problem_5_1d_preference
    {r : HorseLottery (Fin 3) (ℝ × ℝ) → HorseLottery (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (HorseValue Figure510Utility) r) : Strict r Figure511Left Figure511Right := by
  apply strict_of_exerciseValue hr
  change Figure511Value _ Figure511Right < Figure511Value _ Figure511Left
  rw [problem_5_1d.1, problem_5_1d.2]
  norm_num

/-- Part (e) reverses the choice between the same two horse-race lotteries. -/
theorem problem_5_1e_preference
    {r : HorseLottery (Fin 3) (ℝ × ℝ) → HorseLottery (Fin 3) (ℝ × ℝ) → Prop}
    (hr : Represents (SubjectiveHorseValue Figure510Prob.mass Figure510CommonUtility) r) :
    Strict r Figure511Right Figure511Left := by
  apply strict_of_exerciseValue hr
  simpa only [← figure511Value_eq_subjective] using problem_5_1e

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The support of a compound lottery

Kreps I, Definition 5.2 and p. 87, footnote 5. Every positive-mass prize in
either component survives an interior mixture. At endpoint weights only the
selected component remains.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- Membership in the finite support means strictly positive probability. -/
theorem lottery_mem_support_iff {X : Type*} (p : SimpleLottery X) (x : X) :
    x ∈ p.weights.support ↔ 0 < p.weights x :=
  Finsupp.mem_support_iff.trans ⟨fun h => lt_of_le_of_ne (p.nonneg x) (Ne.symm h), ne_of_gt⟩

/-- The exact support of an interior mixture is the union of the component supports. -/
theorem lottery_mix_support {X : Type*} [DecidableEq X] (p q : SimpleLottery X)
    (a : Weight) (ha : 0 < a.val) (ha' : a.val < 1) :
    (Mix a p q).weights.support = p.weights.support ∪ q.weights.support := by
  ext x
  rw [Finset.mem_union, lottery_mem_support_iff, lottery_mem_support_iff,
    lottery_mem_support_iff, lottery_mix_weight]
  constructor
  · intro h
    by_contra! hn
    rw [le_antisymm hn.1 (p.nonneg x), le_antisymm hn.2 (q.nonneg x)] at h
    linarith
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (mul_pos ha h) (mul_nonneg (sub_nonneg.mpr a.property.2)
        (q.nonneg x))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (p.nonneg x)) (mul_pos (sub_pos.mpr ha') h)

/-- The two endpoint supports need no positivity assumption and agree with the selected law. -/
theorem lottery_endpoint_supports {X : Type*} (p q : SimpleLottery X) :
    (Mix 0 p q).weights.support = q.weights.support ∧
      (Mix 1 p q).weights.support = p.weights.support := by rw [mix_zero, mix_one]; exact ⟨rfl, rfl⟩

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# State-contingent examples and probability calibration

Kreps I, pp. 79–86, 106, 108–109 and Problem 5.2, p. 118. The horse race,
advertising decisions and weather-dependent prizes use the printed outcomes.
The World Cup comparisons identify subjective odds by comparison with roulette.
-/

namespace Kreps.ChoiceUnderUncertainty

/-- The three states are a Secretariat win, a Kelso win and a dead heat. -/
noncomputable def RaceOdds : BranchTable 3 :=
  ThreeBranches (59 / 100) (36 / 100) (5 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The two bets and abstention in Figure 5.3. A wager is returned on a tie. -/
noncomputable def RaceBet : Fin 3 → Fin 3 → ℝ := ![![6 / 5, -2, 0], ![-2, 3, 0], fun _ => 0]

/-- Figure 5.1 also includes a constant act giving three dollars regardless of the race. -/
theorem race_sure_three (U : ℝ → ℝ) :
    ExpectedUtility U (RaceOdds.lottery (fun _ => 3)) = U 3 := by
  simp [BranchTable.lottery, ExpectedUtility]

/-- The pushforward of the common state odds yields exactly the three Figure 5.4 lotteries. -/
theorem race_bet_values (U : ℝ → ℝ) :
    ExpectedUtility U (RaceOdds.lottery (RaceBet 0)) =
      59 / 100 * U (6 / 5) + 36 / 100 * U (-2) + 5 / 100 * U 0 ∧
    ExpectedUtility U (RaceOdds.lottery (RaceBet 1)) =
      59 / 100 * U (-2) + 36 / 100 * U 3 + 5 / 100 * U 0 ∧
    ExpectedUtility U (RaceOdds.lottery (RaceBet 2)) = U 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [expectedUtility_branchLottery, BranchTable.value,
    RaceOdds, RaceBet, ThreeBranches, Fin.sum_univ_succ] <;> ring

/-- Figure 5.2 has two distinct bundle prizes with odds one third and two thirds. -/
theorem bundle_lottery_values (U : (ℝ × ℝ) → ℝ) :
    ExpectedUtility U ((TwoBranches (1 / 3) (by constructor <;> norm_num)).lottery
      ![(10, 2), (4, 4)]) = 1 / 3 * U (10, 2) + 2 / 3 * U (4, 4) := by
  rw [expectedUtility_branchLottery]
  norm_num [BranchTable.value, TwoBranches, Fin.sum_univ_two]

/-- Changing the common dead-heat payout from minus one to two preserves the ranking. -/
theorem race_sureThing {r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop} (h : SureThing r) :
    r ![5, -2, -1] ![2, 2, -1] ↔ r ![5, -2, 2] ![2, 2, 2] := by
  apply h ({0, 1} : Set (Fin 3))
  · intro s hs
    fin_cases s <;> norm_num at *
  · intro s hs
    fin_cases s <;> norm_num at *

/-- A constructed meal utility: shrimp pairs with fruit and melon with cake on p. 82. -/
def MealContextUtility (m : Fin 3 → Bool) : ℝ := if m 0 = m 2 then 1 else 0

/-- The printed shrimp/steak versus melon/veal ranking reverses with the common dessert. -/
theorem meal_dessert_reversal :
    MealContextUtility ![true, true, true] > MealContextUtility ![false, false, true] ∧
    MealContextUtility ![true, true, false] < MealContextUtility ![false, false, false] := by
  norm_num [MealContextUtility]

/-- In the two-state sales model the advertising expense lowers profits in each state. -/
theorem advertising_two_states (U : Fin 2 → ℝ → ℝ) (hu : ∀ s, StrictMono (U s)) :
    StateAdditiveValue U ![-2000, 2000] < StateAdditiveValue U ![-1000, 3000] := by
  simp only [StateAdditiveValue, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_lt_add (hu 0 (by norm_num)) (hu 1 (by norm_num))

/-- The responsive state in the repaired sales model raises net profit by three thousand. -/
theorem advertising_three_states (p : BranchTable 3) :
    p.value ![-2000, 2000, 2000] id - p.value ![-1000, -1000, 3000] id =
      4000 * p.mass 1 - 1000 := by
  have h := p.normalized
  simp [Fin.sum_univ_succ] at h
  simp [BranchTable.value, Fin.sum_univ_succ]
  linarith

/-- Risk-neutral advertising is profitable precisely above one-quarter responsive probability. -/
theorem advertising_threshold (p : BranchTable 3) :
    p.value ![-1000, -1000, 3000] id < p.value ![-2000, 2000, 2000] id ↔ 1 / 4 < p.mass 1 := by
  constructor <;> intro h <;> linarith [advertising_three_states p]

/-- With equally likely rain and sun, state-independent utility ties the two prize swaps. -/
theorem umbrella_stateIndependent {X : Type*} (umbrella lotion : X) (U : X → ℝ) :
    SubjectiveActValue (fun _ : Fin 2 => 1 / 2) U ![umbrella, lotion] =
      SubjectiveActValue (fun _ : Fin 2 => 1 / 2) U ![lotion, umbrella] := by
  simp [SubjectiveActValue, Fin.sum_univ_two, add_comm]

/-- Opposite state-dependent rankings of the goods strictly favor the weather-matched act. -/
theorem umbrella_stateDependent {X : Type*} (umbrella lotion : X) (U : Fin 2 → X → ℝ)
    (hrain : U 0 lotion < U 0 umbrella) (hsun : U 1 umbrella < U 1 lotion) :
    StateAdditiveValue U ![lotion, umbrella] < StateAdditiveValue U ![umbrella, lotion] := by
  simpa [StateAdditiveValue, Fin.sum_univ_two] using add_lt_add hrain hsun

/-- A World Cup ticket pays one hundred dollars exactly on the specified winning region. -/
noncomputable def WorldCupTicket (i : Fin 3) (s : Fin 3) : ℝ := if s = i then 100 else 0

/-- A regional ticket has the value of a roulette at that region's subjective probability. -/
theorem worldCup_ticket_value (p : BranchTable 3) (U : ℝ → ℝ) (i : Fin 3) :
    p.value (WorldCupTicket i) U = p.mass i * U 100 + (1 - p.mass i) * U 0 := by
  have h := p.normalized
  simp [Fin.sum_univ_succ] at h
  fin_cases i <;> norm_num [BranchTable.value, WorldCupTicket, Fin.sum_univ_succ] <;>
    linear_combination (U 0) * h

/-- Figure 5.8's two strict comparisons calibrate the American and European probabilities. -/
theorem worldCup_thresholds (p : BranchTable 3) (U : ℝ → ℝ) (hu : U 0 < U 100) :
    (p.value (WorldCupTicket 1) U > ExpectedUtility U
        (BinaryCash (48 / 100) (by constructor <;> norm_num) 100 0) ∧
      ExpectedUtility U (BinaryCash (48 / 100) (by constructor <;> norm_num) 100 0) >
        p.value (WorldCupTicket 0) U) ↔ p.mass 1 > 48 / 100 ∧ 48 / 100 > p.mass 0 := by
  rw [worldCup_ticket_value, worldCup_ticket_value, binaryCash_expectedUtility]
  have h (a b : ℝ) :
      a * U 100 + (1 - a) * U 0 < b * U 100 + (1 - b) * U 0 ↔ a < b := by
    calc
      _ ↔ a * (U 100 - U 0) < b * (U 100 - U 0) := by constructor <;> intro h <;> linarith
      _ ↔ _ := mul_lt_mul_iff_left₀ (sub_pos.mpr hu)
  exact and_congr (h _ _) (h _ _)

/-- Indifference to a calibrated roulette recovers the winning-region probability exactly. -/
theorem worldCup_indifference (p : BranchTable 3) (U : ℝ → ℝ) (hu : U 0 < U 100)
    (i : Fin 3) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    p.value (WorldCupTicket i) U = ExpectedUtility U (BinaryCash a ha 100 0) ↔ p.mass i = a := by
  rw [worldCup_ticket_value, binaryCash_expectedUtility]
  constructor
  · intro h
    have hz : (p.mass i - a) * (U 100 - U 0) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hu.ne'))
  · rintro h
    rw [h]

/-- In Problem 5.2, assigning arbitrary positive state weights just rescales state utilities. -/
theorem weighted_stateUtilities_recover {S X : Type*} [Fintype S] (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (U : S → X → ℝ) (h : StateAct S X) :
    (∑ s, p s * (U s (h s) / p s)) = StateAdditiveValue U h := by
  unfold StateAdditiveValue
  apply Finset.sum_congr rfl
  intro s _
  field_simp [(hp s).ne']

/-- **Problem 5.2:** weighted state-dependent and additive state utility are equivalent. -/
theorem problem_5_2 {S X : Type*} [Fintype S] [Nonempty S]
    (r : StateAct S X → StateAct S X → Prop) :
    (∃ U : S → X → ℝ, Represents (StateAdditiveValue U) r) ↔
    ∃ (p : S → ℝ) (V : S → X → ℝ), (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
      Represents (fun h => ∑ s, p s * V s (h s)) r := by
  constructor
  · rintro ⟨U, hU⟩
    let p : S → ℝ := fun _ => (Fintype.card S : ℝ)⁻¹
    have hp : ∀ s, 0 < p s := fun s => inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
    refine ⟨p, fun s x => U s x / p s, fun s => (hp s).le, ?_, ?_⟩
    · simp [p, Fintype.card_ne_zero]
    · intro a b
      simpa only [weighted_stateUtilities_recover p hp] using hU a b
  · rintro ⟨p, V, _, _, h⟩
    exact ⟨fun s x => p s * V s x, h⟩

/-- Independently specified objective lotteries need not come from common horse-race odds. -/
theorem race_odds_not_imposed :
    ¬∃ p : BranchTable 3, p.lottery (RaceBet 0) = PureLottery (6 / 5) ∧
      p.lottery (RaceBet 1) = PureLottery 3 := by
  rintro ⟨p, h₁, h₂⟩
  have a := congrArg (ExpectedUtility (fun x : ℝ => if x = 6 / 5 then 1 else 0)) h₁
  have b := congrArg (ExpectedUtility (fun x : ℝ => if x = 3 then 1 else 0)) h₂
  norm_num [expectedUtility_branchLottery, expectedUtility_pure, BranchTable.value,
    RaceBet, Fin.sum_univ_succ] at a b
  have ht := p.normalized
  simp [Fin.sum_univ_succ] at ht
  linarith [p.nonnegative 2]

end Kreps.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The countable lottery and Gaussian example on page 100

For an unbounded-below prize utility, geometrically decreasing probabilities
can give infinite expected loss. This proof constructs distinct prizes and
uses an actual probability law. On Gaussian laws and their finite mixtures,
negative exponential utility is integrable and has a finite expected value.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- Choose distinct prizes below the successive negative powers of two. -/
theorem unbounded_prize_sequence {X : Type*} (U : X → ℝ) (hU : ¬BddBelow (Set.range U)) :
    ∃ x : ℕ → X, Function.Injective x ∧ ∀ n, U (x n) < -(2 : ℝ) ^ (n + 1) := by
  have h (t : ℝ) : ∃ z, U z < t := by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := not_bddBelow_iff.mp hU t
    exact ⟨z, hz⟩
  choose pick hp using h
  let x : ℕ → X := Nat.rec (pick (-2)) (fun n z => pick (min (-(2 : ℝ) ^ (n + 2)) (U z)))
  have hs (n : ℕ) : U (x (n + 1)) < U (x n) :=
    (hp _).trans_le (min_le_right _ _)
  have hi : StrictAnti (fun n => U (x n)) := strictAnti_nat_of_succ_lt hs
  refine ⟨x, fun i j he => hi.injective (congrArg U he), ?_⟩
  intro n
  cases n with
  | zero => simpa [x] using hp (-2)
  | succ n => exact (hp _).trans_le (min_le_left _ _)

/-- The countable branch law gives branch number `n+1` probability `1/2^(n+1)`. -/
noncomputable def HalfGeometric : ProbabilityMeasure ℕ :=
  ⟨geometricMeasure ⟨1 / 2, by constructor <;> norm_num⟩, inferInstance⟩

/-- The source's branch probabilities, including the first mass of one half. -/
theorem halfGeometric_odds (n : ℕ) : (HalfGeometric : Measure ℕ).real {n} =
    1 / (2 : ℝ) ^ (n + 1) := by
  change (geometricMeasure _).real {n} = _
  rw [geometricMeasure_real_singleton (by
    intro he
    have := congrArg Subtype.val he
    norm_num at this)]
  norm_num [pow_succ, div_pow]
  ring

/-- The pushforward lottery on the prizes themselves, on any measurable prize space. -/
noncomputable def GeometricPrizeLaw {X : Type*} [MeasurableSpace X] (x : ℕ → X) :
    ProbabilityMeasure X := ⟨(HalfGeometric : Measure ℕ).map x, inferInstance⟩

/-- No branch weights are merged when the prizes are distinct. -/
theorem geometricPrizeLaw_mass {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x : ℕ → X) (hi : Function.Injective x) (n : ℕ) :
    ((GeometricPrizeLaw x : ProbabilityMeasure X) : Measure X).real {x n} =
      1 / (2 : ℝ) ^ (n + 1) := by
  have he : x ⁻¹' {x n} = {n} := by ext j; exact hi.eq_iff
  change ((HalfGeometric : Measure ℕ).map x).real {x n} = _
  rw [measureReal_def, Measure.map_apply (Measurable.of_discrete) (measurableSet_singleton _), he]
  exact halfGeometric_odds n

/-- On the constructed lottery the positive utility part vanishes and expected loss is infinite. -/
theorem geometric_expected_loss {X : Type*} (U : X → ℝ) (x : ℕ → X)
    (hx : ∀ n, U (x n) < -(2 : ℝ) ^ (n + 1)) :
    (∫⁻ n, ENNReal.ofReal (U (x n)) ∂(HalfGeometric : Measure ℕ)) = 0 ∧
    (∫⁻ n, ENNReal.ofReal (-U (x n)) ∂(HalfGeometric : Measure ℕ)) = ⊤ := by
  have hneg (n : ℕ) : U (x n) ≤ 0 := (hx n).le.trans (neg_nonpos.mpr (by positivity))
  constructor
  · simp [ENNReal.ofReal_eq_zero.mpr (hneg _)]
  · rw [lintegral_countable']
    apply top_unique
    calc
      ⊤ = ∑' _ : ℕ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
        have he : (HalfGeometric : Measure ℕ) {n} =
            ENNReal.ofReal (1 / (2 : ℝ) ^ (n + 1)) := by
          rw [← halfGeometric_odds, ofReal_measureReal (measure_ne_top _ _)]
        rw [he, ← ENNReal.ofReal_mul (neg_nonneg.mpr (hneg n)), ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        linarith [hx n]

/-- The pushforward prize law has the literal odds and extended expected utility minus infinity. -/
theorem unbounded_utility_lottery {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (U : X → ℝ) (hm : Measurable U) (hU : ¬BddBelow (Set.range U)) :
    ∃ (p : ProbabilityMeasure X) (x : ℕ → X), Function.Injective x ∧
      (∀ n, (p : Measure X).real {x n} = 1 / (2 : ℝ) ^ (n + 1)) ∧
      (∫⁻ y, ENNReal.ofReal (U y) ∂(p : Measure X)) = 0 ∧
      (∫⁻ y, ENNReal.ofReal (-U y) ∂(p : Measure X)) = ⊤ := by
  obtain ⟨x, hi, hx⟩ := unbounded_prize_sequence U hU
  refine ⟨GeometricPrizeLaw x, x, hi, geometricPrizeLaw_mass x hi, ?_⟩
  obtain ⟨h₁, h₂⟩ := geometric_expected_loss U x hx
  have hneg : Measurable (fun y => ENNReal.ofReal (-U y)) := by fun_prop
  simpa only [GeometricPrizeLaw, ProbabilityMeasure.coe_mk,
    lintegral_map hm.ennreal_ofReal Measurable.of_discrete,
    lintegral_map hneg Measurable.of_discrete] using And.intro h₁ h₂

/-- The printed Gaussian example has a finite closed-form expectation for every real parameter. -/
theorem exponentialUtility_gaussian (m a : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => -Real.exp (-(a * x))) (gaussianReal m v) ∧
    (∫ x : ℝ, -Real.exp (-(a * x)) ∂gaussianReal m v) =
      -Real.exp (m * (-a) + v * (-a) ^ 2 / 2) := by
  constructor
  · convert (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-a)).neg using 1
    simp [Pi.neg_def, neg_mul]
  · rw [integral_neg]
    congr 1
    simpa only [mgf, neg_mul] using congrFun (mgf_fun_id_gaussianReal (μ := m) (v := v)) (-a)

/-- Finite mixtures of normal returns also have integrable negative exponential utility. -/
theorem exponentialUtility_gaussianMixture {I : Type*} (w : SimpleLottery I) (m : I → ℝ)
    (v : I → ℝ≥0) (a : ℝ) :
    Integrable (fun x : ℝ => -Real.exp (-(a * x)))
      (MeasureCombination w (fun i => ⟨gaussianReal (m i) (v i), inferInstance⟩) : Measure ℝ) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (exponentialUtility_gaussian (m i) a (v i)).1.smul_measure ENNReal.ofReal_ne_top

end Kreps.ChoiceUnderUncertainty

set_option linter.style.longLine false
#print axioms Kreps.ChoiceUnderUncertainty.StateAct
#print axioms Kreps.ChoiceUnderUncertainty.StateAdditiveValue
#print axioms Kreps.ChoiceUnderUncertainty.SubjectiveActValue
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveActValue_eq_stateAdditiveValue
#print axioms Kreps.ChoiceUnderUncertainty.SureThing
#print axioms Kreps.ChoiceUnderUncertainty.sureThing_of_stateAdditive
#print axioms Kreps.ChoiceUnderUncertainty.StateIncrement
#print axioms Kreps.ChoiceUnderUncertainty.stateIncrement_independent
#print axioms Kreps.ChoiceUnderUncertainty.PartialAct
#print axioms Kreps.ChoiceUnderUncertainty.partialAct_value
#print axioms Kreps.ChoiceUnderUncertainty.stateAct_decomposition
#print axioms Kreps.ChoiceUnderUncertainty.FullMenus
#print axioms Kreps.ChoiceUnderUncertainty.ChoiceRule
#print axioms Kreps.ChoiceUnderUncertainty.FeasibleOn
#print axioms Kreps.ChoiceUnderUncertainty.Feasible
#print axioms Kreps.ChoiceUnderUncertainty.FiniteNonempty
#print axioms Kreps.ChoiceUnderUncertainty.CoherentOn
#print axioms Kreps.ChoiceUnderUncertainty.Coherent
#print axioms Kreps.ChoiceUnderUncertainty.Complete
#print axioms Kreps.ChoiceUnderUncertainty.TransitivePref
#print axioms Kreps.ChoiceUnderUncertainty.Rational
#print axioms Kreps.ChoiceUnderUncertainty.PrefChoice
#print axioms Kreps.ChoiceUnderUncertainty.UtilityPref
#print axioms Kreps.ChoiceUnderUncertainty.UtilityChoice
#print axioms Kreps.ChoiceUnderUncertainty.Represents
#print axioms Kreps.ChoiceUnderUncertainty.Revealed
#print axioms Kreps.ChoiceUnderUncertainty.Strict
#print axioms Kreps.ChoiceUnderUncertainty.Indifferent
#print axioms Kreps.ChoiceUnderUncertainty.NoBetterThan
#print axioms Kreps.ChoiceUnderUncertainty.complete_refl
#print axioms Kreps.ChoiceUnderUncertainty.prefChoice_feasible
#print axioms Kreps.ChoiceUnderUncertainty.feasible_empty
#print axioms Kreps.ChoiceUnderUncertainty.represents_choice
#print axioms Kreps.ChoiceUnderUncertainty.coherent_iff_on_full
#print axioms Kreps.ChoiceUnderUncertainty.AsymmetricPref
#print axioms Kreps.ChoiceUnderUncertainty.NegativelyTransitive
#print axioms Kreps.ChoiceUnderUncertainty.WeakFromStrict
#print axioms Kreps.ChoiceUnderUncertainty.IndifferenceFromStrict
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9a
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9b
#print axioms Kreps.ChoiceUnderUncertainty.strict_weak_trans
#print axioms Kreps.ChoiceUnderUncertainty.weak_strict_trans
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9c
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9d
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9e
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9f
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9g
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_9h
#print axioms Kreps.ChoiceUnderUncertainty.proposition_1_10
#print axioms Kreps.ChoiceUnderUncertainty.problem_1_9
#print axioms Kreps.ChoiceUnderUncertainty.Weight
#print axioms Kreps.ChoiceUnderUncertainty.Mix
#print axioms Kreps.ChoiceUnderUncertainty.AffineInMix
#print axioms Kreps.ChoiceUnderUncertainty.BackgroundIndependent
#print axioms Kreps.ChoiceUnderUncertainty.MixtureContinuous
#print axioms Kreps.ChoiceUnderUncertainty.MixtureAxioms
#print axioms Kreps.ChoiceUnderUncertainty.Complement
#print axioms Kreps.ChoiceUnderUncertainty.mix_self
#print axioms Kreps.ChoiceUnderUncertainty.mix_zero
#print axioms Kreps.ChoiceUnderUncertainty.mix_one
#print axioms Kreps.ChoiceUnderUncertainty.mix_swap
#print axioms Kreps.ChoiceUnderUncertainty.SimpleLottery
#print axioms Kreps.ChoiceUnderUncertainty.PureLottery
#print axioms Kreps.ChoiceUnderUncertainty.ExpectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_eq_affineMap
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_pure
#print axioms Kreps.ChoiceUnderUncertainty.lottery_mix_weight
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_affine
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_eq_sum
#print axioms Kreps.ChoiceUnderUncertainty.affine_segment_identity
#print axioms Kreps.ChoiceUnderUncertainty.affineInMix_unique
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_4_unique
#print axioms Kreps.ChoiceUnderUncertainty.positive_affine_representation
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_3_unique
#print axioms Kreps.ChoiceUnderUncertainty.WeightMean
#print axioms Kreps.ChoiceUnderUncertainty.mix_mix
#print axioms Kreps.ChoiceUnderUncertainty.WeakBackgroundIndependent
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_5_some_iff
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_5_weak_iff
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_5_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.segment_shift
#print axioms Kreps.ChoiceUnderUncertainty.segment_step_weak
#print axioms Kreps.ChoiceUnderUncertainty.segment_step_strict
#print axioms Kreps.ChoiceUnderUncertainty.GridWeight
#print axioms Kreps.ChoiceUnderUncertainty.gridWeight_last
#print axioms Kreps.ChoiceUnderUncertainty.gridWeight_zero
#print axioms Kreps.ChoiceUnderUncertainty.gridWeight_step
#print axioms Kreps.ChoiceUnderUncertainty.grid_chain
#print axioms Kreps.ChoiceUnderUncertainty.grid_weak
#print axioms Kreps.ChoiceUnderUncertainty.grid_strict
#print axioms Kreps.ChoiceUnderUncertainty.exists_gridWeight_between
#print axioms Kreps.ChoiceUnderUncertainty.segment_base_weak
#print axioms Kreps.ChoiceUnderUncertainty.segment_mono
#print axioms Kreps.ChoiceUnderUncertainty.segment_base_strict
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_7_strict
#print axioms Kreps.ChoiceUnderUncertainty.segment_bounds
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_7_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_6_strict
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_6_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.mix_monotone
#print axioms Kreps.ChoiceUnderUncertainty.mix_strict
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_8
#print axioms Kreps.ChoiceUnderUncertainty.Between
#print axioms Kreps.ChoiceUnderUncertainty.segment_compare_iff
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_9
#print axioms Kreps.ChoiceUnderUncertainty.lemma_5_9_unique
#print axioms Kreps.ChoiceUnderUncertainty.AnchorWeight
#print axioms Kreps.ChoiceUnderUncertainty.anchorWeight_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.mix_congr_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.between_mix
#print axioms Kreps.ChoiceUnderUncertainty.anchorWeight_represents
#print axioms Kreps.ChoiceUnderUncertainty.anchorWeight_affine
#print axioms Kreps.ChoiceUnderUncertainty.representation_with_best_worst
#print axioms Kreps.ChoiceUnderUncertainty.Calibrates
#print axioms Kreps.ChoiceUnderUncertainty.exists_calibration
#print axioms Kreps.ChoiceUnderUncertainty.exists_preference_enclosure
#print axioms Kreps.ChoiceUnderUncertainty.normalized_interval_utility
#print axioms Kreps.ChoiceUnderUncertainty.calibration_eq_local
#print axioms Kreps.ChoiceUnderUncertainty.affineInMix_eq_expectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_3
#print axioms Kreps.ChoiceUnderUncertainty.mixtureAxioms_of_representation
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_4
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_3
#print axioms Kreps.ChoiceUnderUncertainty.StrictIndependence
#print axioms Kreps.ChoiceUnderUncertainty.ArchimedeanMix
#print axioms Kreps.ChoiceUnderUncertainty.mix_complement
#print axioms Kreps.ChoiceUnderUncertainty.archimedeanMix_reverse
#print axioms Kreps.ChoiceUnderUncertainty.mix_strict_both
#print axioms Kreps.ChoiceUnderUncertainty.alt_segment_bounds
#print axioms Kreps.ChoiceUnderUncertainty.mix_toward_baseline
#print axioms Kreps.ChoiceUnderUncertainty.alt_segment_mono
#print axioms Kreps.ChoiceUnderUncertainty.alt_near_better
#print axioms Kreps.ChoiceUnderUncertainty.alt_mixtureContinuous
#print axioms Kreps.ChoiceUnderUncertainty.mix_shared_baseline_comm
#print axioms Kreps.ChoiceUnderUncertainty.alt_no_strict_of_indifferent
#print axioms Kreps.ChoiceUnderUncertainty.alt_mix_strict_iff
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_11
#print axioms Kreps.ChoiceUnderUncertainty.stateAdditiveValue_difference
#print axioms Kreps.ChoiceUnderUncertainty.stateAdditive_local_comparison
#print axioms Kreps.ChoiceUnderUncertainty.stateUtility_difference_of_affine
#print axioms Kreps.ChoiceUnderUncertainty.stateUtility_shifts_of_affine
#print axioms Kreps.ChoiceUnderUncertainty.StateIndependentComparisons
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveActValue_stateIndependent
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveActValue_constant
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveProbabilities_unique
#print axioms Kreps.ChoiceUnderUncertainty.HorseLottery
#print axioms Kreps.ChoiceUnderUncertainty.mix_act_apply
#print axioms Kreps.ChoiceUnderUncertainty.HorseValue
#print axioms Kreps.ChoiceUnderUncertainty.horseValue_affine
#print axioms Kreps.ChoiceUnderUncertainty.stateIncrement_affine
#print axioms Kreps.ChoiceUnderUncertainty.horseValue_of_affine
#print axioms Kreps.ChoiceUnderUncertainty.horseRepresentation_of_affine
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_12_unique
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_affine_transform
#print axioms Kreps.ChoiceUnderUncertainty.SubjectiveHorseValue
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveHorseValue_eq_horseValue
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveHorseValue_affine
#print axioms Kreps.ChoiceUnderUncertainty.constantActs_represented_in_each_state
#print axioms Kreps.ChoiceUnderUncertainty.subjectiveRepresentation_of_stateIndependent
#print axioms Kreps.ChoiceUnderUncertainty.subjective_prize_utility_unique
#print axioms Kreps.ChoiceUnderUncertainty.subjective_probabilities_unique
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_12
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_13
#print axioms Kreps.ChoiceUnderUncertainty.MeasureCombination
#print axioms Kreps.ChoiceUnderUncertainty.measureCombination_event
#print axioms Kreps.ChoiceUnderUncertainty.probabilityMeasure_ext_real
#print axioms Kreps.ChoiceUnderUncertainty.BorelConvexSpace
#print axioms Kreps.ChoiceUnderUncertainty.borelMix_event
#print axioms Kreps.ChoiceUnderUncertainty.AtomicProbability
#print axioms Kreps.ChoiceUnderUncertainty.integral_measureCombination
#print axioms Kreps.ChoiceUnderUncertainty.integral_atomicProbability
#print axioms Kreps.ChoiceUnderUncertainty.AtomicFunctional
#print axioms Kreps.ChoiceUnderUncertainty.atomicFunctional_singleton
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.mk
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.atoms_nonneg
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.continuous
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.compact
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.density_nonneg
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityPresentation.event
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_singleton
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_unique
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_normalized
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_mix
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityDomain
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityDomain_isConvex
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityConvexSpace
#print axioms Kreps.ChoiceUnderUncertainty.AtomicDensityIndex
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityIndex_eq
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityIndex_scaled
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityIndex_affine
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityIndex_mixtureAxioms
#print axioms Kreps.ChoiceUnderUncertainty.atomicProbability_presentation
#print axioms Kreps.ChoiceUnderUncertainty.AtomicLaw
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityIndex_atomic
#print axioms Kreps.ChoiceUnderUncertainty.integral_atomicLaw
#print axioms Kreps.ChoiceUnderUncertainty.DensityProbability
#print axioms Kreps.ChoiceUnderUncertainty.densityProbability_presentation
#print axioms Kreps.ChoiceUnderUncertainty.ThreeFourBump
#print axioms Kreps.ChoiceUnderUncertainty.threeFour_support
#print axioms Kreps.ChoiceUnderUncertainty.ThreeFourLaw
#print axioms Kreps.ChoiceUnderUncertainty.threeFourLaw_range
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_literal_values
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensity_no_expectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.atomicFunctional_one
#print axioms Kreps.ChoiceUnderUncertainty.atomicWeights_normalize
#print axioms Kreps.ChoiceUnderUncertainty.compactDensity_normalize
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityPresentation_ext
#print axioms Kreps.ChoiceUnderUncertainty.atomicDensityDomain_iff_mixture
#print axioms Kreps.ChoiceUnderUncertainty.measureCombination_eq_barycenter
#print axioms Kreps.ChoiceUnderUncertainty.affineInMix_barycenter
#print axioms Kreps.ChoiceUnderUncertainty.affineInMix_atomicProbability
#print axioms Kreps.ChoiceUnderUncertainty.ImageWeights
#print axioms Kreps.ChoiceUnderUncertainty.SimpleImageLottery
#print axioms Kreps.ChoiceUnderUncertainty.simpleImageLottery_law
#print axioms Kreps.ChoiceUnderUncertainty.exists_simpleLotteries_tendsto
#print axioms Kreps.ChoiceUnderUncertainty.OpenStrictSections
#print axioms Kreps.ChoiceUnderUncertainty.affine_attains_between
#print axioms Kreps.ChoiceUnderUncertainty.openStrictSections_iff_continuous
#print axioms Kreps.ChoiceUnderUncertainty.integral_affineInMix
#print axioms Kreps.ChoiceUnderUncertainty.weakMix_tendsto
#print axioms Kreps.ChoiceUnderUncertainty.continuous_affine_bounded
#print axioms Kreps.ChoiceUnderUncertainty.borel_index_is_integral
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_10
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_10_euclidean
#print axioms Kreps.ChoiceUnderUncertainty.proposition_5_10_orthant
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.mk
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.mass
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.nonnegative
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.normalized
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.distribution
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.lottery
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.value
#print axioms Kreps.ChoiceUnderUncertainty.BranchTable.lottery_value
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_branchLottery
#print axioms Kreps.ChoiceUnderUncertainty.CertainBranch
#print axioms Kreps.ChoiceUnderUncertainty.TwoBranches
#print axioms Kreps.ChoiceUnderUncertainty.certainBranch_value
#print axioms Kreps.ChoiceUnderUncertainty.twoBranches_value
#print axioms Kreps.ChoiceUnderUncertainty.ThreeBranches
#print axioms Kreps.ChoiceUnderUncertainty.threeBranches_value
#print axioms Kreps.ChoiceUnderUncertainty.BinaryCash
#print axioms Kreps.ChoiceUnderUncertainty.binaryCash_expectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.framing_cash_laws
#print axioms Kreps.ChoiceUnderUncertainty.framing_no_strict_reversal
#print axioms Kreps.ChoiceUnderUncertainty.AllaisLotteries
#print axioms Kreps.ChoiceUnderUncertainty.allais_difference
#print axioms Kreps.ChoiceUnderUncertainty.allais_no_expectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.EllsbergBets
#print axioms Kreps.ChoiceUnderUncertainty.EllsbergUrn
#print axioms Kreps.ChoiceUnderUncertainty.ellsberg_known_odds
#print axioms Kreps.ChoiceUnderUncertainty.ellsberg_difference
#print axioms Kreps.ChoiceUnderUncertainty.ellsberg_no_subjectiveUtility
#print axioms Kreps.ChoiceUnderUncertainty.ellsberg_not_sureThing
#print axioms Kreps.ChoiceUnderUncertainty.portfolio_dependence_example
#print axioms Kreps.ChoiceUnderUncertainty.delayedCoin_value_iff
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.mk
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.draw
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.disclosure
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.payment
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.heads
#print axioms Kreps.ChoiceUnderUncertainty.TimedCoinOffer.tails
#print axioms Kreps.ChoiceUnderUncertainty.PrintedCoinOffers
#print axioms Kreps.ChoiceUnderUncertainty.printedCoinOffers_compare
#print axioms Kreps.ChoiceUnderUncertainty.expectedUtility_indicator
#print axioms Kreps.ChoiceUnderUncertainty.lottery_eq_of_all_values
#print axioms Kreps.ChoiceUnderUncertainty.Figure55Reduced
#print axioms Kreps.ChoiceUnderUncertainty.figure55_reduction
#print axioms Kreps.ChoiceUnderUncertainty.figure56_deterministic
#print axioms Kreps.ChoiceUnderUncertainty.Figure57First
#print axioms Kreps.ChoiceUnderUncertainty.Figure57Second
#print axioms Kreps.ChoiceUnderUncertainty.Figure57Reduced
#print axioms Kreps.ChoiceUnderUncertainty.figure57_reduction
#print axioms Kreps.ChoiceUnderUncertainty.DinnerAct
#print axioms Kreps.ChoiceUnderUncertainty.dinner_horses_first
#print axioms Kreps.ChoiceUnderUncertainty.MatchingDinnerValue
#print axioms Kreps.ChoiceUnderUncertainty.dinner_roulette_first
#print axioms Kreps.ChoiceUnderUncertainty.dinner_not_stateAdditive
#print axioms Kreps.ChoiceUnderUncertainty.IsEventSimple
#print axioms Kreps.ChoiceUnderUncertainty.isEventSimple_of_partition
#print axioms Kreps.ChoiceUnderUncertainty.isEventSimple_const
#print axioms Kreps.ChoiceUnderUncertainty.isEventSimple_map₂
#print axioms Kreps.ChoiceUnderUncertainty.isEventSimple_indicator
#print axioms Kreps.ChoiceUnderUncertainty.isEventSimple_paste
#print axioms Kreps.ChoiceUnderUncertainty.EventAct
#print axioms Kreps.ChoiceUnderUncertainty.eventAct_isConvex
#print axioms Kreps.ChoiceUnderUncertainty.eventActConvexSpace
#print axioms Kreps.ChoiceUnderUncertainty.EventConstant
#print axioms Kreps.ChoiceUnderUncertainty.EventCut
#print axioms Kreps.ChoiceUnderUncertainty.eventCut_apply
#print axioms Kreps.ChoiceUnderUncertainty.eventAct_mix_apply
#print axioms Kreps.ChoiceUnderUncertainty.EventMix
#print axioms Kreps.ChoiceUnderUncertainty.eventMix_apply
#print axioms Kreps.ChoiceUnderUncertainty.EventAffine
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6a
#print axioms Kreps.ChoiceUnderUncertainty.EventContribution
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_congr_event
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_empty
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_univ
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_congr_act
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_union
#print axioms Kreps.ChoiceUnderUncertainty.partitionUnion_mem
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_partitionUnion
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6b
#print axioms Kreps.ChoiceUnderUncertainty.eventContribution_complement
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6c
#print axioms Kreps.ChoiceUnderUncertainty.EventLotteryIndex
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_base
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_affine
#print axioms Kreps.ChoiceUnderUncertainty.EventPrizeUtility
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_expectedUtility
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6d
#print axioms Kreps.ChoiceUnderUncertainty.EventRanking
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_represents
#print axioms Kreps.ChoiceUnderUncertainty.eventRanking_mixtureAxioms
#print axioms Kreps.ChoiceUnderUncertainty.EventProbability
#print axioms Kreps.ChoiceUnderUncertainty.CalibrationNull
#print axioms Kreps.ChoiceUnderUncertainty.FinitelyAdditiveProbability
#print axioms Kreps.ChoiceUnderUncertainty.eventProbability_zero_iff_null
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6e
#print axioms Kreps.ChoiceUnderUncertainty.eventRepresentation_normalized
#print axioms Kreps.ChoiceUnderUncertainty.EventIndependentRankings
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_univ
#print axioms Kreps.ChoiceUnderUncertainty.eventLotteryIndex_factor
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_6f
#print axioms Kreps.ChoiceUnderUncertainty.event_sign_counterexample
#print axioms Kreps.ChoiceUnderUncertainty.SigmaEvents
#print axioms Kreps.ChoiceUnderUncertainty.sigmaEvents_isSetAlgebra
#print axioms Kreps.ChoiceUnderUncertainty.EventWeightContinuous
#print axioms Kreps.ChoiceUnderUncertainty.InitialEventUnion
#print axioms Kreps.ChoiceUnderUncertainty.initialEventUnion_succ
#print axioms Kreps.ChoiceUnderUncertainty.eventWeight_hasSum
#print axioms Kreps.ChoiceUnderUncertainty.probabilityMeasure_of_eventContinuity
#print axioms Kreps.ChoiceUnderUncertainty.probabilityMeasure_of_calibratedActs
#print axioms Kreps.ChoiceUnderUncertainty.integral_partition_value
#print axioms Kreps.ChoiceUnderUncertainty.integral_simpleHorseValue
#print axioms Kreps.ChoiceUnderUncertainty.simpleHorseValue_tendsto
#print axioms Kreps.ChoiceUnderUncertainty.InclusionProbability
#print axioms Kreps.ChoiceUnderUncertainty.InclusionLottery
#print axioms Kreps.ChoiceUnderUncertainty.inclusionProbability_lottery
#print axioms Kreps.ChoiceUnderUncertainty.inclusionLottery_probability
#print axioms Kreps.ChoiceUnderUncertainty.inclusionProbability_mix
#print axioms Kreps.ChoiceUnderUncertainty.SubsetVertex
#print axioms Kreps.ChoiceUnderUncertainty.subsetVertex_probability
#print axioms Kreps.ChoiceUnderUncertainty.subsetLottery_extension
#print axioms Kreps.ChoiceUnderUncertainty.subsetMargin_additive
#print axioms Kreps.ChoiceUnderUncertainty.wholeSubset_utility_nonadditive
#print axioms Kreps.ChoiceUnderUncertainty.subsetMargin_cube_value
#print axioms Kreps.ChoiceUnderUncertainty.Problem51Money
#print axioms Kreps.ChoiceUnderUncertainty.Problem51MoneyValue
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1a
#print axioms Kreps.ChoiceUnderUncertainty.Figure510Act
#print axioms Kreps.ChoiceUnderUncertainty.Figure510Utility
#print axioms Kreps.ChoiceUnderUncertainty.Figure510Prob
#print axioms Kreps.ChoiceUnderUncertainty.Figure510CommonUtility
#print axioms Kreps.ChoiceUnderUncertainty.figure510CommonUtility_eq_rpow
#print axioms Kreps.ChoiceUnderUncertainty.Figure510AdditiveValue
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1b
#print axioms Kreps.ChoiceUnderUncertainty.Figure510SubjectiveValue
#print axioms Kreps.ChoiceUnderUncertainty.figure510_subjective_values
#print axioms Kreps.ChoiceUnderUncertainty.figure510_root_bounds
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1c
#print axioms Kreps.ChoiceUnderUncertainty.Figure511Left
#print axioms Kreps.ChoiceUnderUncertainty.Figure511Right
#print axioms Kreps.ChoiceUnderUncertainty.Figure511Value
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1d
#print axioms Kreps.ChoiceUnderUncertainty.Figure511WeightedUtility
#print axioms Kreps.ChoiceUnderUncertainty.figure511_subjective_values
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1e
#print axioms Kreps.ChoiceUnderUncertainty.figure511Value_eq_horseValue
#print axioms Kreps.ChoiceUnderUncertainty.figure511Value_eq_subjective
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_4
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_5_whole
#print axioms Kreps.ChoiceUnderUncertainty.subsetUtility_unrestricted
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_5_marginals
#print axioms Kreps.ChoiceUnderUncertainty.strict_of_exerciseValue
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1a_preference
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1b_preference
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1c_preference
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1d_preference
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_1e_preference
#print axioms Kreps.ChoiceUnderUncertainty.lottery_mem_support_iff
#print axioms Kreps.ChoiceUnderUncertainty.lottery_mix_support
#print axioms Kreps.ChoiceUnderUncertainty.lottery_endpoint_supports
#print axioms Kreps.ChoiceUnderUncertainty.RaceOdds
#print axioms Kreps.ChoiceUnderUncertainty.RaceBet
#print axioms Kreps.ChoiceUnderUncertainty.race_sure_three
#print axioms Kreps.ChoiceUnderUncertainty.race_bet_values
#print axioms Kreps.ChoiceUnderUncertainty.bundle_lottery_values
#print axioms Kreps.ChoiceUnderUncertainty.race_sureThing
#print axioms Kreps.ChoiceUnderUncertainty.MealContextUtility
#print axioms Kreps.ChoiceUnderUncertainty.meal_dessert_reversal
#print axioms Kreps.ChoiceUnderUncertainty.advertising_two_states
#print axioms Kreps.ChoiceUnderUncertainty.advertising_three_states
#print axioms Kreps.ChoiceUnderUncertainty.advertising_threshold
#print axioms Kreps.ChoiceUnderUncertainty.umbrella_stateIndependent
#print axioms Kreps.ChoiceUnderUncertainty.umbrella_stateDependent
#print axioms Kreps.ChoiceUnderUncertainty.WorldCupTicket
#print axioms Kreps.ChoiceUnderUncertainty.worldCup_ticket_value
#print axioms Kreps.ChoiceUnderUncertainty.worldCup_thresholds
#print axioms Kreps.ChoiceUnderUncertainty.worldCup_indifference
#print axioms Kreps.ChoiceUnderUncertainty.weighted_stateUtilities_recover
#print axioms Kreps.ChoiceUnderUncertainty.problem_5_2
#print axioms Kreps.ChoiceUnderUncertainty.race_odds_not_imposed
#print axioms Kreps.ChoiceUnderUncertainty.unbounded_prize_sequence
#print axioms Kreps.ChoiceUnderUncertainty.HalfGeometric
#print axioms Kreps.ChoiceUnderUncertainty.halfGeometric_odds
#print axioms Kreps.ChoiceUnderUncertainty.GeometricPrizeLaw
#print axioms Kreps.ChoiceUnderUncertainty.geometricPrizeLaw_mass
#print axioms Kreps.ChoiceUnderUncertainty.geometric_expected_loss
#print axioms Kreps.ChoiceUnderUncertainty.unbounded_utility_lottery
#print axioms Kreps.ChoiceUnderUncertainty.exponentialUtility_gaussian
#print axioms Kreps.ChoiceUnderUncertainty.exponentialUtility_gaussianMixture
