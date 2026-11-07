import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Basic.NNReal.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Prod
import Mathlib.Geometry.Convex.Set
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Comparing risk aversion

Kreps I, Definition 6.6 and Proposition 6.7, pp. 127–129. The comparison
quantifies over every lottery and every sure prize. The inverse of the
second utility is used only on its attained range, which is convex by
continuity of that utility on the monetary interval.
-/

namespace Kreps.UtilityForMoney

/-- **Definition 6.6:** acceptance by the more risk-averse decision maker entails acceptance
by the other one, at every sure prize. -/
def MoreRiskAverse (S : Set ℝ) (W V : ℝ → ℝ) : Prop :=
  ∀ (p : SimpleLottery S) (x : S), W x ≤ ExpectedUtility (fun y : S => W y) p →
    V x ≤ ExpectedUtility (fun y : S => V y) p

/-- The transformation taking the utility scale of `V` to that of `W`. -/
noncomputable def UtilityTransform (S : Set ℝ) (W V : ℝ → ℝ) (t : ℝ) : ℝ :=
  W (Function.invFunOn V S t)

/-- At each attained utility value the transform returns the corresponding first utility. -/
theorem utilityTransform_apply {S : Set ℝ} {V : ℝ → ℝ} (W : ℝ → ℝ)
    (hV : StrictMonoOn V S) {x : ℝ} (hx : x ∈ S) :
    UtilityTransform S W V (V x) = W x :=
  congrArg W (hV.injOn.leftInvOn_invFunOn hx)

/-- The utility transform is strictly increasing on precisely the relevant range. -/
theorem utilityTransform_strictMonoOn {S : Set ℝ} {V W : ℝ → ℝ}
    (hV : StrictMonoOn V S) (hW : StrictMonoOn W S) :
    StrictMonoOn (UtilityTransform S W V) (V '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [utilityTransform_apply W hV hx, utilityTransform_apply W hV hy]
  exact hW hx hy ((hV.lt_iff_lt hx hy).mp hxy)

/-- **Proposition 6.7:** increased risk aversion is equivalent to a concave utility transform. -/
theorem proposition_6_7 {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : StrictMonoOn W S) (hV : StrictMonoOn V S)
    (hWc : ContinuousOn W S) (hVc : ContinuousOn V S) :
    MoreRiskAverse S W V ↔ ConcaveOn ℝ (V '' S) (UtilityTransform S W V) := by
  let T := UtilityTransform S W V
  have hT (x : S) : T (V x) = W x := utilityTransform_apply W hV x.property
  have hrange : Convex ℝ (V '' S) := (hS.isPreconnected.image V hVc).convex
  have hmem (x : S) : V x ∈ V '' S := Set.mem_image_of_mem V x.property
  have hinc := utilityTransform_strictMonoOn hV hW
  constructor
  · intro h
    refine ⟨hrange, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
    let x : S := ⟨v, hv⟩
    let y : S := ⟨w, hw⟩
    have hI : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    let p := BinaryLottery x y a hI
    obtain ⟨c, hc⟩ := proposition_6_5_exists hS hWc p
    have hp := h p c hc.le
    have hmean := expectedUtility_mem_of_convex hrange (fun t : S => V t) hmem p
    have hbound := hinc.monotoneOn (hmem c) hmean hp
    change T (V c) ≤ T (ExpectedUtility (fun t : S => V t) p) at hbound
    change W c = ExpectedUtility (fun t : S => W t) p at hc
    rw [hT c, hc] at hbound
    dsimp only [p] at hbound
    rw [expectedUtility_binary, expectedUtility_binary] at hbound
    change a * T (V x) + b * T (V y) ≤ T (a * V x + b * V y)
    rw [hT x, hT y]
    simpa only [show 1 - a = b by linarith] using hbound
  · intro hc p x hx
    have hj := expectedUtility_jensen hc (fun t : S => V t) hmem p
    change ExpectedUtility (fun t : S => T (V t)) p ≤
      T (ExpectedUtility (fun t : S => V t) p) at hj
    simp only [hT] at hj
    have hm := expectedUtility_mem_of_convex hrange (fun t : S => V t) hmem p
    apply (hinc.le_iff_le (hmem x) hm).mp
    change T (V x) ≤ _
    rw [hT x]
    exact hx.trans hj

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Arrow–Pratt risk aversion and power utility

Kreps I, Definition 6.10 and the relative coefficient, pp. 130–132, and Problem
6.4, p. 141. Economic uses impose positive marginal utility and appropriate
differentiability at the wealth being evaluated.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- **Definition 6.10:** the Arrow–Pratt coefficient of absolute risk aversion. -/
noncomputable def AbsoluteRiskAversion (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv U) x) / deriv U x

/-- Relative risk aversion measures curvature in proportion to wealth. -/
noncomputable def RelativeRiskAversion (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * AbsoluteRiskAversion U x

/-- Nonpositive utility curvature and strictly positive marginal utility imply nonnegative risk. -/
theorem absoluteRiskAversion_nonneg {U : ℝ → ℝ} {x : ℝ} (h₁ : 0 < deriv U x)
    (h₂ : deriv (deriv U) x ≤ 0) : 0 ≤ AbsoluteRiskAversion U x :=
  div_nonneg (neg_nonneg.mpr h₂) h₁.le

/-- The power utility specified in Problem 6.4, economically restricted to positive wealth. -/
noncomputable def PowerUtility (a x : ℝ) : ℝ := x ^ a / a

/-- The first derivative on the positive wealth domain. -/
theorem powerUtility_hasDerivAt {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    HasDerivAt (PowerUtility a) (x ^ (a - 1)) x := by
  unfold PowerUtility
  convert (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).div_const a using 1
  field_simp

/-- The second derivative on the positive wealth domain. -/
theorem powerUtility_second_deriv {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    deriv (deriv (PowerUtility a)) x = (a - 1) * x ^ (a - 1 - 1) := by
  have he : deriv (PowerUtility a) =ᶠ[𝓝 x] fun y : ℝ => y ^ (a - 1) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (powerUtility_hasDerivAt ha hy).deriv
  rw [he.deriv_eq, Real.deriv_rpow_const]

/-- **Problem 6.4:** absolute risk aversion is inversely proportional to wealth;
relative risk aversion is constant. -/
theorem problem_6_4 {a x : ℝ} (ha : a ≠ 0) (hx : 0 < x) :
    AbsoluteRiskAversion (PowerUtility a) x = (1 - a) / x ∧
      RelativeRiskAversion (PowerUtility a) x = 1 - a := by
  have hpow := (Real.rpow_pos_of_pos hx (a - 1)).ne'
  have he : AbsoluteRiskAversion (PowerUtility a) x = (1 - a) / x := by
    rw [AbsoluteRiskAversion, powerUtility_second_deriv ha hx,
      (powerUtility_hasDerivAt ha hx).deriv,
      Real.rpow_sub_one hx.ne' (a - 1)]
    field_simp
    ring
  refine ⟨he, ?_⟩
  rw [RelativeRiskAversion, he]
  field_simp

/-- A positive affine utility is risk neutral in the Arrow–Pratt sense. -/
theorem absoluteRiskAversion_affine (A B x : ℝ) :
    AbsoluteRiskAversion (fun z : ℝ => A * z + B) x = 0 := by
  have h (y : ℝ) : deriv (fun z : ℝ => A * z + B) y = A := by
    simp
  rw [AbsoluteRiskAversion, funext h]
  simp

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Insurance at fair and unfair premiums

Kreps I, Proposition 6.17, pp. 138–140. Coverage is a real number, so both
negative coverage and overinsurance are allowed. Jensen's inequality bounds
the entire objective, and the derivative at full coverage excludes it when
the premium is unfair.
-/

namespace Kreps.UtilityForMoney

/-- Expected utility of buying coverage `a` at premium `d` per unit of coverage. -/
def InsuranceUtility (V : ℝ → ℝ) (p y z d a : ℝ) : ℝ :=
  p * V (y - a * d) + (1 - p) * V (z + a * (y - z) - a * d)

/-- Full insurance makes income certain in both states. -/
theorem insuranceUtility_one (V : ℝ → ℝ) (p y z d : ℝ) :
    InsuranceUtility V p y z d 1 = V (y - d) := by
  unfold InsuranceUtility
  rw [one_mul, one_mul, show z + (y - z) - d = y - d by ring]
  ring

/-- Concavity bounds insurance utility by the utility of mean net income. -/
theorem insuranceUtility_le_mean {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d a : ℝ) :
    InsuranceUtility V p y z d a ≤
      V (p * y + (1 - p) * z + a * ((1 - p) * (y - z) - d)) := by
  have h := hc.2 (Set.mem_univ (y - a * d)) (Set.mem_univ (z + a * (y - z) - a * d))
    hp.1 (sub_nonneg.mpr hp.2) (show p + (1 - p) = 1 by ring)
  simp only [smul_eq_mul] at h
  unfold InsuranceUtility
  convert h using 2
  ring

/-- **Proposition 6.17(a):** full coverage attains a global maximum at a fair premium. -/
theorem proposition_6_17a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z : ℝ) (a : ℝ) :
    InsuranceUtility V p y z ((1 - p) * (y - z)) a ≤
      InsuranceUtility V p y z ((1 - p) * (y - z)) 1 := by
  rw [insuranceUtility_one]
  convert insuranceUtility_le_mean hc hp y z ((1 - p) * (y - z)) a using 2
  ring

/-- Strict increase and concavity make the marginal utility of real wealth positive. -/
theorem deriv_pos_of_concave_strictMono {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) {w : ℝ} (hd : DifferentiableAt ℝ V w) : 0 < deriv V w := by
  have hw : w < w + 1 := by linarith
  have h := hc.slope_le_deriv (Set.mem_univ w) (Set.mem_univ (w + 1)) hw hd
  rw [slope_def_field] at h
  exact (div_pos (sub_pos.mpr (hi hw)) (sub_pos.mpr hw)).trans_le h

/-- At full coverage the marginal benefit is the actuarial discount times marginal utility. -/
theorem insuranceUtility_hasDerivAt_one {V : ℝ → ℝ} (p y z d : ℝ)
    (hd : DifferentiableAt ℝ V (y - d)) :
    HasDerivAt (InsuranceUtility V p y z d)
      (((1 - p) * (y - z) - d) * deriv V (y - d)) 1 := by
  have h₁ : HasDerivAt (fun a : ℝ => y - a * d) (-d) 1 := by
    simpa using ((hasDerivAt_id' 1).mul_const d).const_sub y
  have h₂ : HasDerivAt (fun a : ℝ => z + a * (y - z) - a * d) (y - z - d) 1 := by
    convert (((hasDerivAt_id' (1 : ℝ)).mul_const (y - z)).const_add z).sub
      ((hasDerivAt_id' 1).mul_const d) using 1
    ring
  have h₃ : HasDerivAt V (deriv V (y - d)) (y - 1 * d) := by simpa using hd.hasDerivAt
  have h₄ : HasDerivAt V (deriv V (y - d)) (z + 1 * (y - z) - 1 * d) := by
    convert hd.hasDerivAt using 1
    ring
  convert ((h₃.comp 1 h₁).const_mul p).add ((h₄.comp 1 h₂).const_mul (1 - p)) using 1
  · rfl
  · ring

/-- **Proposition 6.17(b):** every optimum under an unfair premium is below full coverage. -/
theorem proposition_6_17b {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) {p y z d a : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hd : DifferentiableAt ℝ V (y - d)) (hunfair : (1 - p) * (y - z) < d)
    (hmax : ∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a) : a < 1 := by
  by_contra! ha
  rcases ha.eq_or_lt with he | hlt
  · subst a
    have hm : IsLocalMax (InsuranceUtility V p y z d) 1 := Filter.Eventually.of_forall hmax
    have hzero := hm.hasDerivAt_eq_zero (insuranceUtility_hasDerivAt_one p y z d hd)
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hunfair)
      (deriv_pos_of_concave_strictMono hc hi hd)
    linarith
  · have hmean := insuranceUtility_le_mean hc hp y z d a
    have h := mul_lt_mul_of_neg_right hlt (sub_neg.mpr hunfair)
    have hlt' : p * y + (1 - p) * z + a * ((1 - p) * (y - z) - d) < y - d := by
      nlinarith
    have hcontra := hmax 1
    rw [insuranceUtility_one] at hcontra
    exact (not_lt_of_ge hcontra) (hmean.trans_lt (hi hlt'))

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Demand for a risky asset

Kreps I, Problem 6.10 and Proposition 6.18, pp. 144–145. The investor chooses
any nonnegative amount of the risky asset. Leveraged positions are permitted.
The return distribution is simple with arbitrary finite support.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Taking expectations commutes with any affine change of the payoffs. -/
theorem expectedUtility_affine_payoff {X : Type*} (p : SimpleLottery X) (f : X → ℝ)
    (a b : ℝ) : ExpectedUtility (fun x => a * f x + b) p = a * ExpectedUtility f p + b := by
  classical
  have ht : ∑ x ∈ p.weights.support, p.weights x = 1 := p.total
  unfold ExpectedUtility Finsupp.sum
  simp_rw [mul_add, show ∀ x, p.weights x * (a * f x) = a * (p.weights x * f x) by
    intro x; ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ht, one_mul]

/-- A constant payoff has its own value as expectation. -/
theorem expectedUtility_const {X : Type*} (p : SimpleLottery X) (c : ℝ) :
    ExpectedUtility (fun _ : X => c) p = c := by
  simpa using expectedUtility_affine_payoff p (fun _ => (0 : ℝ)) 0 c

/-- Terminal wealth in a state with risky gross return `t`. -/
def PortfolioWealth (r w a t : ℝ) : ℝ := a * (t - r) + r * w

/-- The objective in equation (6.3), with no upper bound on the risky position. -/
noncomputable def PortfolioValue (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w a : ℝ) : ℝ :=
  ExpectedUtility (fun t => V (PortfolioWealth r w a t)) p

/-- The entire portfolio solution set includes the no-short-sale constraint. -/
def PortfolioOptima (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w : ℝ) : Set ℝ :=
  {a | 0 ≤ a ∧ ∀ b, 0 ≤ b → PortfolioValue V p r w b ≤ PortfolioValue V p r w a}

/-- Expected terminal wealth as a function of the risky investment. -/
theorem expected_portfolioWealth (p : SimpleLottery ℝ) (r w a : ℝ) :
    ExpectedUtility (PortfolioWealth r w a) p = a * (ExpectedUtility id p - r) + r * w := by
  have he : PortfolioWealth r w a = fun t => a * id t + (r * w - a * r) := by
    funext t
    simp only [PortfolioWealth, id_eq]
    ring
  rw [he, expectedUtility_affine_payoff]
  ring

/-- The zero position is riskless. -/
theorem portfolioValue_zero (V : ℝ → ℝ) (p : SimpleLottery ℝ) (r w : ℝ) :
    PortfolioValue V p r w 0 = V (r * w) := by
  simp [PortfolioValue, PortfolioWealth, expectedUtility_const]

/-- Jensen's bound for a risky portfolio. -/
theorem portfolioValue_le_mean {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (p : SimpleLottery ℝ) (r w a : ℝ) :
    PortfolioValue V p r w a ≤ V (a * (ExpectedUtility id p - r) + r * w) := by
  rw [← expected_portfolioWealth]
  exact expectedUtility_jensen hc _ (fun _ => Set.mem_univ _) p

/-- **Proposition 6.18(b):** a zero excess expected return makes zero investment optimal. -/
theorem proposition_6_18b {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : SimpleLottery ℝ} {r : ℝ} (w : ℝ) (he : ExpectedUtility id p = r) :
    0 ∈ PortfolioOptima V p r w := by
  refine ⟨le_rfl, fun a _ => ?_⟩
  simpa [he, portfolioValue_zero] using portfolioValue_le_mean hc p r w a

/-- **Proposition 6.18(a):** a negative excess expected return makes zero uniquely optimal. -/
theorem proposition_6_18a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    {p : SimpleLottery ℝ} {r : ℝ} (w : ℝ) (he : ExpectedUtility id p < r) :
    PortfolioOptima V p r w = {0} := by
  have hless (a : ℝ) (ha : 0 < a) : PortfolioValue V p r w a < PortfolioValue V p r w 0 := by
    rw [portfolioValue_zero]
    apply (portfolioValue_le_mean hc p r w a).trans_lt
    apply hi
    have hneg := mul_neg_of_pos_of_neg ha (sub_neg.mpr he)
    linarith
  ext a
  change (0 ≤ a ∧ _) ↔ a = 0
  constructor
  · intro h
    by_contra hne
    exact (not_lt_of_ge (h.2 0 le_rfl)) (hless a (lt_of_le_of_ne h.1 (Ne.symm hne)))
  · rintro rfl
    refine ⟨le_rfl, fun b hb => ?_⟩
    rcases hb.eq_or_lt with heq | hpos
    · rw [← heq]
    · exact (hless b hpos).le

/-- The marginal value at zero is fixed marginal utility times the expected excess return. -/
theorem portfolioValue_hasDerivAt_zero {V : ℝ → ℝ} (p : SimpleLottery ℝ) (r w : ℝ)
    (hd : DifferentiableAt ℝ V (r * w)) :
    HasDerivAt (PortfolioValue V p r w) (deriv V (r * w) * (ExpectedUtility id p - r)) 0 := by
  classical
  have h (t : ℝ) : HasDerivAt (fun a => p.weights t * V (PortfolioWealth r w a t))
      (p.weights t * (deriv V (r * w) * (t - r))) 0 := by
    have hg : HasDerivAt (fun a : ℝ => PortfolioWealth r w a t) (t - r) 0 := by
      simpa [PortfolioWealth] using
        (((hasDerivAt_id' (0 : ℝ)).mul_const (t - r)).add_const (r * w))
    have hv : HasDerivAt V (deriv V (r * w)) (PortfolioWealth r w 0 t) := by
      simpa [PortfolioWealth] using hd.hasDerivAt
    exact ((hv.comp 0 hg).const_mul (p.weights t))
  have hsum := HasDerivAt.fun_sum (u := p.weights.support) (fun t _ => h t)
  change HasDerivAt (PortfolioValue V p r w)
    (ExpectedUtility (fun t => deriv V (r * w) * (t - r)) p) 0 at hsum
  convert hsum using 1
  rw [show (fun t => deriv V (r * w) * (t - r)) =
    (fun t => deriv V (r * w) * id t + (-(deriv V (r * w) * r))) by
    funext t; dsimp; ring, expectedUtility_affine_payoff]
  ring

/-- A positive derivative at zero gives strictly higher values for all small positive positions. -/
theorem improves_small_positive {f : ℝ → ℝ} {m : ℝ} (hd : HasDerivAt f m 0) (hm : 0 < m) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), f 0 < f a := by
  have hs : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := fun _ ha => ne_of_gt ha
  have h := hd.tendsto_slope.mono_left (nhdsWithin_mono _ hs)
  filter_upwards [h.eventually (isOpen_Ioi.mem_nhds hm), self_mem_nhdsWithin] with a hs ha
  change 0 < a at ha
  rw [slope_def_field] at hs
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr ha)).mp hs)

/-- **Proposition 6.18(c):** positive expected excess return excludes the zero position. -/
theorem proposition_6_18c {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    {p : SimpleLottery ℝ} {r w a : ℝ} (hd : DifferentiableAt ℝ V (r * w))
    (he : r < ExpectedUtility id p) (ha : a ∈ PortfolioOptima V p r w) : 0 < a := by
  apply lt_of_le_of_ne ha.1
  rintro rfl
  have hpos : ∀ᶠ b in 𝓝[>] (0 : ℝ), 0 < b := self_mem_nhdsWithin
  obtain ⟨b, hb, hv⟩ := (hpos.and (improves_small_positive
    (portfolioValue_hasDerivAt_zero p r w hd)
    (mul_pos (deriv_pos_of_concave_strictMono hc hi hd) (sub_pos.mpr he)))).exists
  exact (not_lt_of_ge (ha.2 b (le_of_lt hb))) hv

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Marginal utility ratios and comparison of risk aversion

Kreps I, Proposition 6.8, p. 129. The derivative of the ratio of two marginal
utilities has the opposite sign to the difference between their Arrow–Pratt
coefficients. Applying Cauchy's mean value theorem on the segment between two
prizes gives a supporting affine comparison on the second utility scale.
-/

namespace Kreps.UtilityForMoney

/-- The ratio of marginal prize utilities at a common wealth. -/
noncomputable def MarginalRatio (W V : ℝ → ℝ) (x : ℝ) : ℝ := deriv W x / deriv V x

/-- Comparison of Arrow–Pratt coefficients makes the ratio of marginal utilities nonincreasing. -/
theorem antitoneOn_marginalRatio {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, DifferentiableAt ℝ (deriv W) x)
    (hV : ∀ x ∈ S, DifferentiableAt ℝ (deriv V) x)
    (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hA : ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x) :
    AntitoneOn (MarginalRatio W V) S := by
  have hd (x : ℝ) (hx : x ∈ S) := ((hW x hx).hasDerivAt.div (hV x hx).hasDerivAt (hpV x hx).ne')
  apply antitoneOn_of_deriv_nonpos hS
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxs := interior_subset hx
    change deriv (deriv W / deriv V) x ≤ 0
    rw [(hd x hxs).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := (div_le_div_iff₀ (hpV x hxs) (hpW x hxs)).mp (hA x hxs)
    nlinarith

/-- Ordered marginal ratios give the global supporting comparison between any two prizes. -/
theorem utility_le_marginalRatio_support {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, DifferentiableAt ℝ W x) (hV : ∀ x ∈ S, DifferentiableAt ℝ V x)
    (hVi : StrictMonoOn V S) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hR : AntitoneOn (MarginalRatio W V) S) {x z : ℝ} (hx : x ∈ S) (hz : z ∈ S) :
    W z ≤ W x + MarginalRatio W V x * (V z - V x) := by
  have key {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      ∃ c ∈ Set.Ioo a b, c ∈ S ∧ W b - W a = (V b - V a) * MarginalRatio W V c := by
    have hs := hS.ordConnected.out ha hb
    obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope W (deriv W) hab
      (fun t ht => (hW t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hW t (hs ⟨ht.1.le, ht.2.le⟩)).hasDerivAt) V (deriv V)
      (fun t ht => (hV t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hV t (hs ⟨ht.1.le, ht.2.le⟩)).hasDerivAt)
    have hcS := hs ⟨hc.1.le, hc.2.le⟩
    refine ⟨c, hc, hcS, ?_⟩
    unfold MarginalRatio
    field_simp [(hpV c hcS).ne']
    linarith
  rcases lt_trichotomy x z with h | rfl | h
  · obtain ⟨c, hc, hcs, he⟩ := key hx hz h
    have := mul_le_mul_of_nonneg_left (hR hx hcs hc.1.le) (sub_nonneg.mpr (hVi hx hz h).le)
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs, he⟩ := key hz hx h
    have := mul_le_mul_of_nonneg_left (hR hcs hx hc.2.le) (sub_nonneg.mpr (hVi hz hx h).le)
    nlinarith

/-- **Proposition 6.8, sufficient direction:** coefficient comparison suffices for every
lottery, on any interval of common prizes. -/
theorem moreRiskAverse_of_arrowPratt {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : ∀ x ∈ S, ContDiffAt ℝ 2 W x) (hV : ∀ x ∈ S, ContDiffAt ℝ 2 V x)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x)
    (hA : ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x) :
    MoreRiskAverse S W V := by
  have hR := antitoneOn_marginalRatio hS
    (fun x hx => ((hW x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one)
    (fun x hx => ((hV x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one) hpW hpV hA
  intro p x hx
  let R := MarginalRatio W V x
  have hpos : 0 < R := div_pos (hpW x x.property) (hpV x x.property)
  have hpt (z : S) : W z ≤ R * V z + (W x - R * V x) := by
    have h := utility_le_marginalRatio_support hS
      (fun t ht => (hW t ht).differentiableAt (by norm_num))
      (fun t ht => (hV t ht).differentiableAt (by norm_num)) hVi hpV hR x.property z.property
    dsimp [R]
    linarith
  have he : ExpectedUtility (fun z : S => W z) p ≤
      ExpectedUtility (fun z : S => R * V z + (W x - R * V x)) p := by
    apply Finset.sum_le_sum
    exact fun z _ => mul_le_mul_of_nonneg_left (hpt z) (p.nonneg z)
  rw [expectedUtility_affine_payoff] at he
  by_contra! hn
  nlinarith [mul_lt_mul_of_pos_left hn hpos]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk premium of a small symmetric gamble

Kreps I, Proposition 6.9 and Problem 6.3, pp. 130, 141. Taylor expansion on a
neighborhood of the base wealth cancels the two linear terms. A local inverse
constructs a certainty equivalent from positive marginal utility. The continuous
divided difference then converts the utility expansion to a monetary risk premium.
-/

namespace Kreps.UtilityForMoney

open Filter Topology Asymptotics

/-- Second-order Taylor remainder from smoothness at the one point where it is used. -/
theorem local_second_order_remainder {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    (fun y => U y - (U x + (y - x) * deriv U x + (y - x) ^ 2 / 2 * deriv (deriv U) x))
      =o[𝓝 x] (fun y => (y - x) ^ 2) := by
  obtain ⟨s, hs, hcs⟩ := hu.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hs
  have hx := Metric.mem_ball_self hr (x := x)
  have ht := taylor_isLittleO (convex_ball x r) hx (hcs.mono hsub)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] at ht
  apply ht.congr_left
  intro y
  have he (n : ℕ) := iteratedDerivWithin_of_isOpen (f := U) (n := n) Metric.isOpen_ball hx
  simp only [show (2 : ℕ) = 1 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval,
    he, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
  norm_num
  ring_nf
  simp

/-- Expected utility of an equal-chance gain and loss of magnitude `e` about wealth `x`. -/
noncomputable def SymmetricUtility (U : ℝ → ℝ) (x e : ℝ) : ℝ := (U (x + e) + U (x - e)) / 2

/-- The equal-probability utility average cancels its first-order term. -/
theorem symmetricUtility_remainder {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    (fun e => SymmetricUtility U x e - U x - deriv (deriv U) x / 2 * e ^ 2)
      =o[𝓝 0] (fun e : ℝ => e ^ 2) := by
  have h := local_second_order_remainder hu
  have hp : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
  have hm : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have h₁ := (h.comp_tendsto hp).congr_right (g₂ := fun e : ℝ => e ^ 2) (fun e => by
    dsimp; ring)
  have h₂ := (h.comp_tendsto hm).congr_right (g₂ := fun e : ℝ => e ^ 2) (fun e => by
    dsimp; ring)
  apply ((h₁.add h₂).const_mul_left (1 / 2 : ℝ)).congr_left
  intro e
  dsimp [SymmetricUtility]
  ring

/-- The second-order limit of the difference in expected utility. -/
theorem symmetricUtility_quotient {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x) :
    Tendsto (fun e : ℝ => (SymmetricUtility U x e - U x) / e ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv U) x / 2)) := by
  have h := symmetricUtility_remainder hu
  have hzero : ∀ e : ℝ, e ^ 2 = 0 →
      SymmetricUtility U x e - U x - deriv (deriv U) x / 2 * e ^ 2 = 0 := by
    intro e he
    obtain rfl : e = 0 := by nlinarith [sq_nonneg e]
    simp [SymmetricUtility]
  have hlim := ((isLittleO_iff_tendsto hzero).mp h).mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hm : ∀ᶠ e : ℝ in 𝓝[≠] 0, e ≠ 0 := self_mem_nhdsWithin
  have hsum := hlim.add_const (deriv (deriv U) x / 2)
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hm] with e he
  field_simp
  ring

/-- The actual local risk premium of any convergent certainty-equivalent selection. -/
theorem symmetric_premium_of_certainty_equivalent {U c : ℝ → ℝ} {x : ℝ}
    (hu : ContDiffAt ℝ 2 U x) (hp : 0 < deriv U x)
    (hc : Tendsto c (𝓝[≠] 0) (𝓝 x))
    (he : ∀ᶠ e in 𝓝[≠] (0 : ℝ), U (c e) = SymmetricUtility U x e) :
    Tendsto (fun e : ℝ => (x - c e) / e ^ 2) (𝓝[≠] 0) (𝓝 (AbsoluteRiskAversion U x / 2)) := by
  have hD : Tendsto (fun e => dslope U x (c e)) (𝓝[≠] 0) (𝓝 (deriv U x)) := by
    simpa only [dslope_same, Function.comp_def] using
      ((continuousAt_dslope_same.mpr (hu.differentiableAt (by norm_num))).tendsto.comp hc)
  have hlim := (symmetricUtility_quotient hu).neg.div hD hp.ne'
  have hh : -(deriv (deriv U) x / 2) / deriv U x = AbsoluteRiskAversion U x / 2 := by
    unfold AbsoluteRiskAversion
    ring
  rw [hh] at hlim
  apply hlim.congr'
  filter_upwards [he, hD.eventually_ne hp.ne'] with e he hne
  have h := sub_smul_dslope U x (c e)
  change (c e - x) * dslope U x (c e) = U (c e) - U x at h
  dsimp
  rw [← he, ← h]
  field_simp
  ring

/-- **Proposition 6.9 and Problem 6.3:** the symmetric gamble has an actual local certainty
equivalent, and its premium divided by the squared stake tends to half the Arrow–Pratt index. -/
theorem proposition_6_9 {U : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 U x)
    (hp : 0 < deriv U x) :
    ∃ c : ℝ → ℝ, Tendsto c (𝓝 0) (𝓝 x) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), U (c e) = SymmetricUtility U x e) ∧
      Tendsto (fun e : ℝ => (x - c e) / e ^ 2) (𝓝[≠] 0)
        (𝓝 (AbsoluteRiskAversion U x / 2)) := by
  have hd := hu.hasStrictDerivAt (by norm_num)
  let g := hd.localInverse U (deriv U x) x hp.ne'
  have hleft : g (U x) = x := (hd.eventually_left_inverse hp.ne').self_of_nhds
  have hval : Tendsto (SymmetricUtility U x) (𝓝 0) (𝓝 (U x)) := by
    have hc := hu.continuousAt.tendsto
    have hp' : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
    have hm' : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
    have ht := ((hc.comp hp').add (hc.comp hm')).div_const 2
    rw [show (U x + U x) / 2 = U x by ring] at ht
    exact ht
  have hct : Tendsto (g ∘ SymmetricUtility U x) (𝓝 0) (𝓝 x) := by
    have hct' : Tendsto (g ∘ SymmetricUtility U x) (𝓝 0) (𝓝 (g (U x))) :=
      (hd.to_localInverse hp.ne').hasDerivAt.continuousAt.tendsto.comp hval
    rwa [hleft] at hct'
  have he := hval.eventually (hd.eventually_right_inverse hp.ne')
  exact ⟨_, hct, he, symmetric_premium_of_certainty_equivalent hu hp
    (hct.mono_left nhdsWithin_le_nhds) (he.filter_mono nhdsWithin_le_nhds)⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Necessity of the Arrow–Pratt coefficient comparison

Kreps I, Proposition 6.8, p. 129. Local symmetric gambles compare the risk
premia at interior points of the common interval. Continuity extends the
coefficient inequality to included endpoints of a nondegenerate interval.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Acceptance comparisons of all simple lotteries order Arrow–Pratt coefficients at an
interior wealth, with only local twice-continuous differentiability needed there. -/
theorem arrowPratt_le_of_moreRiskAverse_interior {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interior S) (hVi : StrictMonoOn V S) (hR : MoreRiskAverse S W V)
    (hW : ContDiffAt ℝ 2 W x) (hV : ContDiffAt ℝ 2 V x)
    (hpW : 0 < deriv W x) (hpV : 0 < deriv V x) :
    AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x := by
  obtain ⟨w, hw, hwe, hwlim⟩ := proposition_6_9 hW hpW
  obtain ⟨v, hv, hve, hvlim⟩ := proposition_6_9 hV hpV
  have hs := mem_interior_iff_mem_nhds.mp hx
  have hplus : Tendsto (fun e : ℝ => x + e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ)))
  have hminus : Tendsto (fun e : ℝ => x - e) (𝓝 0) (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have horder : ∀ᶠ e in 𝓝 (0 : ℝ), w e ≤ v e := by
    filter_upwards [hw hs, hv hs, hplus hs, hminus hs, hwe, hve]
      with e hwS hvS hpS hmS hwe' hve'
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
    let p := BinaryLottery (⟨x + e, hpS⟩ : S) ⟨x - e, hmS⟩ (1 / 2) hhalf
    have hcalc (U : ℝ → ℝ) : ExpectedUtility (fun t : S => U t) p = SymmetricUtility U x e := by
      dsimp only [p]
      rw [expectedUtility_binary (fun t : S => U t) _ _ _ hhalf]
      unfold SymmetricUtility
      ring
    have he := hR p ⟨w e, hwS⟩ (by rw [hcalc]; exact hwe'.le)
    rw [hcalc, ← hve'] at he
    exact (hVi.le_iff_le hwS hvS).mp he
  have he : ∀ᶠ e in 𝓝[≠] (0 : ℝ), (x - v e) / e ^ 2 ≤ (x - w e) / e ^ 2 := by
    filter_upwards [horder.filter_mono nhdsWithin_le_nhds] with e he
    exact div_le_div_of_nonneg_right (sub_le_sub_left he x) (sq_nonneg e)
  linarith [le_of_tendsto_of_tendsto hvlim hwlim he]

/-- **Proposition 6.8:** the comparative risk criterion equals pointwise comparison of
absolute risk coefficients throughout the common nondegenerate interval. -/
theorem proposition_6_8 {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {W V : ℝ → ℝ} (hW : ∀ x ∈ S, ContDiffAt ℝ 2 W x) (hV : ∀ x ∈ S, ContDiffAt ℝ 2 V x)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < deriv W x) (hpV : ∀ x ∈ S, 0 < deriv V x) :
    MoreRiskAverse S W V ↔ ∀ x ∈ S, AbsoluteRiskAversion V x ≤ AbsoluteRiskAversion W x := by
  refine ⟨?_, moreRiskAverse_of_arrowPratt hS hW hV hVi hpW hpV⟩
  intro h x hx
  have hc {U : ℝ → ℝ} (hs : ContDiffAt ℝ 2 U x) (hp : 0 < deriv U x) :
      ContinuousAt (AbsoluteRiskAversion U) x := by
    have hd := hs.derivWithin (m := 1) (by norm_num)
    have hdd := hd.derivWithin (m := 0) (by norm_num)
    exact hdd.continuousAt.neg.div hd.continuousAt hp.ne'
  have hxcl : x ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  apply le_of_tendsto_of_tendsto
    ((hc (hV x hx) (hpV x hx)).continuousWithinAt (s := interior S))
    ((hc (hW x hx) (hpW x hx)).continuousWithinAt (s := interior S))
  filter_upwards [self_mem_nhdsWithin (a := x) (s := interior S)] with y hy
  exact arrowPratt_le_of_moreRiskAverse_interior hy hVi h (hW y (interior_subset hy))
    (hV y (interior_subset hy)) (hpW y (interior_subset hy)) (hpV y (interior_subset hy))

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Wealth shifts and absolute risk aversion

Kreps I, Definition 6.11 and Proposition 6.12, pp. 130–131. For each pair of
wealth shifts we quantify over simple lotteries whose shifted prizes remain in
the common interval. A larger risk premium corresponds to a lower certainty
equivalent once the deterministic wealth shift has been removed.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Every risk premium under `W` is at least its counterpart under `V`, since the mean is shared. -/
def PremiumOrder (S : Set ℝ) (W V : ℝ → ℝ) : Prop :=
  ∀ (p : SimpleLottery S) (w v : S),
    IsCertaintyEquivalent (fun x : S => W x) p w →
    IsCertaintyEquivalent (fun x : S => V x) p v → RiskPremium p v ≤ RiskPremium p w

/-- Ranking all premia is equivalent to the acceptance ordering in Definition 6.6. -/
theorem premiumOrder_iff_moreRiskAverse {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hWi : StrictMonoOn W S) (hVi : StrictMonoOn V S)
    (hW : ContinuousOn W S) (hV : ContinuousOn V S) :
    PremiumOrder S W V ↔ MoreRiskAverse S W V := by
  constructor
  · intro h p x hx
    obtain ⟨w, hw⟩ := proposition_6_5_exists hS hW p
    obtain ⟨v, hv⟩ := proposition_6_5_exists hS hV p
    have hp := h p w v hw hv
    have hxw := (hWi.le_iff_le x.property w.property).mp (hx.trans hw.ge)
    have hwv : (w : ℝ) ≤ v := by
      unfold RiskPremium at hp
      linarith
    exact (hVi.monotoneOn x.property v.property (hxw.trans hwv)).trans hv.le
  · intro h p w v hw hv
    have hvw := h p w hw.le
    have he := (hVi.le_iff_le w.property v.property).mp (hvw.trans hv.ge)
    unfold RiskPremium
    exact sub_le_sub_left he _

/-- The unshifted prizes for which both wealth shifts stay in the original monetary interval. -/
def ShiftDomain (S : Set ℝ) (u v : ℝ) : Set ℝ := {x | x + u ∈ S ∧ x + v ∈ S}

/-- The overlapping shifted domain is convex, including empty and singleton overlaps. -/
theorem shiftDomain_convex {S : Set ℝ} (hS : Convex ℝ S) (u v : ℝ) :
    Convex ℝ (ShiftDomain S u v) := by
  intro x hx y hy a b ha hb hab
  have h (t : ℝ) (hxt : x + t ∈ S) (hyt : y + t ∈ S) :
      a • x + b • y + t ∈ S := by
    convert hS hxt hyt ha hb hab using 1
    simp only [smul_eq_mul]
    linear_combination -t * hab
  exact ⟨h u hx.1 hy.1, h v hx.2 hy.2⟩

/-- An absolute risk comparison after two shifts uses each utility on exactly its shared domain. -/
def ShiftPremiumOrder (S : Set ℝ) (U : ℝ → ℝ) (u v : ℝ) : Prop :=
  PremiumOrder (ShiftDomain S u v) (fun t => U (t + u)) (fun t => U (t + v))

/-- The local coefficient at a shifted prize is the original coefficient at final wealth. -/
theorem absoluteRiskAversion_shift (U : ℝ → ℝ) (u x : ℝ) :
    AbsoluteRiskAversion (fun t => U (t + u)) x = AbsoluteRiskAversion U (x + u) := by
  simp only [AbsoluteRiskAversion, funext (deriv_comp_add_const U u),
    deriv_comp_add_const]

/-- The shifted premium relation can be evaluated using acceptance comparisons. -/
theorem shiftPremiumOrder_iff {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hc : ContinuousOn U S) (u v : ℝ) :
    ShiftPremiumOrder S U u v ↔
      MoreRiskAverse (ShiftDomain S u v) (fun t => U (t + u)) (fun t => U (t + v)) := by
  apply premiumOrder_iff_moreRiskAverse (shiftDomain_convex hS u v)
  · intro x hx y hy hxy
    exact hi hx.1 hy.1 (by linarith)
  · intro x hx y hy hxy
    exact hi hx.2 hy.2 (by linarith)
  · exact hc.comp (continuous_id.add_const u).continuousOn (fun _ hx => hx.1)
  · exact hc.comp (continuous_id.add_const v).continuousOn (fun _ hx => hx.2)

/-- Coefficient comparisons in the entire overlap imply ordering of every shifted premium. -/
theorem shiftPremiumOrder_of_coefficient {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) (u v : ℝ)
    (hA : ∀ x ∈ ShiftDomain S u v,
      AbsoluteRiskAversion U (x + v) ≤ AbsoluteRiskAversion U (x + u)) :
    ShiftPremiumOrder S U u v := by
  have hc : ContinuousOn U S := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  apply (shiftPremiumOrder_iff hS hi hc u v).mpr
  apply moreRiskAverse_of_arrowPratt (shiftDomain_convex hS u v)
  · exact fun x hx => (hU _ hx.1).comp x (contDiffAt_id.add contDiffAt_const)
  · exact fun x hx => (hU _ hx.2).comp x (contDiffAt_id.add contDiffAt_const)
  · exact fun _ hx _ hy h => hi hx.2 hy.2 (by linarith)
  · intro x hx
    rw [deriv_comp_add_const]
    exact hp _ hx.1
  · intro x hx
    rw [deriv_comp_add_const]
    exact hp _ hx.2
  · simpa only [absoluteRiskAversion_shift] using hA

/-- At any two interior wealth levels, ordering the shifted premia orders the coefficients. -/
theorem coefficient_le_of_shiftPremiumOrder {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) {u v : ℝ} (hu : u ∈ interior S) (hv : v ∈ interior S)
    (h : ShiftPremiumOrder S U u v) : AbsoluteRiskAversion U v ≤ AbsoluteRiskAversion U u := by
  have hc : ContinuousOn U S := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  have hn (t : ℝ) (ht : t ∈ interior S) : ∀ᶠ e : ℝ in 𝓝 0, e + t ∈ S := by
    have he : Tendsto (fun e : ℝ => e + t) (𝓝 0) (𝓝 t) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add_const t
    exact he (mem_interior_iff_mem_nhds.mp ht)
  have hx : 0 ∈ interior (ShiftDomain S u v) :=
    mem_interior_iff_mem_nhds.mpr ((hn u hu).and (hn v hv))
  have hcu : ContDiffAt ℝ 2 (fun e : ℝ => U (e + u)) 0 := by
    apply ContDiffAt.comp (g := U) (f := fun e : ℝ => e + u)
    · simpa using hU u (interior_subset hu)
    · fun_prop
  have hcv : ContDiffAt ℝ 2 (fun e : ℝ => U (e + v)) 0 := by
    apply ContDiffAt.comp (g := U) (f := fun e : ℝ => e + v)
    · simpa using hU v (interior_subset hv)
    · fun_prop
  have hVi : StrictMonoOn (fun e : ℝ => U (e + v)) (ShiftDomain S u v) :=
    fun _ ha _ hb hab => hi ha.2 hb.2 (by linarith)
  have hp' (t : ℝ) (ht : t ∈ S) : 0 < deriv (fun e : ℝ => U (e + t)) 0 := by
    simpa [deriv_comp_add_const] using hp t ht
  have he := arrowPratt_le_of_moreRiskAverse_interior hx hVi
    ((shiftPremiumOrder_iff hS hi hc u v).mp h) hcu hcv
      (hp' u (interior_subset hu)) (hp' v (interior_subset hv))
  simpa only [absoluteRiskAversion_shift, zero_add] using he

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Monotone and constant absolute risk aversion

Kreps I, Definition 6.11 and Proposition 6.12, pp. 130–131. The interval
proof treats both possible endpoints and allows singleton overlaps of shifted
domains. The strictly increasing, decreasing and constant cases use the same
acceptance comparison on the overlap.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- A continuous scalar function that is nondecreasing in the interior is nondecreasing
on the entire nondegenerate real interval. -/
theorem monotoneOn_interval_of_interior {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {f : ℝ → ℝ} (hf : ContinuousOn f S) (hm : MonotoneOn f (interior S)) : MonotoneOn f S := by
  have hd (x : ℝ) (hx : x ∈ S) : NeBot (𝓝[interior S] x) := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have hright {x y : ℝ} (hx : x ∈ interior S) (hy : y ∈ S) (hxy : x < y) : f x ≤ f y := by
    have := hd y hy
    apply ge_of_tendsto ((hf y hy).mono interior_subset)
    have he : ∀ᶠ t in 𝓝[interior S] y, x < t :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hxy)
    filter_upwards [he, self_mem_nhdsWithin] with t hxt ht
    exact hm hx ht hxt.le
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  have := hd x hx
  apply le_of_tendsto ((hf x hx).mono interior_subset)
  have he : ∀ᶠ t in 𝓝[interior S] x, t < y :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds h)
  filter_upwards [he, self_mem_nhdsWithin] with t hty ht
  exact hright ht hy hty

/-- With smooth utility and nonzero marginal utility, the Arrow–Pratt ratio is continuous. -/
theorem absoluteRiskAversion_continuousOn {S : Set ℝ} {U : ℝ → ℝ}
    (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x) (hp : ∀ x ∈ S, 0 < deriv U x) :
    ContinuousOn (AbsoluteRiskAversion U) S := by
  intro x hx
  have hd := (hU x hx).derivWithin (m := 1) (by norm_num)
  have hdd := hd.derivWithin (m := 0) (by norm_num)
  exact (hdd.continuousAt.neg.div hd.continuousAt (hp x hx).ne').continuousWithinAt

/-- **Definition 6.11:** deterministic increases in wealth weakly decrease every risk premium. -/
def NonincreasingRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, u ≤ v → ShiftPremiumOrder S U u v

/-- **Definition 6.11:** deterministic increases in wealth weakly increase every risk premium. -/
def NondecreasingRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, u ≤ v → ShiftPremiumOrder S U v u

/-- **Definition 6.11:** all feasible deterministic shifts preserve every risk premium. -/
def ConstantRiskAversion (S : Set ℝ) (U : ℝ → ℝ) : Prop :=
  NonincreasingRiskAversion S U ∧ NondecreasingRiskAversion S U

/-- **Proposition 6.12:** nondecreasing risk aversion iff the coefficient is nondecreasing. -/
theorem proposition_6_12_nondecreasing {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    NondecreasingRiskAversion S U ↔ MonotoneOn (AbsoluteRiskAversion U) S := by
  constructor
  · intro h
    apply monotoneOn_interval_of_interior hS hI (absoluteRiskAversion_continuousOn hU hp)
    exact fun _ hx _ hy hxy => coefficient_le_of_shiftPremiumOrder hS hi hU hp hy hx (h _ _ hxy)
  · intro h u v huv
    apply shiftPremiumOrder_of_coefficient hS hi hU hp
    exact fun _ hx => h hx.2 hx.1 (by linarith)

/-- **Proposition 6.12:** nonincreasing risk aversion iff the coefficient is nonincreasing. -/
theorem proposition_6_12_nonincreasing {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    NonincreasingRiskAversion S U ↔ AntitoneOn (AbsoluteRiskAversion U) S := by
  constructor
  · intro h
    have hm : MonotoneOn (fun x => -AbsoluteRiskAversion U x) S := by
      apply monotoneOn_interval_of_interior hS hI (absoluteRiskAversion_continuousOn hU hp).neg
      intro x hx y hy hxy
      exact neg_le_neg (coefficient_le_of_shiftPremiumOrder hS hi hU hp hx hy (h _ _ hxy))
    exact fun _ hx _ hy hxy => neg_le_neg_iff.mp (hm hx hy hxy)
  · intro h u v huv
    apply shiftPremiumOrder_of_coefficient hS hi hU hp
    exact fun _ hx => h hx.1 hx.2 (by linarith)

/-- **Proposition 6.12:** shift-invariant premia iff the coefficient has one common value. -/
theorem proposition_6_12_constant {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ∀ x ∈ S, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ S, 0 < deriv U x) :
    ConstantRiskAversion S U ↔ ∃ k : ℝ, ∀ x ∈ S, AbsoluteRiskAversion U x = k := by
  rw [ConstantRiskAversion, proposition_6_12_nonincreasing hS hI hi hU hp,
    proposition_6_12_nondecreasing hS hI hi hU hp]
  constructor
  · rintro ⟨ha, hm⟩
    obtain ⟨x, hx⟩ := hI
    refine ⟨AbsoluteRiskAversion U x, fun y hy => ?_⟩
    rcases le_total x y with h | h
    · exact (ha (interior_subset hx) hy h).antisymm (hm (interior_subset hx) hy h)
    · exact (hm hy (interior_subset hx) h).antisymm (ha hy (interior_subset hx) h)
  · rintro ⟨k, hk⟩
    constructor <;> intro x hx y hy _ <;> rw [hk x hx, hk y hy]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The constant-absolute-risk-aversion utility family

Kreps I, Proposition 6.12, p. 131. Solving the constant-coefficient differential
equation on the monetary interval gives a positive affine transform of negative
exponential utility. At coefficient zero the solution is positive affine in wealth.
-/

namespace Kreps.UtilityForMoney

/-- Negative exponential utility for a consumer with absolute risk aversion `k`. -/
noncomputable def ExponentialUtility (k x : ℝ) : ℝ := -Real.exp (-k * x)

/-- Derivative of exponential utility at any wealth. -/
theorem exponentialUtility_hasDerivAt (k x : ℝ) :
    HasDerivAt (ExponentialUtility k) (k * Real.exp (-k * x)) x := by
  have h := (((hasDerivAt_id' x).const_mul (-k)).exp).neg
  convert h using 1
  · rfl
  · ring

/-- With positive coefficient, exponential utility is strictly increasing. -/
theorem exponentialUtility_strictMono {k : ℝ} (hk : 0 < k) : StrictMono (ExponentialUtility k) := by
  intro x y hxy
  apply neg_lt_neg
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hxy (neg_neg_of_pos hk))

/-- Exponential utility is strictly concave at every wealth when the coefficient is positive. -/
theorem exponentialUtility_strictConcave {k : ℝ} (hk : 0 < k) :
    StrictConcaveOn ℝ Set.univ (ExponentialUtility k) := by
  have hd := funext fun x => (exponentialUtility_hasDerivAt k x).deriv
  apply StrictAnti.strictConcaveOn_univ_of_deriv
  · exact continuous_iff_continuousAt.mpr fun x => (exponentialUtility_hasDerivAt k x).continuousAt
  · rw [hd]
    intro x y hxy
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hxy (neg_neg_of_pos hk))) hk

/-- Exponential utility has the advertised constant Arrow–Pratt coefficient. -/
theorem absoluteRiskAversion_exponential {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    AbsoluteRiskAversion (ExponentialUtility k) x = k := by
  have hd := funext fun t => (exponentialUtility_hasDerivAt k t).deriv
  have h₂ := ((((hasDerivAt_id' x).const_mul (-k)).exp).const_mul k).deriv
  rw [AbsoluteRiskAversion, hd, h₂]
  field_simp [Real.exp_ne_zero]

/-- Vanishing derivative forces constancy on a real interval using the mean value theorem. -/
theorem eq_on_interval_of_deriv_zero {S : Set ℝ} (hS : Convex ℝ S) {f : ℝ → ℝ}
    (hd : ∀ x ∈ S, HasDerivAt f 0 x) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have h {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) : f a = f b := by
    have hs := hS.ordConnected.out ha hb
    obtain ⟨_, _, he⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab
      (fun t ht => (hd t (hs ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hs ⟨ht.1.le, ht.2.le⟩))
    have hzero := (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr hab.ne')
    exact (sub_eq_zero.mp hzero).symm
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact h hx hy hxy
  · rfl
  · exact (h hy hx hyx).symm

/-- A constant coefficient gives an exponential marginal utility on the whole interval. -/
theorem marginal_of_constant_coefficient {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    (k : ℝ) (hk : ∀ x ∈ S, AbsoluteRiskAversion U x = k) :
    ∃ c > 0, ∀ x ∈ S, deriv U x = c * Real.exp (-k * x) := by
  obtain ⟨w, hw⟩ := hne
  let F := fun x => deriv U x * Real.exp (k * x)
  have hd (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    have he := (div_eq_iff (hp x hx).ne').mp (hk x hx)
    have h := (h₂ x hx).hasDerivAt.mul (((hasDerivAt_id' x).const_mul k).exp)
    convert h using 1
    linear_combination Real.exp (k * x) * he
  refine ⟨F w, mul_pos (hp w hw) (Real.exp_pos _), ?_⟩
  intro x hx
  have he := eq_on_interval_of_deriv_zero hS hd hx hw
  rw [← he]
  dsimp [F]
  rw [mul_assoc, ← Real.exp_add, show k * x + -k * x = 0 by ring, Real.exp_zero, mul_one]

/-- **Proposition 6.12, exponential case:** a positive constant coefficient determines the
utility up to positive affine transformation on its interval. -/
theorem proposition_6_12_exponential {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₁ : ∀ x ∈ S, DifferentiableAt ℝ U x)
    (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    {k : ℝ} (hk : 0 < k) (hc : ∀ x ∈ S, AbsoluteRiskAversion U x = k) :
    ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * ExponentialUtility k x := by
  obtain ⟨c, hc', hd⟩ := marginal_of_constant_coefficient hS hne h₂ hp k hc
  obtain ⟨w, hw⟩ := hne
  let B := c / k
  let F := fun x => U x - B * ExponentialUtility k x
  have hf (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    convert (h₁ x hx).hasDerivAt.sub ((exponentialUtility_hasDerivAt k x).const_mul B) using 1
    rw [hd x hx]
    dsimp [B]
    field_simp
    ring
  refine ⟨F w, B, div_pos hc' hk, fun x hx => ?_⟩
  have he := eq_on_interval_of_deriv_zero hS hf hx hw
  dsimp [F] at he ⊢
  linarith

/-- **Proposition 6.12, zero case:** a zero coefficient determines a positive affine utility. -/
theorem proposition_6_12_affine {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty)
    {U : ℝ → ℝ} (h₁ : ∀ x ∈ S, DifferentiableAt ℝ U x)
    (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv U) x) (hp : ∀ x ∈ S, 0 < deriv U x)
    (hc : ∀ x ∈ S, AbsoluteRiskAversion U x = 0) :
    ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * x := by
  obtain ⟨c, hc', hd⟩ := marginal_of_constant_coefficient hS hne h₂ hp 0 hc
  obtain ⟨w, hw⟩ := hne
  let F := fun x => U x - c * x
  have hf (x : ℝ) (hx : x ∈ S) : HasDerivAt F 0 x := by
    convert (h₁ x hx).hasDerivAt.sub ((hasDerivAt_id' x).const_mul c) using 1
    simp [hd x hx]
  refine ⟨F w, c, hc', fun x hx => ?_⟩
  have he := eq_on_interval_of_deriv_zero hS hf hx hw
  dsimp [F] at he ⊢
  linarith

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The numerical CARA calibration of Problem 6.2

Kreps I, pp. 140–141. Writing `q = exp (-200 * k)` turns the $2,400
certainty-equivalent restriction into a polynomial equation. Removing its
extraneous risk-neutral root yields a monotone comparison of geometric sums.
The numerical brackets and all three choice comparisons use exact rationals.
-/

namespace Kreps.UtilityForMoney

/-- A monotone rescaling of the calibration polynomial on the positive unit interval. -/
noncomputable def CalibrationGap (q : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 13, q ^ i) - q⁻¹ * ∑ i ∈ Finset.range 12, q⁻¹ ^ i

/-- The rescaled expression has the same zero as the indifference equation for positive risk. -/
theorem calibrationGap_identity {q : ℝ} (hq : q ∈ Set.Ioo 0 1) :
    q ^ 12 * (1 - q) * CalibrationGap q = 2 * q ^ 12 - 1 - q ^ 25 := by
  have hi : 1 < q⁻¹ := (one_lt_inv₀ hq.1).mpr hq.2
  rw [CalibrationGap, geom_sum_eq hq.2.ne, geom_sum_eq hi.ne']
  field_simp [hq.1.ne', sub_ne_zero.mpr hq.2.ne, sub_ne_zero.mpr hi.ne']
  field_simp [sub_ne_zero.mpr hq.2.ne']
  ring

/-- Monotonicity of the rescaling follows from opposite movements of two geometric sums. -/
theorem calibrationGap_monotone : MonotoneOn CalibrationGap (Set.Ioi 0) := by
  intro a ha b hb hab
  have hi : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab
  have hp (n : ℕ) : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha.le hab n
  have hq (n : ℕ) : b⁻¹ ^ n ≤ a⁻¹ ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hi n
  apply sub_le_sub (Finset.sum_le_sum fun i _ => hp i)
  apply mul_le_mul hi (Finset.sum_le_sum fun i _ => hq i)
  · exact Finset.sum_nonneg fun _ _ => pow_nonneg (inv_nonneg.mpr hb.le) _
  · exact inv_nonneg.mpr ha.le

/-- Exact rational bounds isolate every positive-risk solution of the calibration equation. -/
theorem calibration_bounds {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (he : 2 * q ^ 12 = 1 + q ^ 25) : (9936/10000 : ℝ) < q ∧ q < (9937/10000 : ℝ) := by
  have hgap : CalibrationGap q = 0 := by
    have h := calibrationGap_identity hq
    rw [he] at h
    have hp : 0 < q ^ 12 * (1 - q) := mul_pos (pow_pos hq.1 _) (sub_pos.mpr hq.2)
    have hz : q ^ 12 * (1 - q) * CalibrationGap q = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hp.ne'
  have hlo : CalibrationGap (9936/10000) < 0 := by norm_num [CalibrationGap, Finset.sum_range_succ]
  have hhi : 0 < CalibrationGap (9937/10000) := by norm_num [CalibrationGap, Finset.sum_range_succ]
  constructor
  · by_contra! h
    have hh := calibrationGap_monotone hq.1 (by norm_num : (9936/10000 : ℝ) ∈ Set.Ioi 0) h
    linarith
  · by_contra! h
    have hh := calibrationGap_monotone (by norm_num : (9937/10000 : ℝ) ∈ Set.Ioi 0) hq.1 h
    linarith

/-- The calibration is attainable for a strictly positive coefficient. -/
theorem calibrated_root_exists :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, 2 * q ^ 12 = 1 + q ^ 25 := by
  let f := fun t : ℝ => 2 * t ^ 12 - 1 - t ^ 25
  have hc : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨q, hq, he⟩ := intermediate_value_Icc (f := f)
    (show (9936/10000 : ℝ) ≤ 9937/10000 by norm_num) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f (9936/10000)) (f (9937/10000)) by constructor <;> norm_num [f])
  exact ⟨q, ⟨lt_of_lt_of_le (by norm_num) hq.1, lt_of_le_of_lt hq.2 (by norm_num)⟩, by
    dsimp [f] at he
    linarith⟩

/-- At any calibrated coefficient alternative B has the lowest disutility, followed by C and A. -/
theorem calibrated_disutility_rankings {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (he : 2 * q ^ 12 = 1 + q ^ 25) :
    3/5 * q ^ 25 + 2/5 / q ^ 5 < 2/5 * q ^ 25 + 3/10 + 3/10 * q ^ 5 ∧
      2/5 * q ^ 25 + 3/10 + 3/10 * q ^ 5 < q ^ 10 := by
  obtain ⟨hl, hh⟩ := calibration_bounds hq he
  have hlo (n : ℕ) := pow_le_pow_left₀ (by norm_num : 0 ≤ (9936/10000 : ℝ)) hl.le n
  have hhi (n : ℕ) := pow_le_pow_left₀ hq.1.le hh.le n
  have hinv := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2/5)
    (show 0 < (9936 / 10000 : ℝ) ^ 5 by norm_num) (hlo 5))
  constructor
  · linarith [hlo 25, hlo 5, hhi 25, hinv]
  · linarith [hhi 25, hhi 5, hlo 10]

/-- Utility of the three alternatives as actually offered, including the negative prize. -/
def CalibratedChoicesRanked (U : ℝ → ℝ) : Prop :=
  U 2000 < 2/5 * U 5000 + 3/10 * U 0 + 3/10 * U 1000 ∧
    2/5 * U 5000 + 3/10 * U 0 + 3/10 * U 1000 < 3/5 * U 5000 + 2/5 * U (-1000)

/-- Exponential disutilities at all five prizes are integer powers of the $200 discount factor. -/
theorem exponential_calibration_prizes (k : ℝ) :
    let q := Real.exp (-200 * k)
    ExponentialUtility k 0 = -1 ∧ ExponentialUtility k 1000 = -q ^ 5 ∧
      ExponentialUtility k 2000 = -q ^ 10 ∧ ExponentialUtility k 2400 = -q ^ 12 ∧
      ExponentialUtility k 5000 = -q ^ 25 ∧ ExponentialUtility k (-1000) = -(q ^ 5)⁻¹ := by
  dsimp only
  have hex (n : ℕ) : Real.exp (-k * (200 * (n : ℝ))) = Real.exp (-200 * k) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold ExponentialUtility
  norm_num at *
  have h5 := hex 5
  have h10 := hex 10
  have h12 := hex 12
  have h25 := hex 25
  norm_num at h5 h10 h12 h25
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [← h5, ← Real.exp_neg]
  congr 2
  ring

/-- **Problem 6.2:** positive affine rescalings of the calibrated exponential utility rank
the risky $5,000/$−1,000 alternative above C, and C above $2,000 for certain. -/
theorem problem_6_2 {U : ℝ → ℝ} {A B k : ℝ} (hB : 0 < B) (hk : 0 < k)
    (hU : ∀ x ∈ Set.Icc (-1000 : ℝ) 5000, U x = A + B * ExponentialUtility k x)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  let q := Real.exp (-200 * k)
  have hq : q ∈ Set.Ioo 0 1 := ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  obtain ⟨h0, h1, h2, h24, h5, hn⟩ := exponential_calibration_prizes k
  change ExponentialUtility k 2400 = -q ^ 12 at h24
  change ExponentialUtility k 5000 = -q ^ 25 at h5
  have hcal : 2 * q ^ 12 = 1 + q ^ 25 := by
    rw [hU 5000 (by norm_num), hU 0 (by norm_num), hU 2400 (by norm_num), h5, h0, h24] at he
    apply (mul_right_injective₀ hB.ne')
    linarith
  have hr := calibrated_disutility_rankings hq hcal
  unfold CalibratedChoicesRanked
  rw [hU 2000 (by norm_num), hU 5000 (by norm_num), hU 0 (by norm_num),
    hU 1000 (by norm_num), hU (-1000) (by norm_num), h2, h5, h0, h1, hn]
  change ExponentialUtility k 2000 = -q ^ 10 at h2
  change ExponentialUtility k 1000 = -q ^ 5 at h1
  change ExponentialUtility k (-1000) = -(q ^ 5)⁻¹ at hn
  dsimp only [q] at hr ⊢
  simp only [div_eq_mul_inv] at hr ⊢
  constructor <;> nlinarith [mul_pos hB (sub_pos.mpr hr.1), mul_pos hB (sub_pos.mpr hr.2)]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Behavioral calibration and attainability of Problem 6.2

Kreps I, Problem 6.2, pp. 140–141. Preferences with constant absolute risk
aversion on the stated prize interval select B, then C, then A. Concavity
forces a nonnegative coefficient, and the reported certainty equivalent excludes
the affine risk-neutral case. A positive exponential coefficient satisfying the
reported indifference exists.
-/

namespace Kreps.UtilityForMoney

/-- The range on which the consumer reports constant absolute risk aversion. -/
def CalibrationInterval : Set ℝ := Set.Icc (-1000) 5000

/-- **Problem 6.2 from primitive utility properties:** classification of CARA preferences
and the certainly-equivalent dollar amount imply the strict ranking of the three offers. -/
theorem problem_6_2_behavioral {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ConcaveOn ℝ CalibrationInterval U) (hs : ∀ x ∈ CalibrationInterval, ContDiffAt ℝ 2 U x)
    (hp : ∀ x ∈ CalibrationInterval, 0 < deriv U x)
    (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  have h₁ (x : ℝ) (hx : x ∈ CalibrationInterval) := (hs x hx).differentiableAt (by norm_num)
  have h₂ (x : ℝ) (hx : x ∈ CalibrationInterval) :=
    ((hs x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one
  obtain ⟨k, hk⟩ := (proposition_6_12_constant (convex_Icc _ _) ⟨0, hz⟩ hi hs hp).mp hC
  have hneg := (hc.antitoneOn_deriv h₁).derivWithin_nonpos (x := 0)
  rw [derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)] at hneg
  have hnonneg := absoluteRiskAversion_nonneg (hp 0 (interior_subset hz)) hneg
  rw [hk 0 (interior_subset hz)] at hnonneg
  rcases hnonneg.eq_or_lt with hzero | hpos
  · subst k
    obtain ⟨A, B, hB, hrep⟩ := proposition_6_12_affine hc.1 ⟨0, interior_subset hz⟩ h₁ h₂ hp hk
    rw [hrep 5000 (by norm_num [CalibrationInterval]), hrep 0 (by norm_num [CalibrationInterval]),
      hrep 2400 (by norm_num [CalibrationInterval])] at he
    linarith
  · obtain ⟨A, B, hB, hrep⟩ :=
      proposition_6_12_exponential hc.1 ⟨0, interior_subset hz⟩ h₁ h₂ hp hpos hk
    exact problem_6_2 hB hpos hrep he

/-- Some strictly risk-averse exponential consumer actually reports the specified certainty
equivalent and makes the predicted choices. -/
theorem problem_6_2_compatible_consumer :
    ∃ k > 0, ConstantRiskAversion CalibrationInterval (ExponentialUtility k) ∧
      ((ExponentialUtility k 5000 + ExponentialUtility k 0) / 2 = ExponentialUtility k 2400) ∧
      CalibratedChoicesRanked (ExponentialUtility k) := by
  obtain ⟨q, hq, hcal⟩ := calibrated_root_exists
  let k := -(Real.log q) / 200
  have hk : 0 < k := div_pos (neg_pos.mpr (Real.log_neg hq.1 hq.2)) (by norm_num)
  have heq : Real.exp (-200 * k) = q := by
    rw [show -200 * k = Real.log q by dsimp [k]; ring, Real.exp_log hq.1]
  obtain ⟨h0, _, _, h24, h5, _⟩ := exponential_calibration_prizes k
  have he : (ExponentialUtility k 5000 + ExponentialUtility k 0) / 2 =
      ExponentialUtility k 2400 := by
    rw [h5, h24, h0, heq]
    linarith
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  refine ⟨k, hk, ?_, he, ?_⟩
  · apply (proposition_6_12_constant (convex_Icc _ _) ⟨0, hz⟩
      ((exponentialUtility_strictMono hk).strictMonoOn CalibrationInterval)
      (fun x _ => by unfold ExponentialUtility; fun_prop)
      (fun x _ => by rw [(exponentialUtility_hasDerivAt k x).deriv]; positivity)).mpr
    exact ⟨k, fun x _ => absoluteRiskAversion_exponential hk.ne' x⟩
  · apply problem_6_2 (A := 0) (B := 1) zero_lt_one hk _ he
    exact fun x _ => by simp

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Ranking the offers in Problem 6.2 from constant risk premia

Kreps I, Problem 6.2, pp. 140–141. Equal risk premia preserve the certainty equivalents
of endpoint lotteries after a $200 wealth shift. Their indifferences pin down a single
positive affine transformation on the overlap. Iterating this transformation on the
finite prize grid gives the rankings from the stated $2400 certainty equivalent.
-/

namespace Kreps.UtilityForMoney

/-- Two opposite premium comparisons preserve every certainty equivalent on a convex interval. -/
theorem certaintyEquivalent_of_equal_premia {S : Set ℝ} (hS : Convex ℝ S) {U V : ℝ → ℝ}
    (hc : ContinuousOn V S) (huv : PremiumOrder S U V) (hvu : PremiumOrder S V U)
    (p : SimpleLottery S) {c : S} (h : IsCertaintyEquivalent (fun z : S => U z) p c) :
    IsCertaintyEquivalent (fun z : S => V z) p c := by
  obtain ⟨d, hd⟩ := proposition_6_5_exists hS hc p
  have hcd := huv p c d h hd
  have hdc := hvu p d c hd h
  have he : c = d := by
    apply Subtype.ext
    unfold RiskPremium at hcd hdc
    linarith
  exact he ▸ hd

/-- On the common prize interval a $200 wealth shift is a positive affine change of index. -/
theorem calibration_shift_affine {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ContinuousOn U CalibrationInterval) (hC : ConstantRiskAversion CalibrationInterval U) :
    ∃ q > 0, ∃ b, ∀ x ∈ Set.Icc (-1000 : ℝ) 4800, U (x + 200) = q * U x + b := by
  let S := Set.Icc (-1000 : ℝ) 4800
  have dom : ShiftDomain CalibrationInterval 0 200 = S := by
    ext x
    change ((-1000 ≤ x + 0 ∧ x + 0 ≤ 5000) ∧ -1000 ≤ x + 200 ∧ x + 200 ≤ 5000) ↔ _
    change _ ↔ -1000 ≤ x ∧ x ≤ 4800
    constructor
    · rintro ⟨⟨hl, _⟩, _, hh⟩
      constructor <;> linarith
    · rintro ⟨hl, hh⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have revdom : ShiftDomain CalibrationInterval 200 0 = S := by
    rw [← dom]
    ext x
    exact and_comm
  have forward := hC.1 0 200 (by norm_num)
  have backward := hC.2 0 200 (by norm_num)
  simp only [ShiftPremiumOrder, dom, revdom, add_zero] at forward backward
  have cont : ContinuousOn (fun z => U (z + 200)) S :=
    hc.comp (continuous_id.add_const 200).continuousOn (fun x hx => by
      have hh := hx.2
      have hl := hx.1
      exact ⟨by linarith, by linarith⟩)
  have endpoints : U (-1000) < U 4800 :=
    hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  have shifted : U (-800) < U 5000 :=
    hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  let q := (U 5000 - U (-800)) / (U 4800 - U (-1000))
  refine ⟨q, div_pos (sub_pos.mpr shifted) (sub_pos.mpr endpoints),
    U (-800) - q * U (-1000), ?_⟩
  intro x hx
  have hxc : x ∈ CalibrationInterval := ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hlo := hi.monotoneOn (by norm_num [CalibrationInterval]) hxc hx.1
  have hhi := hi.monotoneOn hxc (by norm_num [CalibrationInterval]) hx.2
  let a := (U x - U (-1000)) / (U 4800 - U (-1000))
  have ha : a ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr endpoints.le),
      (div_le_one (sub_pos.mpr endpoints)).mpr (by linarith)⟩
  let high : S := ⟨4800, by norm_num [S]⟩
  let low : S := ⟨-1000, by norm_num [S]⟩
  let c : S := ⟨x, hx⟩
  let p := BinaryLottery high low a ha
  have ce : IsCertaintyEquivalent (fun z : S => U z) p c := by
    unfold IsCertaintyEquivalent p
    rw [expectedUtility_binary]
    change U x = a * U 4800 + (1 - a) * U (-1000)
    dsimp [a]
    field_simp [(sub_pos.mpr endpoints).ne']
    ring
  have h := certaintyEquivalent_of_equal_premia (convex_Icc _ _) cont forward backward p ce
  unfold IsCertaintyEquivalent p at h
  rw [expectedUtility_binary] at h
  change U (x + 200) = a * U (4800 + 200) + (1 - a) * U (-1000 + 200) at h
  norm_num at h
  rw [h]
  dsimp [a, q]
  field_simp [(sub_pos.mpr endpoints).ne']
  ring

/-- The affine shift recursion and the reported indifference rank the three offers on the grid. -/
theorem calibrated_grid_ranking (G : ℕ → ℝ) {q b : ℝ} (hq : 0 < q)
    (step : ∀ n < 30, G (n + 1) = q * G n + b) (hi : G 0 < G 1)
    (he : (G 30 + G 5) / 2 = G 17) :
    G 15 < 2/5 * G 30 + 3/10 * G 5 + 3/10 * G 10 ∧
      2/5 * G 30 + 3/10 * G 5 + 3/10 * G 10 < 3/5 * G 30 + 2/5 * G 0 := by
  have hn : q ≠ 1 := by
    rintro rfl
    have lin (n : ℕ) (hn : n ≤ 30) : G n = G 0 + n * b := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [step n (by omega), ih (by omega), Nat.cast_succ]
        ring
    rw [lin 30 (by decide), lin 5 (by decide), lin 17 (by decide)] at he
    rw [lin 1 (by decide)] at hi
    norm_num at hi he
    linarith
  let A := b / (1 - q)
  let D := G 0 - A
  have fixed : q * A + b = A := by
    dsimp [A]
    field_simp [sub_ne_zero.mpr hn.symm]
    ring
  have grid (n : ℕ) (hn : n ≤ 30) : G n = A + D * q ^ n := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [step n (by omega), ih (by omega), pow_succ]
      linear_combination fixed
  have hD : D ≠ 0 := by
    intro hz
    rw [grid 0 (by decide), grid 1 (by decide), hz] at hi
    simp at hi
  let T := D * q ^ 5
  have hT : T ≠ 0 := mul_ne_zero hD (pow_ne_zero _ hq.ne')
  have above (n : ℕ) (h : n + 5 ≤ 30) : G (n + 5) = A + T * q ^ n := by
    rw [grid _ h, pow_add]
    dsimp [T]
    ring
  have zero : G 5 = A + T := by simpa using above 0 (by decide)
  have low : G 0 = A + T / q ^ 5 := by
    rw [grid 0 (by decide)]
    simp [T, hq.ne']
  rw [above 25 (by decide), zero, above 12 (by decide)] at he
  have product : T * (2 * q ^ 12 - 1 - q ^ 25) = 0 := by linarith
  have equation : 2 * q ^ 12 = 1 + q ^ 25 := by
    have h := (mul_eq_zero.mp product).resolve_left hT
    linarith
  have hlt : q < 1 := by
    by_contra! h
    have hgt := lt_of_le_of_ne h hn.symm
    have strict : q ^ 24 < q ^ 25 := by
      rw [show q ^ 25 = q ^ 24 * q by ring]
      exact lt_mul_of_one_lt_right (pow_pos hq _) hgt
    nlinarith only [sq_nonneg (q ^ 12 - 1), equation, strict]
  have hneg : T < 0 := by
    rw [grid 0 (by decide), grid 1 (by decide)] at hi
    simp only [pow_zero, mul_one, pow_one] at hi
    have negD : D < 0 := by
      by_contra! h
      nlinarith only [hi, mul_nonneg h (sub_nonneg.mpr hlt.le)]
    exact mul_neg_of_neg_of_pos negD (pow_pos hq _)
  obtain ⟨hBC, hCA⟩ := calibrated_disutility_rankings ⟨hq, hlt⟩ equation
  rw [above 10 (by decide), above 25 (by decide), zero, above 5 (by decide), low]
  constructor
  · linarith only [mul_lt_mul_of_neg_left hCA hneg]
  · have h := mul_lt_mul_of_neg_left hBC hneg
    simp only [div_eq_mul_inv] at h ⊢
    linarith only [h]

/-- **Problem 6.2:** constant risk premia and the given certainty equivalent imply B ≻ C ≻ A
for every continuous, strictly increasing monetary prize index on the specified interval. -/
theorem problem_6_2_of_constant_premia {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ContinuousOn U CalibrationInterval) (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  obtain ⟨q, hq, b, hshift⟩ := calibration_shift_affine hi hc hC
  let G (n : ℕ) := U (-1000 + 200 * (n : ℝ))
  have step (n : ℕ) (hn : n < 30) : G (n + 1) = q * G n + b := by
    have hn' : (n : ℝ) ≤ 29 := by exact_mod_cast (show n ≤ 29 by omega)
    have h := hshift (-1000 + 200 * n) ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by linarith⟩
    dsimp [G]
    rw [← h, Nat.cast_add, Nat.cast_one]
    ring_nf
  have inc : G 0 < G 1 := by
    norm_num [G]
    exact hi (by norm_num [CalibrationInterval]) (by norm_num [CalibrationInterval]) (by norm_num)
  have cal : (G 30 + G 5) / 2 = G 17 := by
    norm_num [G]
    exact he
  have ranked := calibrated_grid_ranking G hq step inc cal
  norm_num [G] at ranked
  exact ranked

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk-neutral portfolios, arbitrage and uniqueness

Kreps I, Proposition 6.18(d–f), pp. 144–145. The return distribution may have
any finite support. An actually positive-probability strict gain gives a strict
expected improvement. Strict utility concavity at one state with a nonzero
excess return gives strict concavity of the full portfolio objective.
-/

namespace Kreps.UtilityForMoney

/-- Linear monetary utility evaluates a portfolio at its mean net return. -/
theorem portfolioValue_affine (p : SimpleLottery ℝ) (r w a A B : ℝ) :
    PortfolioValue (fun x => A * x + B) p r w a =
      A * (a * (ExpectedUtility id p - r) + r * w) + B := by
  rw [PortfolioValue, expectedUtility_affine_payoff, expected_portfolioWealth]

/-- **Proposition 6.18(d):** with linear utility all three possible solution sets are explicit. -/
theorem proposition_6_18d (p : SimpleLottery ℝ) (r w A B : ℝ) (hA : 0 < A) :
    (r < ExpectedUtility id p → PortfolioOptima (fun x => A * x + B) p r w = ∅) ∧
      (r = ExpectedUtility id p → PortfolioOptima (fun x => A * x + B) p r w = Set.Ici 0) ∧
      (ExpectedUtility id p < r → PortfolioOptima (fun x => A * x + B) p r w = {0}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha.2 (a + 1) (by linarith [ha.1])
    rw [portfolioValue_affine, portfolioValue_affine] at h
    nlinarith [mul_pos hA (sub_pos.mpr he)]
  · rintro rfl
    ext a
    exact ⟨And.left, fun ha => ⟨ha, fun b _ => by simp [portfolioValue_affine]⟩⟩
  · intro he
    apply proposition_6_18a _ _ w he
    · refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b _ _ hab
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t * B) hab]
    · exact fun _ _ h => add_lt_add_left (mul_lt_mul_of_pos_left h hA) _

/-- A weak improvement everywhere, strict on the support in one state, improves expected utility. -/
theorem expectedUtility_lt_of_support {X : Type*} (p : SimpleLottery X) {f g : X → ℝ}
    (hle : ∀ x ∈ p.weights.support, f x ≤ g x)
    (hlt : ∃ x ∈ p.weights.support, f x < g x) : ExpectedUtility f p < ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum
  · intro x hx
    exact mul_le_mul_of_nonneg_left (hle x hx) (p.nonneg x)
  · obtain ⟨x, hx, h⟩ := hlt
    exact ⟨x, hx, mul_lt_mul_of_pos_left h
      (lt_of_le_of_ne (p.nonneg x) (Ne.symm (Finsupp.mem_support_iff.mp hx)))⟩

/-- **Proposition 6.18(e):** an arbitrage strictly improves every finite risky position. -/
theorem proposition_6_18e {V : ℝ → ℝ} (hi : StrictMono V) (p : SimpleLottery ℝ) (r w : ℝ)
    (hle : ∀ t ∈ p.weights.support, r ≤ t) (hlt : ∃ t ∈ p.weights.support, r < t) :
    PortfolioOptima V p r w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  refine (not_lt_of_ge (ha.2 (a + 1) (by linarith [ha.1]))) ?_
  apply expectedUtility_lt_of_support p
  · intro t ht
    apply hi.monotone
    unfold PortfolioWealth
    nlinarith [hle t ht]
  · obtain ⟨t, ht, h⟩ := hlt
    refine ⟨t, ht, hi ?_⟩
    unfold PortfolioWealth
    nlinarith

/-- Expected utility is linear in a fixed weighted sum of state-dependent payoffs. -/
theorem expectedUtility_linear_combination {X : Type*} (p : SimpleLottery X) (f g : X → ℝ)
    (a b : ℝ) :
    ExpectedUtility (fun x => a * f x + b * g x) p =
      a * ExpectedUtility f p + b * ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Nonconstant portfolio returns preserve strict concavity of the objective in the investment. -/
theorem portfolioValue_strictConcave {V : ℝ → ℝ} (hc : StrictConcaveOn ℝ Set.univ V)
    (p : SimpleLottery ℝ) (r w : ℝ) (hn : ∃ t ∈ p.weights.support, t ≠ r) :
    StrictConcaveOn ℝ (Set.Ici 0) (PortfolioValue V p r w) := by
  refine ⟨convex_Ici _, ?_⟩
  intro a _ b _ hab c d hc' hd hsum
  simp only [smul_eq_mul]
  rw [PortfolioValue, PortfolioValue, PortfolioValue, ← expectedUtility_linear_combination]
  have he (t : ℝ) : PortfolioWealth r w (c * a + d * b) t =
      c * PortfolioWealth r w a t + d * PortfolioWealth r w b t := by
    unfold PortfolioWealth
    linear_combination -(r * w) * hsum
  apply expectedUtility_lt_of_support
  · intro t _
    rw [he]
    exact hc.concaveOn.2 (Set.mem_univ _) (Set.mem_univ _) hc'.le hd.le hsum
  · obtain ⟨t, ht, htr⟩ := hn
    refine ⟨t, ht, ?_⟩
    rw [he]
    apply hc.2 (Set.mem_univ _) (Set.mem_univ _) _ hc' hd hsum
    intro h
    apply hab
    apply (mul_right_cancel₀ (sub_ne_zero.mpr htr))
    exact add_right_cancel h

/-- **Proposition 6.18(f):** strict risk aversion and two distinct returns give uniqueness
whenever the objective attains its maximum. -/
theorem proposition_6_18f {V : ℝ → ℝ} (hd : Differentiable ℝ V)
    (hanti : StrictAnti (deriv V)) (p : SimpleLottery ℝ) (r w : ℝ)
    (hn : ∃ t ∈ p.weights.support, ∃ u ∈ p.weights.support, t ≠ u) :
    (PortfolioOptima V p r w).Subsingleton := by
  obtain ⟨t, ht, u, hu, htu⟩ := hn
  have hne : ∃ v ∈ p.weights.support, v ≠ r := by
    by_cases htr : t = r
    · exact ⟨u, hu, fun hur => htu (htr.trans hur.symm)⟩
    · exact ⟨t, ht, htr⟩
  have hc := portfolioValue_strictConcave (hanti.strictConcaveOn_univ_of_deriv hd.continuous)
    p r w hne
  intro a ha b hb
  exact hc.eq_of_isMaxOn ha.2 hb.2 ha.1 hb.1

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Investment under constant absolute risk aversion

Kreps I, Problem 6.11, p. 145. The wealth term factors out of exponential
expected utility and the risk-aversion parameter rescales the risky position.
A loss return with positive probability bounds the optimizer in a compact
interval even though borrowing at the safe rate is permitted.
-/

namespace Kreps.UtilityForMoney

/-- The normalized portfolio value is minus the expected exponential loss. -/
theorem cara_unit_value (p : SimpleLottery ℝ) (r a : ℝ) :
    PortfolioValue (ExponentialUtility 1) p r 0 a =
      -∑ t ∈ p.weights.support, p.weights t * Real.exp (a * (r - t)) := by
  unfold PortfolioValue ExpectedUtility Finsupp.sum ExponentialUtility PortfolioWealth
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [show -1 * (a * (t - r) + r * 0) = a * (r - t) by ring, mul_neg]

/-- Exponential expected utility factors into a positive wealth term and a scaled-risk value. -/
theorem cara_portfolio_factor (p : SimpleLottery ℝ) (r w k a : ℝ) :
    PortfolioValue (ExponentialUtility k) p r w a =
      Real.exp (-k * (r * w)) * PortfolioValue (ExponentialUtility 1) p r 0 (k * a) := by
  rw [cara_unit_value]
  unfold PortfolioValue ExpectedUtility Finsupp.sum ExponentialUtility PortfolioWealth
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [show -k * (a * (t - r) + r * w) = -k * (r * w) + k * a * (r - t) by ring, Real.exp_add]
  ring

/-- Strictly positive loss probability makes the normalized problem attain a finite maximum. -/
theorem cara_unit_attains (p : SimpleLottery ℝ) (r : ℝ)
    (hbad : ∃ t ∈ p.weights.support, t < r) :
    (PortfolioOptima (ExponentialUtility 1) p r 0).Nonempty := by
  obtain ⟨t, ht, htr⟩ := hbad
  have hp : 0 < p.weights t :=
    lt_of_le_of_ne (p.nonneg t) (Ne.symm (Finsupp.mem_support_iff.mp ht))
  let A := 1 / (p.weights t * (r - t))
  have hA : 0 < A := div_pos zero_lt_one (mul_pos hp (sub_pos.mpr htr))
  let F := PortfolioValue (ExponentialUtility 1) p r 0
  have hc : Continuous F := by
    unfold F
    simp_rw [funext (cara_unit_value p r)]
    fun_prop
  obtain ⟨a, ha, haopt⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hA.le) hc.continuousOn
  refine ⟨a, ha.1, fun b hb => ?_⟩
  by_cases hle : b ≤ A
  · exact haopt ⟨hb, hle⟩
  · have hbig : 1 < b * (p.weights t * (r - t)) :=
      (div_lt_iff₀ (mul_pos hp (sub_pos.mpr htr))).mp (lt_of_not_ge hle)
    have hl := Finset.single_le_sum (fun i (_ : i ∈ p.weights.support) =>
      mul_nonneg (p.nonneg i) (Real.exp_pos (b * (r - i))).le) ht
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b * (r - t))) hp.le
    have hf : F b < F 0 := by
      rw [show F b = _ from cara_unit_value p r b, show F 0 = _ from portfolioValue_zero _ _ _ _]
      simp only [ExponentialUtility, mul_zero, Real.exp_zero]
      linarith only [hl, he, hp, hbig]
    exact hf.le.trans (haopt (show (0 : ℝ) ∈ Set.Icc 0 A from ⟨le_rfl, hA.le⟩))

/-- The optimum set at any wealth and positive risk coefficient rescales the unit optimum. -/
theorem cara_optima_scale (p : SimpleLottery ℝ) (r w : ℝ) {k : ℝ} (hk : 0 < k) (a : ℝ) :
    a ∈ PortfolioOptima (ExponentialUtility k) p r w ↔
      k * a ∈ PortfolioOptima (ExponentialUtility 1) p r 0 := by
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨mul_nonneg hk.le ha, fun b hb => ?_⟩
    have h := hm (b / k) (div_nonneg hb hk.le)
    rw [cara_portfolio_factor p r w k (b / k), cara_portfolio_factor p r w k a,
      mul_comm k (b / k),
      div_mul_cancel₀ _ hk.ne', mul_le_mul_iff_right₀ (Real.exp_pos _)] at h
    exact h
  · rintro ⟨ha, hm⟩
    refine ⟨(mul_nonneg_iff_of_pos_left hk).mp ha, fun b hb => ?_⟩
    rw [cara_portfolio_factor p r w k b, cara_portfolio_factor p r w k a]
    exact mul_le_mul_of_nonneg_left (hm (k * b) (mul_nonneg hk.le hb)) (Real.exp_pos _).le

/-- **Problem 6.11(a–c):** the optimum equals a constant divided by the risk coefficient. -/
theorem problem_6_11 (p : SimpleLottery ℝ) {r : ℝ} (hmean : r < ExpectedUtility id p)
    (hbad : ∃ t ∈ p.weights.support, t < r) :
    ∃ A > 0, ∀ w k : ℝ, 0 < k → PortfolioOptima (ExponentialUtility k) p r w = {A / k} := by
  obtain ⟨A, hA⟩ := cara_unit_attains p r hbad
  have hsp := portfolioValue_strictConcave (exponentialUtility_strictConcave zero_lt_one) p r 0
    (hbad.imp fun t ⟨ht, hlt⟩ => ⟨ht, hlt.ne⟩)
  have hApos : 0 < A := proposition_6_18c
    (exponentialUtility_strictConcave zero_lt_one).concaveOn
    (exponentialUtility_strictMono zero_lt_one)
    (exponentialUtility_hasDerivAt 1 _).differentiableAt hmean hA
  refine ⟨A, hApos, fun w k hk => ?_⟩
  ext a
  rw [Set.mem_singleton_iff, cara_optima_scale p r w hk]
  constructor
  · intro ha
    have he := hsp.eq_of_isMaxOn ha.2 hA.2 ha.1 hA.1
    exact (eq_div_iff hk.ne').mpr ((mul_comm _ _).trans he)
  · rintro rfl
    rwa [mul_comm k, div_mul_cancel₀ _ hk.ne']

/-- The inverse risk-aversion formula decreases as the coefficient increases. -/
theorem cara_position_antitone {A : ℝ} (hA : 0 ≤ A) {k l : ℝ} (hk : 0 < k) (hkl : k ≤ l) :
    A / l ≤ A / k := div_le_div_of_nonneg_left hA hk hkl

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Joint laws of two finite monetary lotteries

Kreps I, Proposition 6.15 and Problem 6.6, pp. 133–134 and 141–142.
A joint law assigns nonnegative probabilities to pairs of support points.
Rows and columns recover the prescribed marginal laws. Each row has positive
mass, so its conditional expected supplement is well-defined.
-/

namespace Kreps.UtilityForMoney

open Convexity

/-- The probabilities at the actual support points sum to one. -/
theorem support_mass_sum {X : Type*} (p : SimpleLottery X) :
    ∑ i : p.weights.support, p.weights i.val = 1 := by
  rw [Finset.sum_coe_sort p.weights.support (fun x => p.weights x)]
  exact p.total

/-- Each simple lottery has at least one actual support point. -/
theorem lottery_support_nonempty {X : Type*} (p : SimpleLottery X) :
    Nonempty ↥p.weights.support := by
  have h := support_mass_sum p
  by_contra! he
  simp at h

/-- A finite coupling is a joint probability table with the given row and column marginals. -/
structure FiniteCoupling (p q : SimpleLottery ℝ) where
  /-- Joint mass of the specified support pair. -/
  mass : p.weights.support → q.weights.support → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ mass i j
  /-- Summing over columns recovers the first marginal. -/
  row_sum : ∀ i, ∑ j, mass i j = p.weights i.val
  /-- Summing over rows recovers the second marginal. -/
  col_sum : ∀ j, ∑ i, mass i j = q.weights j.val

/-- The second outcome's conditional increment has nonpositive mass-weighted mean in every row. -/
def FiniteCoupling.NonpositiveDrift {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) : Prop :=
  ∀ i, ∑ j : q.weights.support, C.mass i j * (j.val - i.val) ≤ 0

/-- Normalizing the row gives its conditional expected supplement. -/
noncomputable def FiniteCoupling.conditionalDrift {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (i : p.weights.support) : ℝ :=
  ∑ j : q.weights.support, (C.mass i j / p.weights i.val) * (j.val - i.val)

/-- The sign of the conditional mean agrees with that of the unnormalized drift. -/
theorem FiniteCoupling.nonpositiveDrift_iff {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) :
    C.NonpositiveDrift ↔ ∀ i, C.conditionalDrift i ≤ 0 := by
  have hp (i : p.weights.support) : 0 < p.weights i.val :=
    lt_of_le_of_ne (p.nonneg i.val) (Ne.symm (Finsupp.mem_support_iff.mp i.property))
  have he (i : p.weights.support) : C.conditionalDrift i =
      (∑ j : q.weights.support, C.mass i j * (j.val - i.val)) / p.weights i.val := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [NonpositiveDrift, he, div_le_iff₀ (hp _), zero_mul]

/-- The joint lottery on support pairs gives both random variables on a common sample space. -/
noncomputable def FiniteCoupling.jointLaw {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) :
    SimpleLottery (↥p.weights.support × ↥q.weights.support) where
  weights := Finsupp.equivFunOnFinite.symm (fun ij => C.mass ij.1 ij.2)
  nonneg := fun ij => C.nonneg ij.1 ij.2
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 = 1
    rw [Fintype.sum_prod_type]
    simpa only [C.row_sum] using support_mass_sum p

/-- The first projection gives the prescribed marginal expectation. -/
theorem FiniteCoupling.first_marginal {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (U : ℝ → ℝ) : ExpectedUtility (fun ij => U ij.1.val) C.jointLaw = ExpectedUtility U p := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 * U ij.1.val = _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, C.row_sum, Finset.sum_coe_sort p.weights.support
    (fun x => p.weights x * U x), Finsupp.sum]

/-- Integrating a function of the second projection gives its second marginal expectation. -/
theorem FiniteCoupling.second_marginal {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (U : ℝ → ℝ) : ExpectedUtility (fun ij => U ij.2.val) C.jointLaw = ExpectedUtility U q := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change ∑ ij : ↥p.weights.support × ↥q.weights.support, C.mass ij.1 ij.2 * U ij.2.val = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, C.col_sum, Finset.sum_coe_sort q.weights.support
    (fun x => q.weights x * U x), Finsupp.sum]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite separation for marginal laws and conditional means

Kreps I, Proposition 6.15(b), pp. 133–134. Each pair of prizes contributes
its marginal indicators and the supplement in its row. Separating the compact
convex set of attainable moments from prescribed marginals and nonpositive
drifts produces a finite dual certificate.
-/

namespace Kreps.UtilityForMoney

open Convexity Set

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Two marginal vectors and one vector of conditional numerator moments. -/
abbrev CouplingMoments (I J : Type*) := (I → ℝ) × (J → ℝ) × (I → ℝ)

/-- Unit contribution to a row marginal. -/
def RowDirection (i : I) : CouplingMoments I J := (Pi.single i 1, 0, 0)

/-- Unit contribution to a column marginal. -/
def ColumnDirection (j : J) : CouplingMoments I J := (0, Pi.single j 1, 0)

/-- Unit contribution to a row's weighted drift. -/
def DriftDirection (i : I) : CouplingMoments I J := (0, 0, Pi.single i 1)

/-- Moment vector of the pure outcome pair. -/
def PairMoments (x : I → ℝ) (y : J → ℝ) (ij : I × J) : CouplingMoments I J :=
  RowDirection ij.1 + ColumnDirection ij.2 + (y ij.2 - x ij.1) • DriftDirection ij.1

/-- Projection commutes with the finite sum of vector pairs. -/
theorem momentSum_fst {T A B : Type*} [Fintype T] [AddCommMonoid A] [AddCommMonoid B]
    (f : T → A × B) : (∑ t, f t).1 = ∑ t, (f t).1 := map_sum (AddMonoidHom.fst A B) _ _

/-- The second projection also commutes with the finite sum of vector pairs. -/
theorem momentSum_snd {T A B : Type*} [Fintype T] [AddCommMonoid A] [AddCommMonoid B]
    (f : T → A × B) : (∑ t, f t).2 = ∑ t, (f t).2 := map_sum (AddMonoidHom.snd A B) _ _

/-- The moment map on joint probability tables gives their two marginals and rowwise drifts. -/
theorem pairMoments_evaluate (x : I → ℝ) (y : J → ℝ) (w : SimpleLottery (I × J)) :
    StdSimplex.affineMapMk (R := ℝ) (PairMoments x y) w =
      (fun i => ∑ j, w.weights (i, j), fun j => ∑ i, w.weights (i, j),
        fun i => ∑ j, w.weights (i, j) * (y j - x i)) := by
  rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
  apply Prod.ext
  · funext i
    simp [Fintype.sum_prod_type, PairMoments, RowDirection, ColumnDirection, DriftDirection,
      momentSum_fst, Pi.single_apply, Finset.sum_apply, Finset.sum_ite_irrel, mul_ite]
  · apply Prod.ext
    · funext j
      simp [Fintype.sum_prod_type, PairMoments, RowDirection, ColumnDirection, DriftDirection,
        momentSum_fst, momentSum_snd, Pi.single_apply, Finset.sum_apply, mul_ite]
    · funext i
      simp [Fintype.sum_prod_type, PairMoments, RowDirection, ColumnDirection, DriftDirection,
        momentSum_snd, Pi.single_apply, Finset.sum_apply, Finset.sum_ite_irrel, mul_ite]

/-- A linear functional's value at prescribed marginals is the sum of its coordinate prices. -/
theorem marginal_functional (p : I → ℝ) (q : J → ℝ) (F : StrongDual ℝ (CouplingMoments I J)) :
    F (p, q, 0) = (∑ i, p i * F (RowDirection i)) + ∑ j, q j * F (ColumnDirection j) := by
  have he : (p, q, (0 : I → ℝ)) =
      (∑ i, p i • (RowDirection i : CouplingMoments I J)) +
        ∑ j, q j • (ColumnDirection j : CouplingMoments I J) := by
    ext i <;> simp [RowDirection, ColumnDirection, momentSum_fst, momentSum_snd,
      Finset.sum_apply, Pi.single_apply, mul_ite]
  rw [he, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

omit [DecidableEq I] [DecidableEq J] in
/-- Finite separation gives a joint law or affine row majorants separating the marginals. -/
theorem coupling_or_separation (p : I → ℝ) (q : J → ℝ) (x : I → ℝ) (y : J → ℝ) :
    (∃ w : SimpleLottery (I × J), (∀ i, ∑ j, w.weights (i, j) = p i) ∧
      (∀ j, ∑ i, w.weights (i, j) = q j) ∧
      ∀ i, ∑ j, w.weights (i, j) * (y j - x i) ≤ 0) ∨
      ∃ a : I → ℝ, ∃ b : J → ℝ, ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ i j,
        (∑ t, p t * a t) + ∑ t, q t * b t < a i + b j + c i * (y j - x i) := by
  classical
  let M := StdSimplex.affineMapMk (R := ℝ) (PairMoments x y)
  let K := Set.range M
  let D : Set (CouplingMoments I J) := {p} ×ˢ ({q} ×ˢ Set.Iic 0)
  have hK : Convex ℝ K := M.convex_range
  have hKc : IsCompact K := isCompact_range (by dsimp [M]; fun_prop)
  have hD : Convex ℝ D := (convex_singleton p).prod ((convex_singleton q).prod (convex_Iic _))
  have hDc : IsClosed D := isClosed_singleton.prod (isClosed_singleton.prod isClosed_Iic)
  by_cases hd : Disjoint D K
  · right
    obtain ⟨F, l, h, hl, hlh, hh⟩ := geometric_hahn_banach_closed_compact hD hDc hK hKc hd
    have hbase : (p, q, (0 : I → ℝ)) ∈ D := ⟨rfl, rfl, fun _ => le_rfl⟩
    have hfl := hl _ hbase
    refine ⟨fun i => F (RowDirection i), fun j => F (ColumnDirection j),
      fun i => F (DriftDirection i), fun i => ?_, fun i j => ?_⟩
    · by_contra! hn
      let t := (l - F (p, q, 0)) / -F (DriftDirection i)
      have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hfl.le) (by linarith)
      have hfe : t * -F (DriftDirection i) = l - F (p, q, 0) :=
        div_mul_cancel₀ _ (neg_ne_zero.mpr hn.ne)
      have hm : (p, q, (0 : I → ℝ)) - t • DriftDirection i ∈ D := by
        refine ⟨by simp [DriftDirection], by simp [DriftDirection], ?_⟩
        intro j
        by_cases hj : j = i <;> simp [DriftDirection, hj, ht]
      have hv := hl _ hm
      rw [map_sub, map_smul, smul_eq_mul] at hv
      linarith
    · have hm : PairMoments x y (i, j) ∈ K :=
        ⟨StdSimplex.single (i, j), StdSimplex.affineMapMk_single _ _⟩
      have hi := hh _ hm
      rw [PairMoments, map_add, map_add, map_smul, smul_eq_mul] at hi
      rw [← marginal_functional p q F]
      linarith
  · left
    obtain ⟨z, hz, w, hw⟩ := Set.not_disjoint_iff.mp hd
    change StdSimplex.affineMapMk (R := ℝ) (PairMoments x y) w = z at hw
    rw [pairMoments_evaluate] at hw
    rw [← hw] at hz
    exact ⟨w, fun i => congrFun hz.1 i, fun j => congrFun hz.2.1 j, hz.2.2⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local copy of Chapter 4 at commit f9c357ada1d9965dabd9eec694720ba585faf575.
# Finite minima for Afriat's utility construction

Kreps I, p. 73 and Problem 4.2, p. 78. A nonempty finite minimum preserves
continuity, strict increase and concavity. The domain and its order or vector
structure are arbitrary; the next module applies these facts to affine functions
on commodity space. Nonemptiness prevents an artificial value for an empty minimum.
-/

namespace Kreps.UtilityForMoney.DominanceTools

variable {I X : Type*} [Fintype I] [Nonempty I]

/-- The pointwise minimum over a nonempty finite family of real-valued functions. -/
noncomputable def FiniteMinimum (f : I → X → ℝ) (x : X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => f i x)

/-- The finite minimum is no greater than any member of the family. -/
theorem finiteMinimum_le (f : I → X → ℝ) (x : X) (i : I) :
    FiniteMinimum f x ≤ f i x :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- A common lower bound bounds the finite minimum from below. -/
theorem le_finiteMinimum (f : I → X → ℝ) (x : X) {a : ℝ}
    (ha : ∀ i, a ≤ f i x) : a ≤ FiniteMinimum f x :=
  Finset.le_inf' _ _ (fun i _ => ha i)

/-- At each point some family member attains the finite minimum. -/
theorem finiteMinimum_attained (f : I → X → ℝ) (x : X) :
    ∃ i, FiniteMinimum f x = f i x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => f i x)
  exact ⟨i, hi⟩

/-- **Problem 4.2:** a finite minimum of continuous functions is continuous. -/
theorem finiteMinimum_continuous [TopologicalSpace X] {f : I → X → ℝ}
    (hf : ∀ i, Continuous (f i)) : Continuous (FiniteMinimum f) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => hf i)

/-- **Problem 4.2:** a finite minimum of strictly increasing functions is strictly increasing. -/
theorem finiteMinimum_strictMono [Preorder X] {f : I → X → ℝ}
    (hf : ∀ i, StrictMono (f i)) : StrictMono (FiniteMinimum f) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := finiteMinimum_attained f y
  rw [hi]
  exact (finiteMinimum_le f x i).trans_lt (hf i hxy)

/-- **Problem 4.2:** a finite minimum of concave functions is concave on their common domain. -/
theorem finiteMinimum_concaveOn [AddCommMonoid X] [Module ℝ X] {S : Set X}
    {f : I → X → ℝ} (hf : ∀ i, ConcaveOn ℝ S (f i)) :
    ConcaveOn ℝ S (FiniteMinimum f) := by
  refine ⟨(hf (Classical.arbitrary I)).1, ?_⟩
  intro x hx y hy a b ha hb hab
  apply le_finiteMinimum
  intro i
  calc
    a • FiniteMinimum f x + b • FiniteMinimum f y
        ≤ a • f i x + b • f i y :=
      add_le_add (smul_le_smul_of_nonneg_left (finiteMinimum_le f x i) ha)
        (smul_le_smul_of_nonneg_left (finiteMinimum_le f y i) hb)
    _ ≤ f i (a • x + b • y) := (hf i).2 hx hy ha hb hab

end Kreps.UtilityForMoney.DominanceTools

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Stochastic dominance for finite-support monetary distributions

Kreps I, Definition 6.13, pp. 132–134. Both orders test all the specified utility
functions on the real line. The lower-tail shortfall at a threshold will equal
the integral of the cumulative distribution function below that threshold.
-/

namespace Kreps.UtilityForMoney

/-- **Definition 6.13:** every nondecreasing prize utility weakly prefers the first lottery. -/
def FirstOrderDominates (p q : SimpleLottery ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ExpectedUtility U q ≤ ExpectedUtility U p

/-- **Definition 6.13:** every nondecreasing concave utility weakly prefers the first lottery. -/
def SecondOrderDominates (p q : SimpleLottery ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ Set.univ U → ExpectedUtility U q ≤ ExpectedUtility U p

/-- The cumulative probability at or below the threshold, including a possible atom there. -/
noncomputable def Cumulative (p : SimpleLottery ℝ) (r : ℝ) : ℝ :=
  ExpectedUtility (fun x => if x ≤ r then 1 else 0) p

/-- Expected shortfall below a fixed threshold. -/
noncomputable def ExpectedShortfall (p : SimpleLottery ℝ) (r : ℝ) : ℝ :=
  ExpectedUtility (fun x => max (r - x) 0) p

/-- First-order dominance entails second-order dominance. -/
theorem FirstOrderDominates.secondOrder {p q : SimpleLottery ℝ} (h : FirstOrderDominates p q) :
    SecondOrderDominates p q := fun U hi _ => h U hi

/-- **Problem 6.5(a):** first-order dominance orders the cumulative probabilities. -/
theorem cumulative_le_of_firstOrder {p q : SimpleLottery ℝ} (h : FirstOrderDominates p q)
    (r : ℝ) : Cumulative p r ≤ Cumulative q r := by
  let f : ℝ → ℝ := fun x => if x ≤ r then 1 else 0
  have hf : Monotone (fun x => (-1 : ℝ) * f x + 1) := by
    intro x y hxy
    dsimp [f]
    split_ifs <;> linarith
  have he := h _ hf
  rw [expectedUtility_affine_payoff, expectedUtility_affine_payoff] at he
  change ExpectedUtility f p ≤ ExpectedUtility f q
  linarith

/-- The capped utility used to probe second-order dominance is increasing and concave. -/
theorem cappedPrizeUtility_properties (r : ℝ) :
    Monotone (fun x : ℝ => min x r) ∧ ConcaveOn ℝ Set.univ (fun x : ℝ => min x r) := by
  refine ⟨fun _ _ h => min_le_min_right r h, convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left x r) ha)
      (mul_le_mul_of_nonneg_left (min_le_left y r) hb)
  · have h₁ := mul_le_mul_of_nonneg_left (min_le_right x r) ha
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right y r) hb
    nlinarith [congrArg (fun t : ℝ => t * r) hab]

/-- **Problem 6.6(a), shortfall form:** risk-averse dominance reduces each expected shortfall. -/
theorem expectedShortfall_le_of_secondOrder {p q : SimpleLottery ℝ}
    (h : SecondOrderDominates p q) (r : ℝ) : ExpectedShortfall p r ≤ ExpectedShortfall q r := by
  have he := h _ (cappedPrizeUtility_properties r).1 (cappedPrizeUtility_properties r).2
  have heq : (fun x : ℝ => min x r) = fun x => (-1 : ℝ) * max (r - x) 0 + r := by
    funext x
    rcases le_total x r with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
      ring
  rw [heq, expectedUtility_affine_payoff, expectedUtility_affine_payoff] at he
  unfold ExpectedShortfall
  linarith

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Constructing a supermartingale coupling from second-order dominance

Kreps I, Proposition 6.15(b), pp. 133–134. If the marginal and conditional-mean
constraints had no solution, finite separation would give a dual certificate.
The minimum of its affine rows is an increasing concave prize utility strictly
favoring the second lottery, contrary to dominance. The resulting joint law
allows arbitrary finite supports and arbitrary real probabilities.
-/

namespace Kreps.UtilityForMoney

open DominanceTools

/-- The lower envelope of affine rows with nonnegative slopes is nondecreasing and concave. -/
theorem increasing_concave_envelope {I : Type*} [Fintype I] [Nonempty I]
    (x a c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    let U := FiniteMinimum (fun i z => a i + c i * (z - x i))
    Monotone U ∧ ConcaveOn ℝ Set.univ U := by
  constructor
  · intro s t hst
    obtain ⟨i, hi⟩ := finiteMinimum_attained (fun i z => a i + c i * (z - x i)) t
    apply (finiteMinimum_le _ s i).trans
    change _ ≤ FiniteMinimum _ t
    rw [hi]
    gcongr
    exact hc i
  · apply finiteMinimum_concaveOn
    intro i
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ l h _ _ hs
    simp only [smul_eq_mul]
    apply le_of_eq
    calc
      _ = (l + h) * a i + c i * ((l * s + h * t) - (l + h) * x i) := by ring
      _ = _ := by rw [hs]; ring

/-- Summing over support subtypes gives the book's expected utility without any zero-mass rows. -/
theorem sum_support_utility (p : SimpleLottery ℝ) (U : ℝ → ℝ) :
    ∑ i : p.weights.support, p.weights i.val * U i.val = ExpectedUtility U p := by
  exact Finset.sum_coe_sort p.weights.support (fun x => p.weights x * U x)

/-- Proposition 6.15(b), existence direction. Every second-order ranking has a joint law
whose second prize has nonpositive expected increment conditional on the first prize. -/
theorem supermartingaleCoupling_of_dominance {p q : SimpleLottery ℝ}
    (hdom : SecondOrderDominates p q) : ∃ C : FiniteCoupling p q, C.NonpositiveDrift := by
  classical
  let I := ↥p.weights.support
  let J := ↥q.weights.support
  let : Nonempty I := lottery_support_nonempty p
  let : Nonempty J := lottery_support_nonempty q
  let wp (i : I) := p.weights i.val
  let wq (j : J) := q.weights j.val
  obtain h | h := coupling_or_separation wp wq (fun i : I => i.val) (fun j : J => j.val)
  · obtain ⟨w, hrow, hcol, hmean⟩ := h
    exact ⟨⟨fun i j => w.weights (i, j), fun i j => w.nonneg (i, j), hrow, hcol⟩, hmean⟩
  · obtain ⟨a, b, c, hc, hsep⟩ := h
    let L (i : I) (z : ℝ) := a i + c i * (z - i.val)
    let U := FiniteMinimum L
    have hreg : Monotone U ∧ ConcaveOn ℝ Set.univ U :=
      increasing_concave_envelope (fun i : I => i.val) a c hc
    let A := ∑ i, wp i * a i
    let B := ∑ j, wq j * b j
    have hcol (j : J) : A + B - b j < U j.val := by
      obtain ⟨i, hi⟩ := finiteMinimum_attained L j.val
      change _ < FiniteMinimum L j.val
      rw [hi]
      have hj : A + B < a i + b j + c i * (j.val - i.val) := hsep i j
      dsimp only [L]
      linarith
    have hrow (i : I) : U i.val ≤ a i := by
      simpa only [L, sub_self, mul_zero, add_zero] using finiteMinimum_le L i.val i
    have hq : (∑ j, wq j * (A + B - b j)) < ∑ j : J, wq j * U j.val := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro j _
      exact mul_lt_mul_of_pos_left (hcol j)
        (lt_of_le_of_ne (q.nonneg j.val) (Ne.symm (Finsupp.mem_support_iff.mp j.property)))
    have hre : ∑ j, wq j * (A + B - b j) = A := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, wq]
      rw [support_mass_sum, one_mul]
      dsimp [B, wq]
      ring
    rw [hre, show ∑ j : J, wq j * U j.val = ExpectedUtility U q from sum_support_utility q U] at hq
    have hp : ExpectedUtility U p ≤ A := by
      rw [← sum_support_utility]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (p.nonneg i.val)
    exact (hq.not_ge ((hdom U hreg.1 hreg.2).trans hp)).elim

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Conditional Jensen inequality for stochastic dominance

Kreps I, Proposition 6.15(b) and Problem 6.6(b), pp. 133, 142. Each positive
row mass normalizes its row to a conditional probability vector. Jensen's
inequality in that row and nonnegative monotonicity give the comparison, which
is then averaged using the two actual marginal laws.
-/

namespace Kreps.UtilityForMoney

/-- A row of nonpositive mean drift cannot increase conditional expected utility. -/
theorem FiniteCoupling.row_utility_le {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (hc : C.NonpositiveDrift) (U : ℝ → ℝ) (hi : Monotone U) (hu : ConcaveOn ℝ Set.univ U)
    (i : p.weights.support) :
    ∑ j : q.weights.support, C.mass i j * U j.val ≤ p.weights i.val * U i.val := by
  classical
  have hpos : 0 < p.weights i.val :=
    lt_of_le_of_ne (p.nonneg _) (Ne.symm (Finsupp.mem_support_iff.mp i.property))
  let w := fun j : q.weights.support => C.mass i j / p.weights i.val
  have hw (j) : 0 ≤ w j := div_nonneg (C.nonneg _ _) hpos.le
  have hsum : ∑ j, w j = 1 := by
    change (∑ j : q.weights.support, C.mass i j / p.weights i.val) = 1
    rw [← Finset.sum_div, C.row_sum, div_self hpos.ne']
  have hmean : ∑ j : q.weights.support, w j * j.val ≤ i.val := by
    have h := (C.nonpositiveDrift_iff.mp hc) i
    unfold FiniteCoupling.conditionalDrift at h
    change ∑ j : q.weights.support, w j * (j.val - i.val) ≤ 0 at h
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul,
      sub_nonpos] using h
  have hj := hu.le_map_sum (t := Finset.univ) (w := w) (p := fun j : q.weights.support => j.val)
    (fun j _ => hw j) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have he := mul_le_mul_of_nonneg_left (hj.trans (hi hmean)) hpos.le
  rw [Finset.mul_sum] at he
  have heq (j : q.weights.support) : p.weights i.val * (w j * U j.val) = C.mass i j * U j.val := by
    dsimp [w]
    field_simp
  simpa only [heq] using he

/-- **Problem 6.6(b):** a nonpositive conditional supplement implies second-order dominance. -/
theorem secondOrder_of_supermartingaleCoupling {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (hc : C.NonpositiveDrift) : SecondOrderDominates p q := by
  intro U hi hu
  rw [← sum_support_utility, ← sum_support_utility]
  calc
    ∑ j : q.weights.support, q.weights j.val * U j.val =
        ∑ j : q.weights.support, ∑ i : p.weights.support, C.mass i j * U j.val := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_mul, C.col_sum]
    _ = ∑ i : p.weights.support, ∑ j : q.weights.support, C.mass i j * U j.val :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ => C.row_utility_le hc U hi hu i

/-- **Proposition 6.15(b):** second-order dominance iff a joint law has nonpositive conditional
supplement in every row of the first marginal. -/
theorem proposition_6_15b (p q : SimpleLottery ℝ) :
    SecondOrderDominates p q ↔ ∃ C : FiniteCoupling p q, C.NonpositiveDrift :=
  ⟨supermartingaleCoupling_of_dominance, fun ⟨C, h⟩ => secondOrder_of_supermartingaleCoupling C h⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.Prerequisites from
f9c357ada1d9965dabd9eec694720ba585faf575.

# Preference and consumption-domain prerequisites

Selected definitions and elementary results copied or adapted from Chapter 2,
commit `7d496c5`: `Basic`, `OrthantRepresentation`, `Monotonicity`,
`ConvexPreference`, and `ConcaveUtility`. Their economic conventions are unchanged.
Only the ingredients used by consumer demand are included in this independent
chapter package. The mathematical source is Kreps I, Chapters 1-2, pp. 1-44.
-/

namespace Kreps.UtilityForMoney.Demand

variable {X : Type*}

/-- Every pair of alternatives can be compared, including an alternative with itself. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- Weak preference is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- The book's standing rationality assumption: complete and transitive preference. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Alternatives at least as good as every feasible alternative. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Preference induced by utility, oriented with the preferred alternative first. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- A utility represents exactly the given weak preference. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Strict preference is weak preference without its reverse. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference is weak preference in both directions. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- Utility-induced preferences satisfy the chapter's rationality assumption. -/
theorem utilityPref_rational (u : X → ℝ) : Rational (UtilityPref u) :=
  ⟨fun x y => le_total (u y) (u x), fun _ _ _ hxy hyz => hyz.trans hxy⟩

/-- The consumption domain includes every boundary bundle and the origin. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- Local insatiability uses the book's closed-ball inequality. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}

/-- A convex combination as a point of its convex consumption domain. -/
def Mix (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- Internal convexity of a feasible menu agrees with closure under mixtures. -/
def ConvexMenu (hS : Convex ℝ S) (A : Set S) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a, ∀ ha : a ∈ Set.Icc 0 1, Mix hS x y a ha ∈ A

/-- Mixtures are weakly better than the worse endpoint. -/
def ConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- Distinct endpoints give strictly better interior mixtures than the worse endpoint. -/
def StrictlyConvexPreference (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- Jensen's concavity inequality, on the actual consumption domain. -/
def ConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1,
    a * u x + (1 - a) * u y ≤ u (Mix hS x y a ha)

/-- The mixture's utility is at least the lesser endpoint utility. -/
def QuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y a, ∀ ha : a ∈ Set.Icc 0 1, min (u x) (u y) ≤ u (Mix hS x y a ha)

/-- Distinct endpoints give a strict utility improvement over the worse one. -/
def StrictlyQuasiConcaveUtility (hS : Convex ℝ S) (u : S → ℝ) : Prop :=
  ∀ x y, x ≠ y → u y ≤ u x → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    u y < u (Mix hS x y a ⟨ha.1.le, ha.2.le⟩)

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.BudgetSets from
f9c357ada1d9965dabd9eec694720ba585faf575.

# Budget sets at positive prices

Kreps I, Section 3.1 and the budget-set arguments in Proposition 3.1, pp. 50-54.
Income is nonnegative and every commodity price is strictly positive. Feasibility
uses weak inequalities, so zero consumption and spending exactly the available
income are included. Nonemptiness, coordinate bounds, closedness and convexity
are established before optimizing any utility.
-/

namespace Kreps.UtilityForMoney.Demand

open scoped NNReal

/-- The strictly positive finite-dimensional price vectors of Section 3.1. -/
abbrev PositivePrices (k : ℕ) := {p : Fin k → ℝ // ∀ j, 0 < p j}

/-- The zero consumption bundle, feasible at every nonnegative income. -/
def ZeroBundle (k : ℕ) : NonnegativeOrthant k := ⟨0, le_rfl⟩

/-- Expenditure at constant unit prices, the finite scalar product `p · x`. -/
def Expenditure {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) : ℝ :=
  ∑ j, p.val j * x.val j

/-- The budget-feasible bundles at a strictly positive price vector and nonnegative income. -/
def BudgetSet {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  {x | Expenditure p x ≤ (y : ℝ)}

/-- The zero bundle costs nothing. -/
theorem expenditure_zero {k : ℕ} (p : PositivePrices k) :
    Expenditure p (ZeroBundle k) = 0 := by simp [Expenditure, ZeroBundle]

/-- Every feasible consumption expenditure is nonnegative. -/
theorem expenditure_nonneg {k : ℕ} (p : PositivePrices k) (x : NonnegativeOrthant k) :
    0 ≤ Expenditure p x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (p.property j).le (x.property j))

/-- Every nonnegative-income budget set is nonempty. -/
theorem budgetSet_nonempty {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    (BudgetSet p y).Nonempty := by
  refine ⟨ZeroBundle k, ?_⟩
  change Expenditure p (ZeroBundle k) ≤ (y : ℝ)
  rw [expenditure_zero]
  exact y.property

/-- Spending on one good cannot exceed the total nonnegative expenditure. -/
theorem commodity_expenditure_le {k : ℕ} (p : PositivePrices k)
    (x : NonnegativeOrthant k) (j : Fin k) : p.val j * x.val j ≤ Expenditure p x :=
  Finset.single_le_sum (fun i _ => mul_nonneg (p.property i).le (x.property i))
    (Finset.mem_univ j)

/-- Each budget-feasible coordinate is bounded by income divided by its price. -/
theorem budgetSet_coordinate_bound {k : ℕ} (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ BudgetSet p y) (j : Fin k) :
    x.val j ≤ (y : ℝ) / p.val j := by
  apply (le_div_iff₀ (p.property j)).mpr
  simpa only [mul_comm] using (commodity_expenditure_le p x j).trans hx

/-- At zero income the zero bundle is the only feasible consumption. -/
theorem budgetSet_zero {k : ℕ} (p : PositivePrices k) :
    BudgetSet p 0 = {ZeroBundle k} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    funext j
    apply le_antisymm
    · change x.val j ≤ 0
      simpa only [NNReal.coe_zero, zero_div] using budgetSet_coordinate_bound p 0 hx j
    · exact x.property j
  · rintro rfl
    change Expenditure p (ZeroBundle k) ≤ 0
    exact (expenditure_zero p).le

/-- Expenditure is continuous in the consumption bundle. -/
theorem expenditure_continuous {k : ℕ} (p : PositivePrices k) : Continuous (Expenditure p) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)

/-- Feasibility is a closed condition inside the nonnegative orthant. -/
theorem budgetSet_isClosed {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsClosed (BudgetSet p y) := isClosed_le (expenditure_continuous p) continuous_const

/-- Positive prices put the closed budget set inside a compact coordinate box. -/
theorem budgetSet_isCompact {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    IsCompact (BudgetSet p y) := by
  let b : Fin k → ℝ := fun j => (y : ℝ) / p.val j
  have hbox : IsCompact ((Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹'
      Set.Icc 0 b) :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  apply hbox.of_isClosed_subset (budgetSet_isClosed p y)
  intro x hx
  exact ⟨x.property, fun j => budgetSet_coordinate_bound p y hx j⟩

/-- Expenditure of a mixture is the corresponding mixture of expenditures. -/
theorem expenditure_mix {k : ℕ} (p : PositivePrices k) (x z : NonnegativeOrthant k)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) =
      a * Expenditure p x + (1 - a) * Expenditure p z := by
  change (∑ j, p.val j * (a * x.val j + (1 - a) * z.val j)) = _
  calc
    _ = ∑ j, (a * (p.val j * x.val j) + (1 - a) * (p.val j * z.val j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- Budget sets are convex, without any assumption on the consumer's utility. -/
theorem budgetSet_convex {k : ℕ} (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (BudgetSet p y) := by
  intro x hx z hz a ha
  have he := expenditure_mix p x z a ha
  change Expenditure p (Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x z a ha) ≤ (y : ℝ)
  rw [he]
  have hx' := mul_le_mul_of_nonneg_left hx ha.1
  have hz' := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ha.2)
  linarith

/-- Multiply every commodity price by the same strictly positive factor. -/
def ScalePrices {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) : PositivePrices k :=
  ⟨fun j => a * p.val j, fun j => mul_pos ha (p.property j)⟩

/-- Scaling all unit prices scales expenditure by the same factor. -/
theorem expenditure_scalePrices {k : ℕ} (a : ℝ) (ha : 0 < a)
    (p : PositivePrices k) (x : NonnegativeOrthant k) :
    Expenditure (ScalePrices a ha p) x = a * Expenditure p x := by
  simp only [Expenditure, ScalePrices, mul_assoc, Finset.mul_sum]

/-- Simultaneous positive scaling of prices and income leaves the entire budget set unchanged. -/
theorem budgetSet_scale {k : ℕ} (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    BudgetSet (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = BudgetSet p y := by
  ext x
  change Expenditure (ScalePrices a ha p) x ≤ a * (y : ℝ) ↔ _
  rw [expenditure_scalePrices, mul_le_mul_iff_right₀ ha]
  rfl

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.CorrespondenceMaximum from
f9c357ada1d9965dabd9eec694720ba585faf575.

# Correspondences and parametric maxima

Kreps I, Appendix 4, pp. 471-477. The book's upper semicontinuity is the
sequential closed-graph condition. It must not be confused with open-set upper
hemicontinuity in the absence of a local compact bound. These general lemmas
provide the existence and limit steps used in the maximum theorem.
-/

namespace Kreps.UtilityForMoney.Demand

open Filter Set
open scoped Topology

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- Definition A4.2a: membership is preserved under simultaneous sequential limits. -/
def SequentialUpper (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (x : ℕ → X) (p₀ : P) (x₀ : X),
    Tendsto p atTop (𝓝 p₀) → Tendsto x atTop (𝓝 x₀) →
    (∀ n, x n ∈ A (p n)) → x₀ ∈ A p₀

/-- Definition A4.2b: every feasible limit point has a feasible companion sequence. -/
def SequentialLower (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (p₀ : P), Tendsto p atTop (𝓝 p₀) →
    ∀ x₀ ∈ A p₀, ∃ x : ℕ → X, (∀ᶠ n in atTop, x n ∈ A (p n)) ∧
      Tendsto x atTop (𝓝 x₀)

/-- The maximizing correspondence for an objective depending on the parameter. -/
def ParametricMaxima (A : P → Set X) (F : P → X → ℝ) (p : P) : Set X :=
  {x | x ∈ A p ∧ ∀ y ∈ A p, F p y ≤ F p x}

omit [TopologicalSpace P] in
/-- Compact, nonempty feasible sets give nonempty maximizing sets. -/
theorem parametricMaxima_nonempty {A : P → Set X} {F : P → X → ℝ} {p : P}
    (hA : IsCompact (A p)) (hne : (A p).Nonempty) (hF : Continuous (F p)) :
    (ParametricMaxima A F p).Nonempty := by
  obtain ⟨x, hx, hm⟩ := hA.exists_isMaxOn hne hF.continuousOn
  exact ⟨x, hx, hm⟩

/-- The closed-graph step of Berge's theorem, using the book's sequential conventions. -/
theorem parametricMaxima_sequentialUpper {A : P → Set X} {F : P → X → ℝ}
    (hA : SequentialUpper A) (hL : SequentialLower A)
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    SequentialUpper (ParametricMaxima A F) := by
  intro p x p₀ x₀ hp hx hm
  refine ⟨hA p x p₀ x₀ hp hx (fun n => (hm n).1), ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hL p p₀ hp y hy
  exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
    (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
    (hz.mono fun n hn => (hm n).2 (z n) hn)

/-- A compact local bound converts the book's upper condition to Mathlib hemicontinuity. -/
theorem sequentialUpper_upperHemicontinuousAt {A : P → Set X} {p₀ : P}
    [(𝓝 p₀).IsCountablyGenerated] (hA : SequentialUpper A)
    {K : Set X} (hK : IsSeqCompact K) (hb : ∀ᶠ p in 𝓝 p₀, A p ⊆ K) :
    UpperHemicontinuousAt A p₀ := by
  apply UpperHemicontinuousAt.of_sequences hK hb
  intro p hp x hx x₀ hlim
  exact hA p x p₀ x₀ hp hlim hx

/-- Continuous feasible selections through each point imply the book's lower condition. -/
theorem sequentialLower_of_continuous_selections {A : P → Set X}
    (h : ∀ p x, x ∈ A p → ∃ s : P → X,
      Continuous s ∧ s p = x ∧ ∀ q, s q ∈ A q) : SequentialLower A := by
  intro p p₀ hp x₀ hx₀
  obtain ⟨s, hs, hsp, hmem⟩ := h p₀ x₀ hx₀
  refine ⟨s ∘ p, Eventually.of_forall (fun n => hmem (p n)), ?_⟩
  simpa only [hsp] using hs.continuousAt.tendsto.comp hp

/-- A local compact container for all nearby feasible sets (Appendix 4). -/
def LocalCompactBound (A : P → Set X) : Prop :=
  ∀ p, ∃ K : Set X, IsCompact K ∧ ∀ᶠ q in 𝓝 p, A q ⊆ K

/-- The supremum value of a parameterized optimization problem. -/
noncomputable def ParametricValue (A : P → Set X) (F : P → X → ℝ) (p : P) : ℝ :=
  sSup (F p '' A p)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- An attained maximum evaluates the supremum without any choice of maximizer. -/
theorem parametricValue_eq_of_maximum {A : P → Set X} {F : P → X → ℝ} {p : P} {x : X}
    (hx : x ∈ ParametricMaxima A F p) : ParametricValue A F p = F p x := by
  apply csSup_eq_of_is_forall_le_of_forall_le_imp_ge
  · exact ⟨F p x, x, hx.1, rfl⟩
  · rintro v ⟨y, hy, rfl⟩
    exact hx.2 y hy
  · intro b hb
    exact hb _ ⟨x, hx.1, rfl⟩

/-- The maximum-value continuity step, with existence separated from the limit argument. -/
theorem parametricValue_continuous [SequentialSpace P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hupper : SequentialUpper (ParametricMaxima A F))
    (hne : ∀ p, (ParametricMaxima A F p).Nonempty)
    (hbound : LocalCompactBound (ParametricMaxima A F))
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    Continuous (ParametricValue A F) := by
  classical
  choose s hs using hne
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hpn := hp.comp hns
  obtain ⟨K, hK, hb⟩ := hbound p₀
  have hev : ∀ᶠ n in atTop, s (p (ns n)) ∈ K := by
    filter_upwards [hpn hb] with n hn
    exact hn (hs _)
  obtain ⟨x, _, ms, hms, hlim⟩ := hK.tendsto_subseq' hev.frequently
  have hpm := hpn.comp hms.tendsto_atTop
  have hx : x ∈ ParametricMaxima A F p₀ :=
    hupper (fun n => p (ns (ms n))) (fun n => s (p (ns (ms n))))
      p₀ x hpm hlim (fun n => hs _)
  refine ⟨ms, ?_⟩
  have ht := hF.continuousAt.tendsto.comp (hpm.prodMk_nhds hlim)
  have heq : (fun n => ParametricValue A F (p (ns (ms n)))) =
      (fun n => F (p (ns (ms n))) (s (p (ns (ms n))))) := by
    funext n
    exact parametricValue_eq_of_maximum (hs _)
  change Tendsto (fun n => ParametricValue A F (p (ns (ms n)))) atTop
    (𝓝 (ParametricValue A F p₀))
  rw [heq, parametricValue_eq_of_maximum hx]
  exact ht

/-- Local compact containment passes to every pointwise smaller correspondence. -/
theorem LocalCompactBound.mono {A B : P → Set X} (h : LocalCompactBound B)
    (hab : ∀ p, A p ⊆ B p) : LocalCompactBound A := by
  intro p
  obtain ⟨K, hK, hb⟩ := h p
  exact ⟨K, hK, hb.mono (fun q hq => (hab q).trans hq)⟩

/-- Closed-graph fibers are closed in first-countable spaces. -/
theorem SequentialUpper.isClosed [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (p : P) : IsClosed (A p) := by
  apply isSeqClosed_iff_isClosed.mp
  intro x x₀ hx ht
  exact h (fun _ => p) x p x₀ tendsto_const_nhds ht hx

/-- The book's closed-graph condition and a local compact bound imply compact values. -/
theorem SequentialUpper.isCompact [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (hb : LocalCompactBound A) (p : P) : IsCompact (A p) := by
  obtain ⟨K, hK, hlocal⟩ := hb p
  exact hK.of_isClosed_subset (h.isClosed p) hlocal.self_of_nhds

/-- Corollary A4.8's singleton step, without needing a utility function. -/
theorem continuous_of_singleton_correspondence [FirstCountableTopology P]
    [FirstCountableTopology X] {s : P → X}
    (hu : SequentialUpper (fun p => {s p}))
    (hb : LocalCompactBound (fun p => {s p})) : Continuous s := by
  apply upperHemicontinuous_singleton_iff.mp
  intro p
  obtain ⟨K, hK, hk⟩ := hb p
  exact sequentialUpper_upperHemicontinuousAt hu hK.isSeqCompact hk

/-- Equality of objective suprema expressed by equality of all real upper bounds.
This avoids assigning a real value to the supremum of an unbounded set. -/
def SameObjectiveUpperBounds (A B : P → Set X) (F : P → X → ℝ) : Prop :=
  ∀ p r, (∀ x ∈ A p, F p x ≤ r) ↔ (∀ x ∈ B p, F p x ≤ r)

/-- Berge's auxiliary-correspondence form: the feasible set itself need not be compact.
The nonempty auxiliary fibers make the convention used in the source proof explicit. -/
theorem maximum_theorem_auxiliary [FirstCountableTopology P] [FirstCountableTopology X]
    {A B : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper B) (hb : LocalCompactBound B)
    (hne : ∀ p, (B p).Nonempty) (hba : ∀ p, B p ⊆ A p)
    (hzb : ∀ p, ParametricMaxima A F p ⊆ B p)
    (hsup : SameObjectiveUpperBounds A B F) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) := by
  have hn (p) : (ParametricMaxima A F p).Nonempty := by
    have hc : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
    obtain ⟨x, hx, hmax⟩ := parametricMaxima_nonempty (hu.isCompact hb p) (hne p) hc
    exact ⟨x, hba p hx, (hsup p (F p x)).mpr hmax⟩
  have hz : SequentialUpper (ParametricMaxima A F) := by
    intro p x p₀ x₀ hp hx hm
    have hxB : x₀ ∈ B p₀ := hu p x p₀ x₀ hp hx (fun n => hzb _ (hm n))
    refine ⟨hba _ hxB, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hl p p₀ hp y hy
    exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
      (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
      (hz.mono fun n hn => (hm n).2 (z n) hn)
  have hbound := hb.mono hzb
  exact ⟨hn, hz, hbound, parametricValue_continuous hz hn hbound hF⟩

/-- The compact-feasible-set version used for consumer budgets, including zero income. -/
theorem maximum_theorem [FirstCountableTopology P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper A) (hb : LocalCompactBound A)
    (hne : ∀ p, (A p).Nonempty) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) :=
  maximum_theorem_auxiliary hF hl hu hb hne (fun _ => Subset.rfl)
    (fun _ _ hx => hx.1) (fun _ _ => Iff.rfl)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- For nonempty objectives with finite upper bounds, the auxiliary theorem's upper-bound
formulation is exactly equality of the printed real suprema. -/
theorem sameObjectiveUpperBounds_iff_value_eq {A B : P → Set X} {F : P → X → ℝ}
    (ha : ∀ p, (A p).Nonempty) (hb : ∀ p, (B p).Nonempty)
    (hba : ∀ p, BddAbove (F p '' A p)) (hbb : ∀ p, BddAbove (F p '' B p)) :
    SameObjectiveUpperBounds A B F ↔ ∀ p, ParametricValue A F p = ParametricValue B F p := by
  have hA (p : P) (r : ℝ) : ParametricValue A F p ≤ r ↔ ∀ x ∈ A p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hba p) ((ha p).image (F p))]
    simp
  have hB (p : P) (r : ℝ) : ParametricValue B F p ≤ r ↔ ∀ x ∈ B p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hbb p) ((hb p).image (F p))]
    simp
  constructor
  · intro h p
    apply le_antisymm
    · exact (hA p _).mpr ((h p _).mpr ((hB p _).mp le_rfl))
    · exact (hB p _).mpr ((h p _).mp ((hA p _).mp le_rfl))
  · intro h p r
    rw [← hA, ← hB, h p]

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.BudgetContinuity from
f9c357ada1d9965dabd9eec694720ba585faf575.

# Continuity and local boundedness of the budget correspondence

Kreps I, the proof of Proposition 3.3, pp. 55-56. The graph is closed and nearby
budgets lie in a common compact coordinate box. For lower semicontinuity we use
the printed recovery formula `(y'/y) * (p · x)/(p' · x) * x`, with the zero
bundle handled separately. The formula supplies a continuous feasible selection
through every feasible bundle, including the zero-income case.
-/

namespace Kreps.UtilityForMoney.Demand

open scoped NNReal Topology

/-- The full parameter domain, including zero income but excluding zero prices. -/
abbrev PriceIncome (k : ℕ) := PositivePrices k × ℝ≥0

/-- Scale a nonnegative bundle by a nonnegative scalar. -/
def ScaleBundle {k : ℕ} (a : ℝ≥0) (x : NonnegativeOrthant k) : NonnegativeOrthant k :=
  ⟨fun j => (a : ℝ) * x.val j, fun j => mul_nonneg a.property (x.property j)⟩

/-- Scaling zero consumption leaves it unchanged. -/
theorem scaleBundle_zero {k : ℕ} (a : ℝ≥0) : ScaleBundle a (ZeroBundle k) = ZeroBundle k := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle, ZeroBundle]

/-- Scaling by one leaves the whole bundle unchanged. -/
theorem scaleBundle_one {k : ℕ} (x : NonnegativeOrthant k) : ScaleBundle 1 x = x := by
  apply Subtype.ext
  funext j
  simp [ScaleBundle]

/-- Expenditure scales linearly in consumption. -/
theorem expenditure_scaleBundle {k : ℕ} (p : PositivePrices k) (a : ℝ≥0)
    (x : NonnegativeOrthant k) : Expenditure p (ScaleBundle a x) = a * Expenditure p x := by
  simp only [Expenditure, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every nonzero nonnegative bundle costs strictly more than zero at strictly positive prices. -/
theorem expenditure_pos {k : ℕ} (p : PositivePrices k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : 0 < Expenditure p x := by
  have hn : Expenditure p x ≠ 0 := by
    intro he
    apply hx
    apply Subtype.ext
    funext j
    have h := commodity_expenditure_le p x j
    have hp := p.property j
    have hxj : 0 ≤ x.val j := x.property j
    change x.val j = 0
    rw [he] at h
    nlinarith
  exact lt_of_le_of_ne (expenditure_nonneg p x) hn.symm

/-- For a fixed bundle, expenditure varies continuously with the price vector. -/
theorem expenditure_price_continuous {k : ℕ} (x : NonnegativeOrthant k) :
    Continuous (fun p : PositivePrices k => Expenditure p x) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- Joint continuity in prices and consumption gives closed budget graphs. -/
theorem expenditure_joint_continuous {k : ℕ} :
    Continuous (fun z : PositivePrices k × NonnegativeOrthant k => Expenditure z.1 z.2) := by
  unfold Expenditure
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))

/-- The exact nonnegative multiplier in the book's recovery sequence. -/
noncomputable def BudgetAdjustmentFactor {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : ℝ≥0 :=
  ⟨(η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x),
    mul_nonneg (div_nonneg η.2.property θ.2.property)
      (div_nonneg (expenditure_nonneg θ.1 x) (expenditure_nonneg η.1 x))⟩

/-- Adjust the reference bundle to the new prices and income by the printed scaling formula. -/
noncomputable def BudgetAdjustment {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (η : PriceIncome k) : NonnegativeOrthant k :=
  ScaleBundle (BudgetAdjustmentFactor θ x η) x

/-- The recovery multiplier equals one at its positive-income, nonzero reference point. -/
theorem budgetAdjustment_self {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ≠ ZeroBundle k) : BudgetAdjustment θ x θ = x := by
  have hf : BudgetAdjustmentFactor θ x θ = 1 := by
    apply NNReal.coe_injective
    change (θ.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure θ.1 x) = 1
    rw [div_self hy.ne', div_self (expenditure_pos θ.1 hx).ne', one_mul]
  rw [BudgetAdjustment, hf, scaleBundle_one]

/-- Every adjusted bundle remains feasible at its new prices and income. -/
theorem budgetAdjustment_feasible {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hy : 0 < (θ.2 : ℝ)) (hx : x ∈ BudgetSet θ.1 θ.2) (η : PriceIncome k) :
    BudgetAdjustment θ x η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    change Expenditure η.1 (ScaleBundle _ (ZeroBundle k)) ≤ (η.2 : ℝ)
    rw [scaleBundle_zero, expenditure_zero]
    exact η.2.property
  change Expenditure η.1 (ScaleBundle _ x) ≤ (η.2 : ℝ)
  rw [expenditure_scaleBundle]
  change ((η.2 : ℝ) / θ.2 * (Expenditure θ.1 x / Expenditure η.1 x)) *
    Expenditure η.1 x ≤ (η.2 : ℝ)
  rw [mul_assoc, div_mul_cancel₀ _ (expenditure_pos η.1 hx0).ne']
  calc
    _ ≤ ((η.2 : ℝ) / θ.2) * θ.2 :=
      mul_le_mul_of_nonneg_left hx (div_nonneg η.2.property θ.2.property)
    _ = _ := div_mul_cancel₀ _ hy.ne'

/-- The recovery bundle is continuous in the new parameters when the reference is nonzero. -/
theorem budgetAdjustment_continuous {k : ℕ} (θ : PriceIncome k) {x : NonnegativeOrthant k}
    (hx : x ≠ ZeroBundle k) : Continuous (BudgetAdjustment θ x) := by
  have hf : Continuous (fun η : PriceIncome k => (BudgetAdjustmentFactor θ x η : ℝ)) :=
    ((continuous_subtype_val.comp continuous_snd).div_const (θ.2 : ℝ)).mul
      (continuous_const.div ((expenditure_price_continuous x).comp continuous_fst)
        (fun η => (expenditure_pos η.1 hx).ne'))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact hf.mul continuous_const

/-- Every feasible reference bundle admits a global continuous feasible recovery selection. -/
theorem budgetSet_continuous_selection {k : ℕ} (θ : PriceIncome k)
    (x : NonnegativeOrthant k) (hx : x ∈ BudgetSet θ.1 θ.2) :
    ∃ s : PriceIncome k → NonnegativeOrthant k, Continuous s ∧ s θ = x ∧
      ∀ η, s η ∈ BudgetSet η.1 η.2 := by
  by_cases hx0 : x = ZeroBundle k
  · subst x
    exact ⟨fun _ => ZeroBundle k, continuous_const, rfl,
      fun η => by change Expenditure η.1 (ZeroBundle k) ≤ (η.2 : ℝ)
                  rw [expenditure_zero]; exact η.2.property⟩
  have hy : 0 < (θ.2 : ℝ) := (expenditure_pos θ.1 hx0).trans_le hx
  exact ⟨BudgetAdjustment θ x, budgetAdjustment_continuous θ hx0,
    budgetAdjustment_self θ hy hx0, budgetAdjustment_feasible θ hy hx⟩

/-- The budget correspondence is lower semicontinuous, including at zero income. -/
theorem budgetSet_sequentialLower {k : ℕ} :
    SequentialLower (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) :=
  sequentialLower_of_continuous_selections budgetSet_continuous_selection

/-- Limits of feasible bundles are feasible at the limiting prices and income. -/
theorem budgetSet_sequentialUpper {k : ℕ} :
    SequentialUpper (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ x θ₀ x₀ hθ hx hm
  have he := expenditure_joint_continuous.continuousAt.tendsto.comp
    ((continuous_fst.continuousAt.tendsto.comp hθ).prodMk_nhds hx)
  have hy := (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hθ
  exact le_of_tendsto_of_tendsto he hy (Filter.Eventually.of_forall hm)

/-- All nearby budgets fit in one compact coordinate box. -/
theorem budgetSet_localCompactBound {k : ℕ} :
    LocalCompactBound (fun θ : PriceIncome k => BudgetSet θ.1 θ.2) := by
  intro θ
  let b : Fin k → ℝ := fun j => ((θ.2 : ℝ) + 1) / (θ.1.val j / 2)
  let K := (Subtype.val : NonnegativeOrthant k → Fin k → ℝ) ⁻¹' Set.Icc 0 b
  have hK : IsCompact K :=
    (isClosed_Ici (a := (0 : Fin k → ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      isCompact_Icc
  refine ⟨K, hK, ?_⟩
  have hyc : Continuous (fun η : PriceIncome k => (η.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hy : ∀ᶠ η : PriceIncome k in 𝓝 θ, (η.2 : ℝ) < (θ.2 : ℝ) + 1 :=
    (hyc.continuousAt (x := θ)).eventually
      (isOpen_Iio.mem_nhds (show (θ.2 : ℝ) < (θ.2 : ℝ) + 1 by linarith))
  have hp : ∀ᶠ η : PriceIncome k in 𝓝 θ, ∀ j, θ.1.val j / 2 < η.1.val j := by
    apply Filter.eventually_all.mpr
    intro j
    have hjc : Continuous (fun η : PriceIncome k => η.1.val j) :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    have hj : θ.1.val j / 2 < θ.1.val j := by have h := θ.1.property j; linarith
    exact hjc.continuousAt.eventually (isOpen_Ioi.mem_nhds hj)
  filter_upwards [hy, hp] with η hy hp
  intro x hx
  refine ⟨x.property, fun j => ?_⟩
  apply (le_div_iff₀ (by have h := θ.1.property j; positivity)).mpr
  have h₁ := commodity_expenditure_le η.1 x j
  have h₂ := mul_le_mul_of_nonneg_right (hp j).le (x.property j)
  change Expenditure η.1 x ≤ (η.2 : ℝ) at hx
  change x.val j * (θ.1.val j / 2) ≤ (θ.2 : ℝ) + 1
  nlinarith

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.ConsumerProblem from
f9c357ada1d9965dabd9eec694720ba585faf575.

# The consumer's problem and its basic properties

Kreps I, Proposition 3.1 and Definition 3.2, pp. 52-54. Demand is the full set
of utility-maximizing budget-feasible bundles. Continuous utility guarantees
existence; quasi-concavity gives a convex solution set and strict quasi-concavity
gives uniqueness. Local insatiability implies exhaustion of the budget.
All results permit zero income; none assumes a maximizer as an existence premise.
-/

namespace Kreps.UtilityForMoney.Demand

open scoped NNReal

/-- **Definition 3.2:** Marshallian demand is the full solution set of the consumer's problem. -/
def MarshallianDemand {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : Set (NonnegativeOrthant k) :=
  PrefChoice (UtilityPref u) (BudgetSet p y)

/-- Demand membership consists precisely of budget feasibility and utility optimality. -/
theorem mem_marshallianDemand_iff {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand u p y ↔
      x ∈ BudgetSet p y ∧ ∀ z ∈ BudgetSet p y, u z ≤ u x := Iff.rfl

/-- The alternative Mathlib formulation identifies demand with feasible global maximizers. -/
theorem mem_marshallianDemand_iff_isMaxOn {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) (x : NonnegativeOrthant k) :
    x ∈ MarshallianDemand u p y ↔ x ∈ BudgetSet p y ∧ IsMaxOn u (BudgetSet p y) x := Iff.rfl

/-- **Proposition 3.1(a):** positive joint scaling of prices and income preserves all solutions. -/
theorem proposition_3_1a {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = MarshallianDemand u p y := by
  simp only [MarshallianDemand, budgetSet_scale]

/-- **Proposition 3.1(b):** a continuous utility attains its maximum on every budget set. -/
theorem proposition_3_1b {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u)
    (p : PositivePrices k) (y : ℝ≥0) : (MarshallianDemand u p y).Nonempty := by
  obtain ⟨x, hx, hm⟩ := (budgetSet_isCompact p y).exists_isMaxOn
    (budgetSet_nonempty p y) hu.continuousOn
  exact ⟨x, hx, hm⟩

/-- At zero income, every utility has the unique feasible bundle as its unique demand. -/
theorem marshallianDemand_zero {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) : MarshallianDemand u p 0 = {ZeroBundle k} := by
  ext x
  simp only [MarshallianDemand, PrefChoice, UtilityPref, budgetSet_zero, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨And.left, fun h => ⟨h, by rw [h]⟩⟩

/-- **Proposition 3.1(c):** quasi-concavity makes the entire demand set convex. -/
theorem proposition_3_1c_convex {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : QuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) :
    ConvexMenu (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (MarshallianDemand u p y) := by
  intro x hx z hz a ha
  refine ⟨budgetSet_convex p y x hx.1 z hz.1 a ha, fun w hw => ?_⟩
  exact (le_min (hx.2 w hw) (hz.2 w hw)).trans (hu x z a ha)

/-- Strict quasi-concavity permits at most one budget-feasible maximizer. -/
theorem marshallianDemand_subsingleton {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : StrictlyQuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) : (MarshallianDemand u p y).Subsingleton := by
  intro x hx z hz
  by_contra hne
  have hbetter := hu x z hne (hx.2 z hz.1) (1 / 2) (by constructor <;> norm_num)
  have hfeasible := budgetSet_convex p y x hx.1 z hz.1 (1 / 2)
    (by constructor <;> norm_num)
  exact not_lt_of_ge (hz.2 _ hfeasible) hbetter

/-- **Proposition 3.1(c):** continuous strictly quasi-concave utility has exactly one solution. -/
theorem proposition_3_1c_unique {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hc : Continuous u)
    (hu : StrictlyQuasiConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) u)
    (p : PositivePrices k) (y : ℝ≥0) : ∃! x, x ∈ MarshallianDemand u p y := by
  obtain ⟨x, hx⟩ := proposition_3_1b hc p y
  exact ⟨x, hx, fun z hz => marshallianDemand_subsingleton hu p y hz hx⟩

/-- Local insatiability excludes a preference-best point with strictly slack expenditure. -/
theorem preferenceChoice_exhausts_budget {k : ℕ}
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : LocallyInsatiable r)
    (p : PositivePrices k) (y : ℝ≥0) {x : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (BudgetSet p y)) : Expenditure p x = (y : ℝ) := by
  apply le_antisymm hx.1
  by_contra hnot
  have hslack : Expenditure p x < (y : ℝ) := lt_of_not_ge hnot
  have hopen : IsOpen {z : NonnegativeOrthant k | Expenditure p z < (y : ℝ)} :=
    isOpen_lt (expenditure_continuous p) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hslack
  obtain ⟨z, hzx, hbetter⟩ := hr x (ε / 2) (by positivity)
  have hzlt : Expenditure p z < (y : ℝ) :=
    hball (show z ∈ Metric.ball x ε from by change dist z x < ε; linarith)
  have hz : z ∈ BudgetSet p y := hzlt.le
  exact hbetter.2 (hx.2 z hz)

/-- **Proposition 3.1(d):** locally insatiable consumers spend their entire income at a solution. -/
theorem proposition_3_1d {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : LocallyInsatiable (UtilityPref u)) (p : PositivePrices k) (y : ℝ≥0)
    {x : NonnegativeOrthant k} (hx : x ∈ MarshallianDemand u p y) :
    Expenditure p x = (y : ℝ) := preferenceChoice_exhausts_budget hu p y hx

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ConsumerDemand.IndirectUtility from
f9c357ada1d9965dabd9eec694720ba585faf575.

# Marshallian demand and indirect utility

Kreps I, Definition 3.2 and Proposition 3.3, pp. 54-56. The budget correspondence
satisfies all hypotheses of the maximum theorem, so demand is nonempty, locally
bounded and upper semicontinuous, and indirect utility is continuous. The domain
includes zero income. On every subset where demand is singleton-valued its
selection is relatively continuous, which includes the book's open subsets.
-/

namespace Kreps.UtilityForMoney.Demand

open scoped NNReal Topology

/-- **Definition 3.2:** the value of the consumer's problem, attained for continuous utility. -/
noncomputable def IndirectUtility {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) (y : ℝ≥0) : ℝ := sSup (u '' BudgetSet p y)

/-- Every demanded bundle gives exactly the indirect utility value. -/
theorem indirectUtility_eq_of_mem {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    {p : PositivePrices k} {y : ℝ≥0} {x : NonnegativeOrthant k}
    (hx : x ∈ MarshallianDemand u p y) : IndirectUtility u p y = u x :=
  parametricValue_eq_of_maximum (A := fun θ : PriceIncome k => BudgetSet θ.1 θ.2)
    (F := fun _ z => u z) (p := (p, y)) hx

/-- At zero income, indirect utility equals the utility of consuming nothing. -/
theorem indirectUtility_zero {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (p : PositivePrices k) : IndirectUtility u p 0 = u (ZeroBundle k) := by
  apply indirectUtility_eq_of_mem
  rw [marshallianDemand_zero]
  exact Set.mem_singleton _

/-- **Proposition 3.3(a):** demand and indirect utility are homogeneous of degree zero. -/
theorem proposition_3_3a {k : ℕ} (u : NonnegativeOrthant k → ℝ)
    (a : ℝ) (ha : 0 < a) (p : PositivePrices k) (y : ℝ≥0) :
    MarshallianDemand u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = MarshallianDemand u p y ∧
      IndirectUtility u (ScalePrices a ha p) (⟨a, ha.le⟩ * y) = IndirectUtility u p y := by
  refine ⟨proposition_3_1a u a ha p y, ?_⟩
  simp only [IndirectUtility, budgetSet_scale]

/-- Berge's theorem applies with every budget-continuity and compactness hypothesis discharged. -/
theorem consumer_maximum_theorem {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    (∀ θ : PriceIncome k, (MarshallianDemand u θ.1 θ.2).Nonempty) ∧
      SequentialUpper (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) ∧
      LocalCompactBound (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) ∧
      Continuous (fun θ : PriceIncome k => IndirectUtility u θ.1 θ.2) :=
  maximum_theorem (A := fun θ : PriceIncome k => BudgetSet θ.1 θ.2)
    (F := fun _ x => u x) (hu.comp continuous_snd) budgetSet_sequentialLower
    budgetSet_sequentialUpper budgetSet_localCompactBound (fun θ => budgetSet_nonempty θ.1 θ.2)

/-- **Proposition 3.3(b):** demand is upper semicontinuous in the book's closed-graph convention. -/
theorem proposition_3_3b {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u) :
    SequentialUpper (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.1

/-- The same demand correspondence has a common compact bound around each parameter. -/
theorem marshallianDemand_localCompactBound {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    LocalCompactBound (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.2.1

/-- Each complete set of demanded bundles is compact. -/
theorem marshallianDemand_isCompact {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) (p : PositivePrices k) (y : ℝ≥0) :
    IsCompact (MarshallianDemand u p y) :=
  (proposition_3_3b hu).isCompact (marshallianDemand_localCompactBound hu) (p, y)

/-- Demand also satisfies Mathlib's open-set definition of upper hemicontinuity. -/
theorem marshallianDemand_upperHemicontinuous {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) :
    UpperHemicontinuous (fun θ : PriceIncome k => MarshallianDemand u θ.1 θ.2) := by
  intro θ
  obtain ⟨K, hK, hlocal⟩ := marshallianDemand_localCompactBound hu θ
  exact sequentialUpper_upperHemicontinuousAt (proposition_3_3b hu) hK.isSeqCompact hlocal

/-- **Proposition 3.3(c):** indirect utility is continuous even at zero income. -/
theorem proposition_3_3c {k : ℕ} {u : NonnegativeOrthant k → ℝ} (hu : Continuous u) :
    Continuous (fun θ : PriceIncome k => IndirectUtility u θ.1 θ.2) :=
  (consumer_maximum_theorem hu).2.2.2

/-- **Proposition 3.3(b):** a unique demand selection is continuous on its parameter subset. -/
theorem proposition_3_3b_unique {k : ℕ} {u : NonnegativeOrthant k → ℝ}
    (hu : Continuous u) (S : Set (PriceIncome k)) (s : S → NonnegativeOrthant k)
    (hs : ∀ θ : S, MarshallianDemand u θ.val.1 θ.val.2 = {s θ}) : Continuous s := by
  apply continuous_of_singleton_correspondence
  · intro θ x θ₀ x₀ hθ hx hm
    have hmem : x₀ ∈ MarshallianDemand u θ₀.val.1 θ₀.val.2 :=
      proposition_3_3b hu (fun n => (θ n).val) x θ₀.val x₀
        (continuous_subtype_val.continuousAt.tendsto.comp hθ) hx
        (fun n => by
          change x n ∈ MarshallianDemand u (θ n).val.1 (θ n).val.2
          rw [hs (θ n)]
          exact hm n)
    rwa [hs θ₀] at hmem
  · intro θ
    obtain ⟨K, hK, hlocal⟩ := marshallianDemand_localCompactBound hu θ.val
    refine ⟨K, hK, ?_⟩
    have hrestricted := (continuous_subtype_val.continuousAt (x := θ)).eventually hlocal
    filter_upwards [hrestricted] with η hη
    rwa [hs η] at hη

end Kreps.UtilityForMoney.Demand

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.Basic from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

Local prerequisite copy from Chapter 1 at commit `f9c357a`.
Imports and namespace are adapted for this independent project.

# Choice, preference, and utility

Kreps I, §1.1, pp. 1-4: feasible choice, finite nonemptiness, choice coherence,
complete and transitive preferences, and equations (1.1)-(1.3).

Choice is extended to the empty menu by the empty set. Nonemptiness is a separate
hypothesis, imposed only on finite nonempty menus in `FiniteNonempty`.
`FeasibleOn` and `CoherentOn` retain restricted menu domains for Problems 1.15-1.16.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.StrictPreference from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

Local prerequisite copy from Chapter 1 at commit `f9c357a`.
Imports and namespace are adapted for this independent project.

# Strict preference and indifference

Kreps I, §1.4, Propositions 1.9-1.10, pp. 9-10, and Problem 1.9, p. 26.
The two presentations of rational preference are equivalent: complete, transitive
weak preference, or asymmetric, negatively transitive strict preference.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.MixtureSpace from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Mixture spaces and their preference axioms

Kreps I, Sections 5.1–5.2, pp. 88–92. Mathlib's convex spaces supply the
usual mixture identities on abstract spaces. The independence axiom compares
different common backgrounds at a fixed weight, including both endpoint weights.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.MixtureAlgebra from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Algebra of a binary mixture segment

Kreps I, p. 89. Two nested mixtures of the same prizes reduce to a single
mixture whose first probability is the weighted mean of the inner probabilities.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.Independence from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Background substitution and equally spaced comparisons

Kreps I, Lemmas 5.5–5.7, pp. 91–92. At fixed mixture weight a common
background can be replaced in either a strict or a weak comparison. Along a
single segment, comparisons separated by the same probability increment are
therefore identical. This holds before any continuity assumption is imposed.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.ProbabilityGrids from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Preferences on probability grids

Kreps I, proof of Lemma 5.7, pp. 91–92. Background substitution makes all
adjacent intervals of a grid comparable in the same direction. A chain of
those intervals transfers comparisons between endpoints to every rational grid
weight. Equal-step grids include the dyadic ones in the printed proof.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.SegmentOrder from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Order on a mixture segment

Kreps I, Lemmas 5.6–5.8, pp. 91–92. First transfer weak comparisons on rational
grids to every probability by the endpoint continuity axiom. A strictly ordered
pair then gives strict monotonicity at every positive probability increment.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.SegmentCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Calibration on a preference segment

Kreps I, Lemma 5.9, pp. 92–93. Take the supremum of the probabilities at which
the reference alternative is weakly preferred to the mixture. Either strict
ranking at this cut would contradict endpoint continuity or its supremum property.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.BoundedCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Affine utility calibrated between two anchors

Kreps I, Proposition 5.4, pp. 93–95. Within any interval with strictly ranked
endpoints, the unique indifferent probability represents all comparisons and
preserves mixtures. Other alternatives in the surrounding space need not be
bounded by these endpoints.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.UnboundedCalibration from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Calibration without global best and worst alternatives

Kreps I, pp. 94–95 and Problem 5.3, p. 118. Normalize two strictly ranked
anchors at one and zero. Alternatives between, above, and below them receive
the three values in the book's construction. Any normalized affine index on
an interval containing the three alternatives must give the same value.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.SimpleLottery from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Finite-support lotteries and expected utility

Kreps I, Definition 5.2 and equation (5.3), pp. 85–88. Prize types may be
infinite. Mathlib's standard simplex gives each lottery its own finite support.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.LotteryEvaluation from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# Recovering a prize index from an affine lottery index

Kreps I, Proposition 5.3, pp. 95–96. Agreement on sure prizes extends to the
entire simplex. Mathlib proves closure under finite convex combinations from
binary closure by splitting off one positively weighted prize and normalizing
the remaining lottery, as in the source's support induction.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.MixtureRepresentation from
commit db0d8dce6618d30395cd02429d614bca59568fe7.

# The mixture-space and expected-utility theorems

Kreps I, Propositions 5.3–5.4 and Problem 5.3, pp. 88–96, 118. Normalize two
strictly ranked anchors. For each pair of alternatives, one bounded preference
interval contains the pair, its mixtures, and the anchors. Its normalized local
utility agrees with each globally calibrated value, proving representation and
affinity even when preferences have no best or worst alternative.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Income risk resolved before consumption choice

Kreps I, Proposition 6.16, pp. 135–137. Each realized nonnegative income finances
a utility-maximizing bundle. Pushing a lottery through any optimal selection
induces the same expected indirect utility. The copied Chapter 3 results supply
actual budget maxima, continuity and exhaustion.
-/

namespace Kreps.UtilityForMoney

open scoped NNReal
open Convexity

variable {k : ℕ}

/-- Push a simple lottery through the deterministic rule selecting a consumption bundle. -/
theorem expectedUtility_map {X Y : Type*} (U : Y → ℝ) (f : X → Y) (p : SimpleLottery X) :
    ExpectedUtility U (p.map f) = ExpectedUtility (fun x => U (f x)) p := by
  rw [expectedUtility_eq_affine, expectedUtility_eq_affine, StdSimplex.affineMapMk_apply,
    StdSimplex.affineMapMk_apply, iConvexComb_map]

/-- Income lotteries are ranked by the lotteries of bundles bought after income is observed. -/
def InducedIncomePreference
    (r : SimpleLottery (Demand.NonnegativeOrthant k) → SimpleLottery (Demand.NonnegativeOrthant k) →
      Prop) (f : ℝ≥0 → Demand.NonnegativeOrthant k) (p q : SimpleLottery ℝ≥0) : Prop :=
  r (p.map f) (q.map f)

/-- All optimal selections yield expected indirect utility for an income lottery. -/
theorem incomeLottery_value {U : Demand.NonnegativeOrthant k → ℝ} (p : Demand.PositivePrices k)
    (f : ℝ≥0 → Demand.NonnegativeOrthant k) (hf : ∀ y, f y ∈ Demand.MarshallianDemand U p y)
    (q : SimpleLottery ℝ≥0) :
    ExpectedUtility U (q.map f) = ExpectedUtility (Demand.IndirectUtility U p) q := by
  rw [expectedUtility_map]
  exact congrArg (fun g => ExpectedUtility g q)
    (funext fun y => (Demand.indirectUtility_eq_of_mem (hf y)).symm)

/-- Proposition 6.16. Every optimal choice rule induces the three mixture axioms on income risk. -/
theorem proposition_6_16 {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    {r : SimpleLottery (Demand.NonnegativeOrthant k) → SimpleLottery (Demand.NonnegativeOrthant k) →
      Prop} (hr : LotteryTheory.Represents (ExpectedUtility U) r) (p : Demand.PositivePrices k) :
    (∃ f : ℝ≥0 → Demand.NonnegativeOrthant k, ∀ y, f y ∈ Demand.MarshallianDemand U p y) ∧
      ∀ f : ℝ≥0 → Demand.NonnegativeOrthant k, (∀ y, f y ∈ Demand.MarshallianDemand U p y) →
        LotteryTheory.Represents (ExpectedUtility (Demand.IndirectUtility U p))
          (InducedIncomePreference r f) ∧
          LotteryTheory.MixtureAxioms (InducedIncomePreference r f) := by
  constructor
  · exact Classical.axiomOfChoice (fun y => Demand.proposition_3_1b hU p y)
  · intro f hf
    have hi : LotteryTheory.Represents (ExpectedUtility (Demand.IndirectUtility U p))
        (InducedIncomePreference r f) := by
      intro q t
      change r (q.map f) (t.map f) ↔ _
      rw [hr, incomeLottery_value p f hf, incomeLottery_value p f hf]
    exact ⟨hi, LotteryTheory.proposition_5_3.mpr ⟨_, hi⟩⟩

/-- Part (a). Indirect utility is continuous in nonnegative income, including at the origin. -/
theorem proposition_6_16a {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (p : Demand.PositivePrices k) : Continuous (Demand.IndirectUtility U p) :=
  (Demand.proposition_3_3c hU).comp (continuous_const.prodMk continuous_id)

/-- Part (b). Local insatiability rules out equal values at two strictly ordered incomes. -/
theorem proposition_6_16b {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hi : Demand.LocallyInsatiable (Demand.UtilityPref U)) (p : Demand.PositivePrices k) :
    StrictMono (Demand.IndirectUtility U p) := by
  intro y z hyz
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hU p y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hU p z
  rw [Demand.indirectUtility_eq_of_mem hx, Demand.indirectUtility_eq_of_mem hw]
  apply lt_of_not_ge
  intro hle
  have hy : Demand.Expenditure p x ≤ (y : ℝ) := hx.1
  have hxz : x ∈ Demand.MarshallianDemand U p z :=
    ⟨hy.trans (show (y : ℝ) ≤ (z : ℝ) from hyz.le),
      fun t ht => (show U t ≤ U w from hw.2 t ht).trans hle⟩
  have he := Demand.proposition_3_1d hi p z hxz
  exact (show (y : ℝ) < (z : ℝ) from hyz).not_ge (he ▸ hy)

/-- Part (c). A mixture of two optimal bundles is affordable at the corresponding mixed income. -/
theorem proposition_6_16c {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (p : Demand.PositivePrices k) : ConcaveOn ℝ (Set.Ici 0)
      (fun y : ℝ => Demand.IndirectUtility U p y.toNNReal) := by
  refine ⟨convex_Ici _, ?_⟩
  intro y hy z hz a b ha hb hab
  let Y : ℝ≥0 := ⟨y, hy⟩
  let Z : ℝ≥0 := ⟨z, hz⟩
  let m := a * y + b * z
  have hm : 0 ≤ m := add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hz)
  let M : ℝ≥0 := ⟨m, hm⟩
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hU p Y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hU p Z
  obtain ⟨t, ht⟩ := Demand.proposition_3_1b hU p M
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
  let v := Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x w a ha'
  have hv : v ∈ Demand.BudgetSet p M := by
    change Demand.Expenditure p v ≤ m
    rw [show Demand.Expenditure p v = _ from Demand.expenditure_mix p x w a ha',
      show 1 - a = b by linarith]
    exact add_le_add (mul_le_mul_of_nonneg_left (show Demand.Expenditure p x ≤ y from hx.1) ha)
      (mul_le_mul_of_nonneg_left (show Demand.Expenditure p w ≤ z from hw.1) hb)
  have huv := hc x w a ha'
  have huv' : a * U x + b * U w ≤ U v := by simpa only [← show 1 - a = b by linarith] using huv
  have hco (c : ℝ) (h : 0 ≤ c) : c.toNNReal = ⟨c, h⟩ := NNReal.eq (Real.coe_toNNReal c h)
  change a * Demand.IndirectUtility U p y.toNNReal + b * Demand.IndirectUtility U p z.toNNReal ≤
    Demand.IndirectUtility U p m.toNNReal
  rw [hco y hy, hco z hz, hco m hm, Demand.indirectUtility_eq_of_mem hx,
    Demand.indirectUtility_eq_of_mem hw, Demand.indirectUtility_eq_of_mem ht]
  exact huv'.trans (ht.2 v hv)

/-- Concavity gives the income risk-aversion comparison at every finite-support lottery. -/
theorem incomeLottery_risk_averse {U : Demand.NonnegativeOrthant k → ℝ} (hU : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (p : Demand.PositivePrices k) (q : SimpleLottery ℝ≥0) :
    ExpectedUtility (Demand.IndirectUtility U p) q ≤
      Demand.IndirectUtility U p (ExpectedUtility (fun y : ℝ≥0 => (y : ℝ)) q).toNNReal := by
  simpa only [Real.toNNReal_coe] using expectedUtility_jensen (proposition_6_16c hU hc p)
    (fun y : ℝ≥0 => (y : ℝ)) (fun y => y.property) q

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two-stage monetary lottery in Figure 6.2

Kreps I, pp. 133–135. The six terminal branch probabilities are the products
of the first-stage probabilities and the conditional probabilities. Pushing the
common branch law forward recovers all three marginal distributions.
-/

namespace Kreps.UtilityForMoney

/-- Joint weights of the six terminal branches, ordered in pairs by initial prize. -/
noncomputable def Figure62States : SimpleLottery (Fin 6) where
  weights := Finsupp.equivFunOnFinite.symm ![1/5, 1/5, 3/20, 1/20, 1/5, 1/5]
  nonneg := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Finsupp.sum_fintype, Fin.sum_univ_succ]

/-- First-stage prize on each of the six joint branches. -/
def Figure62Initial : Fin 6 → ℝ := ![0, 0, 5, 5, 10, 10]

/-- Conditional supplement, in the same branch order. -/
def Figure62Supplement : Fin 6 → ℝ := ![-3, 3, -2, 3, -2, 2]

/-- The net final prize adds the supplement on the same branch. -/
def Figure62Final (i : Fin 6) : ℝ := Figure62Initial i + Figure62Supplement i

/-- Evaluation on the common state law before collecting repeated prizes. -/
theorem figure62_states_value (f : Fin 6 → ℝ) :
    ExpectedUtility f Figure62States =
      f 0 / 5 + f 1 / 5 + 3 * f 2 / 20 + f 3 / 20 + f 4 / 5 + f 5 / 5 := by
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp)]
  norm_num [Figure62States, Fin.sum_univ_succ]
  ring

/-- **Figure 6.2(a):** the initial distribution has masses 0.4, 0.2 and 0.4. -/
theorem figure62_initial_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Initial) =
      2/5 * U 0 + 1/5 * U 5 + 2/5 * U 10 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Initial]
  ring

/-- **Figure 6.2(c):** the reduced final law has masses 0.2, 0.35, 0.25 and 0.2. -/
theorem figure62_final_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Final) =
      1/5 * U (-3) + 7/20 * U 3 + 1/4 * U 8 + 1/5 * U 12 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Final, Figure62Initial, Figure62Supplement]
  ring

/-- Footnote 10: the marginal law of the supplement, collected across the three rows. -/
theorem figure62_supplement_law (U : ℝ → ℝ) :
    ExpectedUtility U (Figure62States.map Figure62Supplement) =
      1/5 * U (-3) + 7/20 * U (-2) + 1/5 * U 2 + 1/4 * U 3 := by
  rw [expectedUtility_map, figure62_states_value]
  norm_num [Function.comp_def, Figure62Supplement]
  ring

/-- The three conditional supplement distributions all have nonpositive mean. -/
theorem figure62_conditional_means :
    (1/2 : ℝ) * (-3) + 1/2 * 3 = 0 ∧
      (3/4 : ℝ) * (-2) + 1/4 * 3 = -(3/4) ∧
      (1/2 : ℝ) * (-2) + 1/2 * 2 = 0 := by norm_num

/-- The initial three-outcome lottery second-order dominates the final four-outcome lottery. -/
theorem figure62_secondOrder :
    SecondOrderDominates (Figure62States.map Figure62Initial)
      (Figure62States.map Figure62Final) := by
  intro U hi hc
  rw [figure62_final_law, figure62_initial_law]
  have h (x y a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b = 1) (hz : a*x+b*y ≤ z) :
      a * U x + b * U y ≤ U z :=
    (hc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hs).trans (hi hz)
  linarith [h (-3) 3 (1/2) (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 3 8 (3/4) (1/4) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 8 12 (1/2) (1/2) 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Capped-linear tests for second-order dominance

Kreps I, Proposition 6.14(b) and Problem 6.6. On the union of two finite supports
an increasing concave utility can be interpolated by nonnegative combinations of
capped-linear tests and a constant. The induction removes the last segment's
slope before interpolating the preceding points. It allows arbitrary real prizes.
-/

namespace Kreps.UtilityForMoney

/-- Expectations of a sum with a scaled component distribute over a finite lottery. -/
theorem expectedUtility_add_scaled {X : Type*} (p : SimpleLottery X) (f g : X → ℝ) (a : ℝ) :
    ExpectedUtility (fun x => f x + a * g x) p = ExpectedUtility f p + a * ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- All earlier secants of a concave function dominate the last segment's slope. -/
theorem last_secant_le {U : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ U)
    {x y b r : ℝ} (hxy : x < y) (hyb : y ≤ b) (hbr : b < r) :
    (U r - U b) / (r - b) ≤ (U y - U x) / (y - x) := by
  rcases hyb.eq_or_lt with rfl | h
  · exact hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) hxy hbr
  · exact (hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) h hbr).trans
      (hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) hxy h)

/-- Interpolate the specified concave utility on a finite set while preserving the capped tests. -/
theorem exists_cap_interpolant (p q : SimpleLottery ℝ)
    (ht : ∀ r : ℝ, ExpectedUtility (fun x => min x r) q ≤ ExpectedUtility (fun x => min x r) p)
    (T : Finset ℝ) (U : ℝ → ℝ) (hc : ConcaveOn ℝ Set.univ U) (hm : MonotoneOn U T) :
    ∃ f : ℝ → ℝ, ExpectedUtility f q ≤ ExpectedUtility f p ∧ (∀ x ∈ T, f x = U x) ∧
      ∀ v w, (∀ t ∈ T, t ≤ v) → (∀ t ∈ T, t ≤ w) → f v = f w := by
  classical
  induction T using Finset.induction_on_max generalizing U with
  | empty =>
    exact ⟨fun _ => 0, by simp [expectedUtility_const], by simp, by simp⟩
  | insert r T htop ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · refine ⟨fun _ => U r, by simp [expectedUtility_const], ?_, by simp⟩
      simp
    let b := T.max' hT
    have hb : b ∈ T := T.max'_mem hT
    have hbr : b < r := htop b hb
    let m := (U r - U b) / (r - b)
    have hm₀ : 0 ≤ m := div_nonneg (sub_nonneg.mpr (hm
      (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hbr.le)) (sub_nonneg.mpr hbr.le)
    have hmr : m * (r - b) = U r - U b := div_mul_cancel₀ _ (sub_ne_zero.mpr hbr.ne')
    let V (z : ℝ) := U z - m * z
    have hcV : ConcaveOn ℝ Set.univ V := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a c ha hh hsum
      have h := hc.2 hx hy ha hh hsum
      simp only [smul_eq_mul, V] at *
      linarith only [h]
    have hmV : MonotoneOn V T := by
      intro x hx y hy hxy
      rcases hxy.eq_or_lt with rfl | h
      · exact le_rfl
      · have hs := last_secant_le hc h (T.le_max' _ hy) hbr
        have he := (le_div_iff₀ (sub_pos.mpr h)).mp hs
        change U x - m * x ≤ U y - m * y
        change m * (y - x) ≤ U y - U x at he
        linarith
    obtain ⟨f, hpass, hval, hflat⟩ := ih V hcV hmV
    let F (x : ℝ) := f x + m * min x r
    refine ⟨F, ?_, ?_, ?_⟩
    · change ExpectedUtility (fun x => f x + m * min x r) q ≤ _
      rw [expectedUtility_add_scaled, show ExpectedUtility F p =
        ExpectedUtility f p + m * ExpectedUtility (fun x => min x r) p from
        expectedUtility_add_scaled p f _ m]
      exact add_le_add hpass (mul_le_mul_of_nonneg_left (ht r) hm₀)
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have he := hflat z b (fun t ht => (htop t ht).le) (fun t ht => T.le_max' t ht)
        dsimp only [F]
        rw [min_self, he, hval b hb]
        dsimp only [V]
        linarith
      · dsimp only [F]
        rw [min_eq_left (htop z hz).le, hval z hz]
        dsimp only [V]
        ring
    · intro v w hv hw
      dsimp only [F]
      rw [min_eq_right (hv r (Finset.mem_insert_self _ _)),
        min_eq_right (hw r (Finset.mem_insert_self _ _)),
        hflat v w (fun t ht => hv t (Finset.mem_insert_of_mem ht))
          (fun t ht => hw t (Finset.mem_insert_of_mem ht))]

/-- Expected shortfalls at all thresholds characterize the increasing concave order. -/
theorem secondOrder_iff_shortfalls (p q : SimpleLottery ℝ) : SecondOrderDominates p q ↔
    ∀ r, ExpectedShortfall p r ≤ ExpectedShortfall q r := by
  refine ⟨fun h => expectedShortfall_le_of_secondOrder h, ?_⟩
  intro hs U hm hc
  have ht (r : ℝ) : ExpectedUtility (fun x => min x r) q ≤
      ExpectedUtility (fun x => min x r) p := by
    have he : (fun x : ℝ => min x r) = fun x => -1 * max (r - x) 0 + r := by
      funext x
      rcases le_total x r with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]; ring
      · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]; ring
    rw [he, expectedUtility_affine_payoff, expectedUtility_affine_payoff]
    have h := hs r
    unfold ExpectedShortfall at h
    linarith
  let T := p.weights.support ∪ q.weights.support
  obtain ⟨f, hp, hv, _⟩ := exists_cap_interpolant p q ht T U hc (fun _ _ _ _ h => hm h)
  have he (w : SimpleLottery ℝ) (hw : w.weights.support ⊆ T) :
      ExpectedUtility f w = ExpectedUtility U w :=
    Finset.sum_congr rfl fun x hx => congrArg (w.weights x * ·) (hv x (hw hx))
  rwa [he p Finset.subset_union_left, he q Finset.subset_union_right] at hp

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.MeasureMixtures from
commit db0d8dce6618d30395cd02429d614bca59568fe7.
# Mixtures of Borel probability measures

Kreps I, Proposition 5.10, pp. 98–100. A finite mixture of probability measures is
an actual measure with total mass one. Evaluation on every measurable event
identifies its convex-space structure. Weak convergence is Mathlib's topology
of convergence of integrals against bounded continuous functions.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.WeakApproximation from
commit db0d8dce6618d30395cd02429d614bca59568fe7.
# Approximating Borel probabilities by lotteries of finite support

Kreps I, pp. 98–99. Approximating the identity map pointwise by measurable simple
functions induces a sequence of finite lotteries. The probabilities are the
actual masses of their fibers. Bounded convergence proves weak convergence.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
Local prerequisite copy of ChoiceUnderUncertainty.WeakUtilityContinuity from
commit db0d8dce6618d30395cd02429d614bca59568fe7.
# Weak continuity and bounded affine utility

Kreps I, Proposition 5.10, pp. 98–100. Open strict contours make an affine
representation continuous, since it takes every value between its attainable
levels. Weak continuity on the entire probability space forces boundedness:
vanishing weights on arbitrarily distant utility values contradict continuity.
-/

namespace Kreps.UtilityForMoney.LotteryTheory

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

end Kreps.UtilityForMoney.LotteryTheory

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuity in lottery probabilities and prizes

Kreps I, pp. 124–125. With support in a common finite set, expected utility
is continuous in probabilities for arbitrary prize values. Weak convergence
suffices for bounded continuous utility and for continuous utility on a common
compact set of prizes. The latter formulation covers uniformly bounded prizes
when the monetary domain is the real line.
-/

namespace Kreps.UtilityForMoney

open Filter Convexity MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- Extra zero-probability prizes preserve the support sum. -/
theorem expectedUtility_sum_over {X : Type*} (U : X → ℝ) (p : SimpleLottery X) (T : Finset X)
    (hp : p.weights.support ⊆ T) : ExpectedUtility U p = ∑ x ∈ T, p.weights x * U x :=
  Finset.sum_subset hp fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx]

/-- On a common finite set of possible prizes coordinatewise convergence of weights suffices. -/
theorem expectedUtility_tendsto_fixed_support {X : Type*} (U : X → ℝ) (T : Finset X)
    (p : SimpleLottery X) (q : ℕ → SimpleLottery X) (hp : p.weights.support ⊆ T)
    (hq : ∀ n, (q n).weights.support ⊆ T)
    (hw : ∀ x ∈ T, Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  simp only [expectedUtility_sum_over U p T hp, fun n => expectedUtility_sum_over U (q n) T (hq n)]
  exact tendsto_finsetSum _ fun x hx => (hw x hx).mul_const _

/-- Both strict comparisons with any fixed lottery persist eventually. -/
theorem lottery_strict_rankings_eventually {X : Type*} (U : X → ℝ) (p r : SimpleLottery X)
    (q : ℕ → SimpleLottery X)
    (h : Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p))) :
    (ExpectedUtility U r < ExpectedUtility U p →
      ∀ᶠ n in atTop, ExpectedUtility U r < ExpectedUtility U (q n)) ∧
    (ExpectedUtility U p < ExpectedUtility U r →
      ∀ᶠ n in atTop, ExpectedUtility U (q n) < ExpectedUtility U r) :=
  ⟨fun hl => h.eventually (isOpen_Ioi.mem_nhds hl),
    fun hg => h.eventually (isOpen_Iio.mem_nhds hg)⟩

/-- With continuous utility, finitely many probability weights and prize locations can both vary. -/
theorem expectedUtility_tendsto_moving_prizes {X I : Type*} [TopologicalSpace X] [Finite I]
    (U : X → ℝ) (hU : Continuous U) (p : SimpleLottery I) (q : ℕ → SimpleLottery I)
    (x : I → X) (z : ℕ → I → X)
    (hw : ∀ i, Tendsto (fun n => (q n).weights i) atTop (𝓝 (p.weights i)))
    (hx : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ExpectedUtility (fun i => U (z n i)) (q n)) atTop
      (𝓝 (ExpectedUtility (fun i => U (x i)) p)) := by
  let : Fintype I := Fintype.ofFinite I
  have he (u : I → ℝ) (w : SimpleLottery I) : ExpectedUtility u w = ∑ i, w.weights i * u i :=
    Finsupp.sum_fintype _ _ (by simp)
  simp only [he]
  exact tendsto_finsetSum _ fun i _ => (hw i).mul (hU.continuousAt.tendsto.comp (hx i))

/-- The illustrative two-outcome tables on p. 124 have these exact expected utilities. -/
theorem nearby_money_lotteries (U : ℝ → ℝ) :
    ExpectedUtility U (BinaryLottery 4 6 (3/10) (by constructor <;> norm_num)) =
      3/10 * U 4 + 7/10 * U 6 ∧
    ExpectedUtility U (BinaryLottery (39/10) (121/20) (29/100) (by constructor <;> norm_num)) =
      29/100 * U (39/10) + 71/100 * U (121/20) := by
  constructor
  · simpa only [show (1 : ℝ) - 3/10 = 7/10 by norm_num] using
      expectedUtility_binary U 4 6 (3/10) (by constructor <;> norm_num)
  · simpa only [show (1 : ℝ) - 29/100 = 71/100 by norm_num] using
      expectedUtility_binary U (39/10) (121/20) (29/100) (by constructor <;> norm_num)

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- Bounded continuous prize utility preserves weak convergence even when supports change. -/
theorem expectedUtility_tendsto_weak (U : X →ᵇ ℝ) (q : ℕ → SimpleLottery X) (p : SimpleLottery X)
    (hw : Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop
      (𝓝 (LotteryTheory.AtomicProbability p))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction U).continuousAt
    |>.tendsto.comp hw
  change Tendsto (fun n => LotteryTheory.ExpectedUtility U (q n)) atTop
    (𝓝 (LotteryTheory.ExpectedUtility U p))
  simpa only [Function.comp_def, LotteryTheory.integral_atomicProbability] using h

/-- Common compact support gives weak convergence of values even for globally unbounded utility. -/
theorem expectedUtility_tendsto_on_compact (U : X → ℝ) (hu : Continuous U) {K : Set X}
    (hK : IsCompact K) (q : ℕ → SimpleLottery X) (p : SimpleLottery X)
    (hp : ∀ x ∈ p.weights.support, x ∈ K) (hq : ∀ n x, x ∈ (q n).weights.support → x ∈ K)
    (hw : Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop
      (𝓝 (LotteryTheory.AtomicProbability p))) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  let B := max C 0
  let g (x : X) := min B (max (-B) (U x))
  have hg (x : X) : |g x| ≤ B := abs_le.mpr
    ⟨le_min (by dsimp [B]; linarith [le_max_right C 0]) (le_max_left _ _), min_le_left _ _⟩
  let G : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨g, continuous_const.inf (continuous_const.sup hu)⟩ (B+B) (fun x y =>
      (abs_sub (g x) (g y)).trans (add_le_add (hg x) (hg y)))
  have he (w : SimpleLottery X) (h : ∀ x ∈ w.weights.support, x ∈ K) :
      ExpectedUtility G w = ExpectedUtility U w := by
    apply Finset.sum_congr rfl
    intro x hx
    have hb : |U x| ≤ B := (hC x (h x hx)).trans (le_max_left _ _)
    change w.weights x * min B (max (-B) (U x)) = _
    rw [max_eq_right (abs_le.mp hb).1, min_eq_right (abs_le.mp hb).2]
  simpa only [he p hp, fun n => he (q n) (hq n)] using expectedUtility_tendsto_weak G q p hw

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two stochastic dominance orders

Kreps I, p. 132. Both dominance relations are partial orders on monetary laws.
For antisymmetry, differences of three capped payoffs recover the mass of each
individual prize on the finite union of the two supports.
-/

namespace Kreps.UtilityForMoney

/-- Mutual aversion rankings identify expected utility for every increasing capped payoff. -/
theorem capped_values_equal {p q : SimpleLottery ℝ}
    (hp : SecondOrderDominates p q) (hq : SecondOrderDominates q p) (r : ℝ) :
    ExpectedUtility (fun x => min x r) p = ExpectedUtility (fun x => min x r) q := by
  have h := cappedPrizeUtility_properties r
  exact le_antisymm (hq _ h.1 h.2) (hp _ h.1 h.2)

/-- A finite grid admits a positive gap separating any point from its other grid points. -/
theorem finite_prize_gap (T : Finset ℝ) (r : ℝ) :
    ∃ e > 0, ∀ x ∈ T, x ≠ r → e ≤ |x-r| := by
  classical
  by_cases h : (T.erase r).Nonempty
  · let e := (T.erase r).inf' h (fun x => |x-r|)
    obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_inf' h (fun x => |x-r|)
    refine ⟨e, ?_, fun x hx hn => Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hn, hx⟩)⟩
    rw [show e = |x-r| from he]
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_erase.mp hx).1)
  · exact ⟨1, zero_lt_one, fun x hx hn => (h ⟨x, Finset.mem_erase.mpr ⟨hn, hx⟩⟩).elim⟩

/-- A difference of three capped values can isolate one mass on a finite prize grid. -/
theorem secondOrder_antisymm {p q : SimpleLottery ℝ}
    (hp : SecondOrderDominates p q) (hq : SecondOrderDominates q p) : p = q := by
  classical
  apply Convexity.StdSimplex.ext
  ext r
  let T := insert r (p.weights.support ∪ q.weights.support)
  obtain ⟨e, he, hgap⟩ := finite_prize_gap T r
  let F (x : ℝ) := min x (r+e) + min x (r-e) - 2 * min x r
  have aux (w : SimpleLottery ℝ) : ExpectedUtility F w =
      ExpectedUtility (fun x => min x (r+e)) w + ExpectedUtility (fun x => min x (r-e)) w -
        2 * ExpectedUtility (fun x => min x r) w := by
    unfold ExpectedUtility Finsupp.sum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    ring
  have hF : ExpectedUtility F p = ExpectedUtility F q := by
    simp only [aux, capped_values_equal hp hq]
  have at_r : F r = -e := by
    dsimp only [F]
    rw [min_eq_left (by linarith : r ≤ r+e), min_eq_right (by linarith : r-e ≤ r), min_self]
    ring
  have elsewhere (x : ℝ) (hx : x ∈ T) (hn : x ≠ r) : F x = 0 := by
    have hg := hgap x hx hn
    rcases lt_or_gt_of_ne hn with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h.le)] at hg
      dsimp only [F]
      rw [min_eq_left (by linarith : x ≤ r+e), min_eq_left (by linarith : x ≤ r-e),
        min_eq_left h.le]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h.le)] at hg
      dsimp only [F]
      rw [min_eq_right (by linarith : r+e ≤ x), min_eq_right (by linarith : r-e ≤ x),
        min_eq_right h.le]
      ring
  have val (w : SimpleLottery ℝ) (hw : w.weights.support ⊆ T) :
      ExpectedUtility F w = w.weights r * -e := by
    rw [expectedUtility_sum_over F w T hw,
      Finset.sum_eq_single_of_mem r (Finset.mem_insert_self _ _)]
    · rw [at_r]
    · intro x hx hn
      rw [elsewhere x hx hn, mul_zero]
  have sub : p.weights.support ∪ q.weights.support ⊆ T := Finset.subset_insert _ _
  rw [val p (Finset.subset_union_left.trans sub), val q (Finset.subset_union_right.trans sub)] at hF
  exact (mul_left_inj' (neg_ne_zero.mpr he.ne')).mp hF

/-- First-order dominance is antisymmetric on actual prize laws. -/
theorem firstOrder_antisymm {p q : SimpleLottery ℝ}
    (hp : FirstOrderDominates p q) (hq : FirstOrderDominates q p) : p = q :=
  secondOrder_antisymm (fun U hm _ => hp U hm) (fun U hm _ => hq U hm)

/-- The two dominance relations are reflexive. -/
theorem dominance_reflexive (p : SimpleLottery ℝ) :
    FirstOrderDominates p p ∧ SecondOrderDominates p p :=
  ⟨fun _ _ => le_rfl, fun _ _ _ => le_rfl⟩

/-- Both stochastic rankings compose transitively. -/
theorem dominance_transitive (p q r : SimpleLottery ℝ) :
    (FirstOrderDominates p q → FirstOrderDominates q r → FirstOrderDominates p r) ∧
    (SecondOrderDominates p q → SecondOrderDominates q r → SecondOrderDominates p r) :=
  ⟨fun hp hq U hm => (hq U hm).trans (hp U hm),
    fun hp hq U hm hc => (hq U hm hc).trans (hp U hm hc)⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equally likely consumption gambles and concavity

Kreps I, footnote 12, p. 137. Continuity lets equally likely binary gambles
test full concavity. Along a segment subtract the chord joining the endpoint
utilities. A negative minimum would be the midpoint of an endpoint with zero
gap and a second point with no smaller gap, contradicting midpoint concavity.
-/

namespace Kreps.UtilityForMoney

/-- A continuous midpoint-concave gap vanishing at both endpoints is nonnegative throughout. -/
theorem midpoint_gap_nonneg (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1))
    (hm : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (f x + f y) / 2 ≤ f ((x + y) / 2)) (h₀ : f 0 = 0) (h₁ : f 1 = 0) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z := by
  have hz : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have ho : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨t, ht, hlo⟩ := isCompact_Icc.exists_isMinOn ⟨0, hz⟩ hc
  suffices he : 0 ≤ f t from fun z h => he.trans (hlo h)
  rcases le_or_gt t (1/2) with h | h
  · have hv : 2*t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
    have hh := hm 0 hz _ hv
    rw [h₀, show (0 + 2*t)/2 = t by ring] at hh
    have hl : f t ≤ f (2*t) := hlo hv
    linarith
  · have hv : 2*t-1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    have hh := hm _ hv 1 ho
    rw [h₁, show (2*t-1+1)/2 = t by ring] at hh
    have hl : f t ≤ f (2*t-1) := hlo hv
    linarith

/-- Under continuity, a weak preference for the sure midpoint in every fair binary gamble
gives Jensen's inequality for every mixing weight, including the endpoints. -/
theorem concavity_of_equal_probability_gambles {k : ℕ}
    (U : Demand.NonnegativeOrthant k → ℝ) (hU : Continuous U)
    (hm : ∀ x y, (U x + U y) / 2 ≤ U (Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ))
      x y (1 / 2) (by constructor <;> norm_num))) :
    Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U := by
  intro x y a ha
  let z (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) := Demand.Mix
    (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x y t ht
  let f (t : ℝ) := if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    U (z t ht) - (t * U x + (1-t) * U y) else 0
  have he (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      f t = U (z t ht) - (t * U x + (1-t) * U y) := dite_eq_left ht
  have hz : Continuous (fun t : Set.Icc (0 : ℝ) 1 => z t.val t.property) := by
    apply Continuous.subtype_mk
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 => t.val • x.val + (1-t.val) • y.val)
    fun_prop
  have hc : ContinuousOn f (Set.Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 => f t.val)
    simp only [fun t : Set.Icc (0 : ℝ) 1 => he t.val t.property]
    exact (hU.comp hz).sub ((continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const))
  have hmid (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
      (f v + f w)/2 ≤ f ((v+w)/2) := by
    have hav : (v+w)/2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hv.1, hw.1], by linarith [hv.2, hw.2]⟩
    have h := hm (z v hv) (z w hw)
    have hpos : (1/2 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
    have heq : Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (z v hv) (z w hw)
        (1/2) hpos = z ((v+w)/2) hav := by
      ext i
      change 1/2 * (v*x.val i + (1-v)*y.val i) + (1-1/2) * (w*x.val i + (1-w)*y.val i) =
        ((v+w)/2) * x.val i + (1-(v+w)/2) * y.val i
      ring
    have h' := h.trans_eq (congrArg U heq)
    rw [he v hv, he w hw, he _ hav]
    linarith only [h']
  have h₀ : f 0 = 0 := by
    rw [he 0 (by norm_num)]
    simp [z, Demand.Mix]
  have h₁ : f 1 = 0 := by
    rw [he 1 (by norm_num)]
    simp [z, Demand.Mix]
  have h := midpoint_gap_nonneg f hc hmid h₀ h₁ a ha
  rw [he a ha] at h
  exact sub_nonneg.mp h

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Weak limits and small-probability monetary prizes

Kreps I, footnote 3, pp. 124–125. A vanishing chance of a prize with sufficiently
large utility alters an expected-utility ranking even as the laws converge weakly
to a sure prize. On an interval with an excluded endpoint, bounded monetary prizes
can likewise leave every compact subset of the prize domain.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory Filter Convexity
open scoped Topology

attribute [local instance] LotteryTheory.BorelConvexSpace

variable {X : Type*} [MeasurableSpace X]

/-- The probability law of a binary lottery is the indicated mixture of Dirac laws. -/
theorem binaryLottery_law (x y : X) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    LotteryTheory.AtomicProbability (BinaryLottery x y a ha) =
      LotteryTheory.Mix ⟨a, ha⟩ (diracProba x) (diracProba y) := by
  rw [LotteryTheory.AtomicProbability, LotteryTheory.measureCombination_eq_barycenter,
    BinaryLottery]
  rw [(StdSimplex.isAffineMap_map ℝ diracProba).map_convexCombPair, sConvexComb_convexCombPair]
  simp only [StdSimplex.map_single, sConvexComb_single, LotteryTheory.Mix]

/-- The rare prize receives probability one over the positive trial index. -/
noncomputable def RareWeight (n : ℕ) : LotteryTheory.Weight :=
  ⟨1 / ((n : ℝ) + 1), by positivity,
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩

/-- The weak law of the rare-prize lottery tends to the unchanged sure prize. -/
theorem rareLottery_weak_limit [TopologicalSpace X] [OpensMeasurableSpace X] (x : ℕ → X) (x₀ : X) :
    Tendsto (fun n => LotteryTheory.AtomicProbability
      (BinaryLottery (x n) x₀ (RareWeight n).val (RareWeight n).property)) atTop
      (𝓝 (diracProba x₀)) := by
  simp only [binaryLottery_law]
  exact LotteryTheory.weakMix_tendsto (diracProba x₀) (fun n => diracProba (x n))
    RareWeight tendsto_one_div_add_atTop_nhds_zero_nat

/-- Footnote 3. A fixed binary lottery with the intermediate utility separates the rankings. -/
theorem unbounded_prize_reversal [TopologicalSpace X] [OpensMeasurableSpace X]
    (U : X → ℝ) (x₀ : X) (hun : ∀ c : ℝ, ∃ x, c < U x) :
    ∃ (q : ℕ → SimpleLottery X) (r : SimpleLottery X),
      Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop (𝓝 (diracProba x₀)) ∧
      ExpectedUtility U r = U x₀ + 1 / 2 ∧
      ∀ᶠ n in atTop, ExpectedUtility U r < ExpectedUtility U (q n) := by
  choose x hx using fun n : ℕ => hun ((n : ℝ) + 1)
  obtain ⟨z, hz⟩ := hun (U x₀ + 1)
  let a := (1 / 2) / (U z - U x₀)
  have hd : 0 < U z - U x₀ := by linarith
  have ha : a ∈ Set.Icc 0 1 := ⟨div_nonneg (by norm_num) hd.le, (div_le_one hd).mpr (by linarith)⟩
  let r := BinaryLottery z x₀ a ha
  let q (n : ℕ) := BinaryLottery (x n) x₀ (RareWeight n).val (RareWeight n).property
  have hv : ExpectedUtility U r = U x₀ + 1 / 2 := by
    change ExpectedUtility U (BinaryLottery z x₀ a ha) = _
    rw [expectedUtility_binary U z x₀ a ha]
    have he : a * (U z - U x₀) = 1 / 2 := div_mul_cancel₀ _ hd.ne'
    linarith only [he]
  refine ⟨q, r, rareLottery_weak_limit x x₀, hv, ?_⟩
  have hw : Tendsto (fun n => (RareWeight n).val) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).sub hw).mul_const (U x₀)
  have hlim : Tendsto (fun n => 1 + (1 - (RareWeight n).val) * U x₀) atTop (𝓝 (1 + U x₀)) := by
    simpa only [sub_zero, one_mul] using (tendsto_const_nhds (x := (1 : ℝ))).add hl
  have hh := hlim.eventually (lt_mem_nhds (show U x₀ + 1/2 < 1 + U x₀ by linarith))
  filter_upwards [hh] with n hn
  have hd' : 0 < (n : ℝ) + 1 := by positivity
  have hg : 1 < (RareWeight n).val * U (x n) := by
    change 1 < 1 / ((n : ℝ) + 1) * U (x n)
    rw [one_div_mul_eq_div, one_lt_div hd']
    exact hx n
  rw [hv, show ExpectedUtility U (q n) = _ from
    expectedUtility_binary U (x n) x₀ (RareWeight n).val (RareWeight n).property]
  change U x₀ + 1/2 < 1 + (1 - (RareWeight n).val) * U x₀ at hn
  linarith

/-- A continuous increasing utility on positive wealth with an excluded zero endpoint. -/
noncomputable def OpenWealthUtility (x : Set.Ioi (0 : ℝ)) : ℝ := -x.val⁻¹

/-- The open-domain utility is continuous and strictly increasing at every admissible wealth. -/
theorem openWealthUtility_regular :
    Continuous OpenWealthUtility ∧ StrictMono OpenWealthUtility := by
  exact ⟨(continuous_subtype_val.inv₀ (fun x => x.property.ne')).neg,
    fun x y h => neg_lt_neg_iff.mpr (inv_lt_inv₀ y.property x.property |>.mpr h)⟩

/-- Bounded prizes on an open interval can converge weakly while their expected utilities differ. -/
theorem bounded_prizes_open_endpoint :
    ∃ (q : ℕ → SimpleLottery (Set.Ioi (0 : ℝ))) (b : Set.Ioi (0 : ℝ)),
      (∀ n x, x ∈ (q n).weights.support → x.val ≤ 1) ∧
      Tendsto (fun n => LotteryTheory.AtomicProbability (q n)) atTop (𝓝 (diracProba b)) ∧
      OpenWealthUtility b = -1 ∧ ∀ n, ExpectedUtility OpenWealthUtility (q n) = -2 := by
  let b : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let x (n : ℕ) : Set.Ioi (0 : ℝ) :=
    ⟨1 / ((n : ℝ) + 2), show 0 < 1 / ((n : ℝ) + 2) by positivity⟩
  let q (n : ℕ) := BinaryLottery (x n) b (RareWeight n).val (RareWeight n).property
  refine ⟨q, b, ?_, rareLottery_weak_limit x b, by norm_num [OpenWealthUtility, b], ?_⟩
  · intro n z hz
    by_cases he : z = x n
    · subst z
      change 1 / ((n : ℝ) + 2) ≤ 1
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    by_cases hb : z = b
    · subst z
      exact le_rfl
    exfalso
    apply (Finsupp.mem_support_iff.mp hz)
    change (LotteryTheory.Mix (RareWeight n) (LotteryTheory.PureLottery (x n))
      (LotteryTheory.PureLottery b)).weights z = 0
    rw [LotteryTheory.lottery_mix_weight]
    simp [LotteryTheory.PureLottery, Finsupp.single_eq_of_ne he, Finsupp.single_eq_of_ne hb]
  · intro n
    rw [show ExpectedUtility OpenWealthUtility (q n) = _ from
      expectedUtility_binary OpenWealthUtility (x n) b (RareWeight n).val (RareWeight n).property]
    simp [OpenWealthUtility, x, b, RareWeight]
    field_simp
    ring

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Inverse-CDF sampling for general probability laws

Kreps I, Problem 6.5(b), footnote 15, p. 141. For any probability measure on
the real line, the generalized inverse of its right-continuous distribution
function pushes a uniform draw forward to the original law. The construction
uses the open unit interval, whose omitted endpoints have zero uniform mass.
-/

namespace Kreps.UtilityForMoney

open Filter MeasureTheory ProbabilityTheory Set Topology

/-- Lower quantile of a real probability law, with a default at zero-mass endpoints. -/
noncomputable def GeneralQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf {x : ℝ | u ≤ cdf μ x} else 0

/-- The basic inverse-CDF equivalence at every draw strictly between zero and one. -/
theorem generalQuantile_le_iff (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    GeneralQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  let A : Set ℝ := {y | u ≤ cdf μ y}
  have hne : A.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually (isOpen_Ioi.mem_nhds hu.2)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow A := by
    obtain ⟨z, hz⟩ := ((tendsto_cdf_atBot μ).eventually (isOpen_Iio.mem_nhds hu.1)).exists
    refine ⟨z, fun y hy => ?_⟩
    change u ≤ cdf μ y at hy
    by_contra! h
    exact (not_le_of_gt hz) (hy.trans ((monotone_cdf μ) h.le))
  have hinf : u ≤ cdf μ (sInf A) := by
    apply ge_of_tendsto (((cdf μ).right_continuous (sInf A)).mono Set.Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : sInf A < y := hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy'
    exact hz.trans ((monotone_cdf μ) hzy.le)
  rw [GeneralQuantile, ite_eq_left hu]
  exact ⟨fun h => hinf.trans ((monotone_cdf μ) h), fun h => csInf_le hb h⟩

/-- The extended quantile is a measurable real random variable. -/
theorem generalQuantile_measurable (μ : Measure ℝ) : Measurable (GeneralQuantile μ) := by
  apply measurable_of_Iic
  intro x
  have hin (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) := generalQuantile_le_iff μ hu x
  by_cases hx : 0 ≤ x
  · have he : GeneralQuantile μ ⁻¹' Iic x =
        (Ioo 0 1 ∩ Iic (cdf μ x)) ∪ (Ioo 0 1)ᶜ := by
      ext u
      by_cases h : u ∈ Ioo (0 : ℝ) 1
      · simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, h, true_and, mem_compl_iff,
          not_true_eq_false, or_false, hin u h]
      · simp [GeneralQuantile, h, hx]
    rw [he]
    exact (measurableSet_Ioo.inter measurableSet_Iic).union measurableSet_Ioo.compl
  · have he : GeneralQuantile μ ⁻¹' Iic x = Ioo 0 1 ∩ Iic (cdf μ x) := by
      ext u
      by_cases h : u ∈ Ioo (0 : ℝ) 1
      · simp only [mem_preimage, mem_Iic, mem_inter_iff, h, true_and, hin u h]
      · simp [GeneralQuantile, h, hx]
    rw [he]
    exact measurableSet_Ioo.inter measurableSet_Iic

/-- **Footnote 15:** the generalized inverse pushes uniform probability to an arbitrary real law. -/
theorem generalQuantile_uniform_law (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (GeneralQuantile μ) = μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ioo]⟩
  have : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map (GeneralQuantile μ)) :=
    (Measure.isProbabilityMeasure_map_iff (generalQuantile_measurable μ).aemeasurable).mpr
      inferInstance
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (generalQuantile_measurable μ) measurableSet_Iic,
    Measure.restrict_apply ((generalQuantile_measurable μ) measurableSet_Iic), ← ofReal_cdf]
  have he : (GeneralQuantile μ ⁻¹' Iic x) ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext u
    by_cases h : u ∈ Ioo (0 : ℝ) 1
    · simp only [mem_inter_iff, mem_preimage, mem_Iic, h, and_true, true_and,
        generalQuantile_le_iff μ h]
    · simp [h]
  rw [he]
  rcases (cdf_le_one μ x).eq_or_lt with h | h
  · rw [h, inter_eq_left.mpr (fun _ hu => hu.2.le), Real.volume_Ioo]
    norm_num
  · have ht : Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) = Ioc 0 (cdf μ x) := by
      ext t
      exact ⟨fun ht => ⟨ht.1.1, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.trans_lt h⟩, ht.2⟩⟩
    rw [ht, Real.volume_Ioc, sub_zero]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Full coverage with an imperfect fair policy

Kreps I, Problem 6.9, pp. 143–144. Starting wealth is one. No loss occurs with
probability one half. Conditional on loss, the loss is either one or three,
equally likely. Coverage pays their mean, two, and costs one. Full insurance
therefore leaves wealth at zero, one or minus one. A necessary and sufficient
marginal-utility test in this example gives both answers within increasing,
strictly concave differentiable utility.
-/

namespace Kreps.UtilityForMoney

/-- The three loss amounts with the probabilities in the example. -/
noncomputable def ImperfectLoss : SimpleLottery ℝ :=
  LotteryTheory.Mix ⟨1 / 2, by norm_num⟩ (LotteryTheory.PureLottery 0)
    (BinaryLottery 1 3 (1 / 2) (by norm_num))

/-- The expected conditional loss is two, yielding an actuarially fair premium of one. -/
theorem imperfect_policy_fair :
    ExpectedUtility id (BinaryLottery 1 3 (1 / 2) (by norm_num)) = 2 ∧
      (1 / 2 : ℝ) * 2 = 1 := by rw [expectedUtility_binary]; norm_num

/-- Expected utility under coverage `a` for this imperfect but fairly priced indemnity. -/
noncomputable def ImperfectValue (V : ℝ → ℝ) (a : ℝ) : ℝ :=
  (2 * V (1 - a) + V a + V (a - 2)) / 4

/-- The displayed objective is the expected utility of final wealth under the actual loss law. -/
theorem imperfectValue_expectedUtility (V : ℝ → ℝ) (a : ℝ) :
    ExpectedUtility (fun t => V (1 - t + (if t = 0 then 0 else 2 * a) - a)) ImperfectLoss =
      ImperfectValue V a := by
  let g := fun t : ℝ => V (1 - t + (if t = 0 then 0 else 2 * a) - a)
  change LotteryTheory.ExpectedUtility g _ = _
  rw [ImperfectLoss, LotteryTheory.expectedUtility_affine, LotteryTheory.expectedUtility_pure]
  change _ + _ * ExpectedUtility g (BinaryLottery ..) = _
  rw [expectedUtility_binary]
  norm_num [g, ImperfectValue]
  ring_nf

/-- At full coverage only the three marginal utilities at residual wealth enter the derivative. -/
theorem imperfectValue_hasDerivAt (V : ℝ → ℝ) (hd : Differentiable ℝ V) :
    HasDerivAt (ImperfectValue V) ((-2 * deriv V 0 + deriv V 1 + deriv V (-1)) / 4) 1 := by
  have h₀ := (hasDerivAt_id' (1 : ℝ)).const_sub 1
  have h₂ := (hasDerivAt_id' (1 : ℝ)).sub_const 2
  have hd₀ : HasDerivAt V (deriv V 0) (1 - 1) := by simpa using (hd 0).hasDerivAt
  have hd₂ : HasDerivAt V (deriv V (-1)) (1 - 2) := by
    convert (hd (-1)).hasDerivAt using 1
    norm_num
  convert ((((hd₀.comp 1 h₀).const_mul 2).add (hd 1).hasDerivAt).add (hd₂.comp 1 h₂)).div_const 4
    using 1
  · rfl
  · ring

/-- A global concave differentiable function lies below each of its tangent lines. -/
theorem wealth_concave_tangent {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hd : Differentiable ℝ V) (x z : ℝ) : V z - V x ≤ deriv V x * (z - x) := by
  rcases lt_trichotomy x z with hh | rfl | hh
  · have he := hc.slope_le_deriv (Set.mem_univ _) (Set.mem_univ _) hh (hd x)
    rw [slope_def_field] at he
    exact (div_le_iff₀ (sub_pos.mpr hh)).mp he
  · simp
  · have he := hc.deriv_le_slope (Set.mem_univ _) (Set.mem_univ _) hh (hd x)
    rw [slope_def_field] at he
    linarith only [(le_div_iff₀ (sub_pos.mpr hh)).mp he]

/-- Full coverage in this imperfect policy is optimal exactly at the marginal-utility equality. -/
theorem imperfect_full_iff {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hd : Differentiable ℝ V) :
    (∀ a, ImperfectValue V a ≤ ImperfectValue V 1) ↔
      deriv V 1 + deriv V (-1) = 2 * deriv V 0 := by
  constructor
  · intro hm
    have hmax : IsLocalMax (ImperfectValue V) (1 : ℝ) := Filter.Eventually.of_forall hm
    have he := hmax.hasDerivAt_eq_zero (imperfectValue_hasDerivAt V hd)
    linarith
  · intro he a
    obtain h₀ := wealth_concave_tangent hc hd 0 (1 - a)
    obtain h₁ := wealth_concave_tangent hc hd 1 a
    obtain h₂ := wealth_concave_tangent hc hd (-1) (a - 2)
    unfold ImperfectValue
    norm_num
    nlinarith only [h₀, h₁, h₂, he, congrArg (fun q : ℝ => q * a) he]

/-- Smooth utility whose marginal utilities at opposite wealth levels sum to one. -/
noncomputable def BalancedMarginalUtility (x : ℝ) : ℝ := x - Real.log (1 + Real.exp x)

/-- The exact marginal utility, strictly positive and strictly decreasing. -/
theorem balancedMarginal_derivative (x : ℝ) :
    HasDerivAt BalancedMarginalUtility (1 / (1 + Real.exp x)) x := by
  have h := (hasDerivAt_id' x).sub (((Real.hasDerivAt_exp x).const_add 1).log (by positivity))
  convert h using 1
  · rfl
  · field_simp
    ring

/-- This balanced marginal example is strictly increasing and strictly concave on all wealth. -/
theorem balancedMarginal_regular :
    StrictMono BalancedMarginalUtility ∧ StrictConcaveOn ℝ Set.univ BalancedMarginalUtility ∧
      Differentiable ℝ BalancedMarginalUtility := by
  have hd : Differentiable ℝ BalancedMarginalUtility := fun x =>
    (balancedMarginal_derivative x).differentiableAt
  refine ⟨strictMono_of_deriv_pos (fun x => by
    rw [(balancedMarginal_derivative x).deriv]
    positivity),
    StrictAnti.strictConcaveOn_univ_of_deriv hd.continuous ?_, hd⟩
  intro x y hxy
  rw [(balancedMarginal_derivative x).deriv, (balancedMarginal_derivative y).deriv]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith [Real.exp_lt_exp.mpr hxy])

/-- **Problem 6.9:** a genuinely imperfect fair policy can make full coverage optimal. -/
theorem problem_6_9_full : ∀ a, ImperfectValue BalancedMarginalUtility a ≤
    ImperfectValue BalancedMarginalUtility 1 := by
  apply (imperfect_full_iff balancedMarginal_regular.2.1.concaveOn balancedMarginal_regular.2.2).mpr
  rw [(balancedMarginal_derivative 1).deriv, (balancedMarginal_derivative (-1)).deriv,
    (balancedMarginal_derivative 0).deriv, Real.exp_neg, Real.exp_zero]
  field_simp
  ring

/-- **Problem 6.9:** the same imperfect fair policy does not make full coverage optimal for CARA. -/
theorem problem_6_9_not_full :
    ¬∀ a, ImperfectValue (ExponentialUtility 1) a ≤ ImperfectValue (ExponentialUtility 1) 1 := by
  intro hm
  have he := (imperfect_full_iff (exponentialUtility_strictConcave zero_lt_one).concaveOn
    (fun x => (exponentialUtility_hasDerivAt 1 x).differentiableAt)).mp hm
  rw [(exponentialUtility_hasDerivAt 1 1).deriv, (exponentialUtility_hasDerivAt 1 (-1)).deriv,
    (exponentialUtility_hasDerivAt 1 0).deriv] at he
  norm_num at he
  linarith [Real.exp_one_gt_two, Real.exp_pos (-1)]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Marginal insurance incentives and the unrestricted coverage domain

Kreps I, equation (6.2) and footnotes 13–14, pp. 139–140. The first-order
equation is equivalent to optimality on the entire real line. At a fair premium
a risk-neutral consumer is indifferent across all coverage levels. If the
premium covers or exceeds the loss and the no-loss event has positive probability,
reducing one's position strictly improves expected utility.
-/

namespace Kreps.UtilityForMoney

/-- Concavity survives evaluation at affine wealth and averaging across the two loss states. -/
theorem insuranceUtility_concave {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d : ℝ) :
    ConcaveOn ℝ Set.univ (InsuranceUtility V p y z d) := by
  have hlin (s t : ℝ) : ConcaveOn ℝ Set.univ (fun a : ℝ => V (s + a*t)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ w _ a b ha hb hab
    have h := hc.2 (Set.mem_univ (s+x*t)) (Set.mem_univ (s+w*t)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    convert h using 2
    linear_combination -s * hab
  have h := (ConcaveOn.smul hp.1 (hlin y (-d))).add
    (ConcaveOn.smul (sub_nonneg.mpr hp.2) (hlin z (y-z-d)))
  convert h using 1
  funext a
  change p * V (y-a*d) + (1-p) * V (z+a*(y-z)-a*d) =
    p * V (y+a*(-d)) + (1-p) * V (z+a*(y-z-d))
  rw [show y-a*d = y+a*(-d) by ring, show z+a*(y-z)-a*d = z+a*(y-z-d) by ring]

/-- The derivative is marginal insurance benefit less marginal premium cost. -/
theorem insuranceUtility_hasDerivAt {V : ℝ → ℝ} (hd : Differentiable ℝ V) (p y z d a : ℝ) :
    HasDerivAt (InsuranceUtility V p y z d)
      ((1-p) * (y-z-d) * deriv V (z+a*(y-z)-a*d) - p*d*deriv V (y-a*d)) a := by
  have h₁ := ((hasDerivAt_id' a).mul_const d).const_sub y
  have h₂ := (((hasDerivAt_id' a).mul_const (y-z)).const_add z).sub
    ((hasDerivAt_id' a).mul_const d)
  convert (((hd _).hasDerivAt.comp a h₁).const_mul p).add
    (((hd _).hasDerivAt.comp a h₂).const_mul (1-p)) using 1
  · rfl
  · dsimp
    ring

/-- Equation (6.2) is necessary and sufficient for global optimality. -/
theorem insurance_optimal_iff_marginals {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hd : Differentiable ℝ V) {p : ℝ} (hp : p ∈ Set.Icc 0 1) (y z d a : ℝ) :
    (∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a) ↔
      p * d * deriv V (y-a*d) = (1-p) * (y-z-d) * deriv V (z+a*(y-z)-a*d) := by
  have hv := insuranceUtility_hasDerivAt hd p y z d a
  constructor
  · intro hm
    have hloc : IsLocalMax (InsuranceUtility V p y z d) a := Filter.Eventually.of_forall hm
    exact (sub_eq_zero.mp (hloc.hasDerivAt_eq_zero hv)).symm
  · intro he b
    rw [he, sub_self] at hv
    have hconc := insuranceUtility_concave hc hp y z d
    rcases lt_trichotomy a b with h | rfl | h
    · have hh := hconc.slope_le_of_hasDerivAt (Set.mem_univ a) (Set.mem_univ b) h hv
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h), zero_mul] at hh
      linarith
    · exact le_rfl
    · have hh := hconc.le_slope_of_hasDerivAt (Set.mem_univ b) (Set.mem_univ a) h hv
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h), zero_mul] at hh
      linarith

/-- Footnote 13. Fair insurance leaves a risk-neutral consumer indifferent over all positions. -/
theorem fair_affine_insurance (A B p y z a b : ℝ) :
    InsuranceUtility (fun x => A*x+B) p y z ((1-p)*(y-z)) a =
      InsuranceUtility (fun x => A*x+B) p y z ((1-p)*(y-z)) b := by
  unfold InsuranceUtility
  ring

/-- Footnote 14. A sufficiently costly contract admits no maximizer with unrestricted positions. -/
theorem expensive_insurance_no_maximum {V : ℝ → ℝ} (hi : StrictMono V) {p y z d : ℝ}
    (hp : p ∈ Set.Ioc 0 1) (hy : z < y) (hd : y - z ≤ d) :
    ¬∃ a, ∀ b, InsuranceUtility V p y z d b ≤ InsuranceUtility V p y z d a := by
  rintro ⟨a, h⟩
  have h₁ := mul_lt_mul_of_pos_left
    (hi (show y-a*d < y-(a-1)*d by nlinarith)) hp.1
  have h₂ := mul_le_mul_of_nonneg_left (hi.monotone
    (show z+a*(y-z)-a*d ≤ z+(a-1)*(y-z)-(a-1)*d by nlinarith)) (sub_nonneg.mpr hp.2)
  exact (not_lt_of_ge (h (a-1))) (add_lt_add_of_lt_of_le h₁ h₂)

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Integrated distribution functions and downside risk

Kreps I, Proposition 6.14(b) and Problem 6.6(a,c), pp. 132–133 and 141–142.
Integrating the step distribution above a zero-mass cutoff yields its expected
shortfall. The capped-utility characterization then gives the full converse and
the joint law with conditionally nonpositive supplements.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory Set

/-- A zero cumulative mass means that the threshold is strictly below each support prize. -/
theorem cumulative_zero_iff (p : SimpleLottery ℝ) (b : ℝ) :
    Cumulative p b = 0 ↔ ∀ x ∈ p.weights.support, b < x := by
  classical
  constructor
  · intro hz x hx
    by_contra! hle
    have hn (t : ℝ) : 0 ≤ p.weights t * (if t ≤ b then 1 else 0 : ℝ) :=
      mul_nonneg (p.nonneg t) (by split <;> norm_num)
    have h := Finset.single_le_sum (s := p.weights.support)
      (f := fun t => p.weights t * (if t ≤ b then 1 else 0 : ℝ)) (fun t _ => hn t) hx
    change p.weights x * _ ≤ Cumulative p b at h
    simp only [hz, hle, ↓reduceIte, mul_one] at h
    exact (Finsupp.mem_support_iff.mp hx) (le_antisymm h (p.nonneg x))
  · intro hs
    unfold Cumulative ExpectedUtility Finsupp.sum
    apply Finset.sum_eq_zero
    intro x hx
    simp [(hs x hx).not_ge]

/-- The integral of one atom's cumulative step is its mass times its shortfall. -/
theorem atom_cdf_integral (m x b r : ℝ) (hb : b < x) (hr : b ≤ r) :
    (∫ z in b..r, m * (if x ≤ z then 1 else 0 : ℝ)) = m * max (r - x) 0 := by
  have he : (fun z : ℝ => m * (if x ≤ z then 1 else 0 : ℝ)) =
      (Ici x).indicator (fun _ => m) := by
    funext z
    by_cases h : x ≤ z <;> simp [indicator, h]
  have hi : Ioc b r ∩ Ici x = Icc x r := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hb.trans_le h.1, h.2⟩, h.1⟩⟩
  rw [he, intervalIntegral.integral_of_le hr, setIntegral_indicator measurableSet_Ici, hi,
    setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_comm]

/-- An integrated cumulative distribution equals the support sum of shortfalls. -/
theorem integrated_cumulative_eq_shortfall (p : SimpleLottery ℝ) {b r : ℝ}
    (hb : Cumulative p b = 0) (hr : b ≤ r) :
    (∫ z in b..r, Cumulative p z) = ExpectedShortfall p r := by
  classical
  unfold Cumulative ExpectedShortfall ExpectedUtility Finsupp.sum
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun x hx =>
      atom_cdf_integral _ _ _ _ ((cumulative_zero_iff p b).mp hb x hx) hr
  · intro x _
    change IntervalIntegrable (fun z : ℝ => p.weights x * (if x ≤ z then 1 else 0 : ℝ))
      volume b r
    have hi : IntervalIntegrable ((Ici x).indicator (fun _ : ℝ => p.weights x)) volume b r :=
      intervalIntegrable_iff.mpr (intervalIntegrable_const.def'.indicator measurableSet_Ici)
    convert hi using 1
    funext z
    by_cases h : x ≤ z <;> simp [indicator, h]

/-- All shortfalls are zero below any common lower support bound. -/
theorem expectedShortfall_zero_of_le {p : SimpleLottery ℝ} {b r : ℝ}
    (hb : Cumulative p b = 0) (hr : r ≤ b) : ExpectedShortfall p r = 0 := by
  unfold ExpectedShortfall ExpectedUtility Finsupp.sum
  apply Finset.sum_eq_zero
  intro x hx
  have h := hr.trans ((cumulative_zero_iff p b).mp hb x hx).le
  simp [sub_nonpos.mpr h]

/-- Proposition 6.14(b). Weak integrated-CDF comparisons characterize second-order dominance. -/
theorem proposition_6_14b (p q : SimpleLottery ℝ) (b : ℝ)
    (hp : Cumulative p b = 0) (hq : Cumulative q b = 0) :
    SecondOrderDominates p q ↔ ∀ r, b ≤ r →
      (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z := by
  rw [secondOrder_iff_shortfalls]
  constructor
  · intro h r hr
    simpa only [integrated_cumulative_eq_shortfall p hp hr,
      integrated_cumulative_eq_shortfall q hq hr] using h r
  · intro h r
    rcases le_or_gt r b with hle | hgt
    · rw [expectedShortfall_zero_of_le hp hle, expectedShortfall_zero_of_le hq hle]
    · simpa only [integrated_cumulative_eq_shortfall p hp hgt.le,
        integrated_cumulative_eq_shortfall q hq hgt.le] using h r hgt.le

/-- Problem 6.6(a). The integrated comparison holds above any strict lower support bound. -/
theorem problem_6_6a {p q : SimpleLottery ℝ} (h : SecondOrderDominates p q) (b : ℝ)
    (hp : ∀ x ∈ p.weights.support, b < x) (hq : ∀ x ∈ q.weights.support, b < x) :
    ∀ r, b < r → (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z :=
  fun r hr => (proposition_6_14b p q b ((cumulative_zero_iff p b).mpr hp)
    ((cumulative_zero_iff q b).mpr hq)).mp h r hr.le

/-- Problem 6.6(c). The stated integrated-CDF comparisons produce the required joint variables. -/
theorem problem_6_6c {p q : SimpleLottery ℝ} (b : ℝ)
    (hp : ∀ x ∈ p.weights.support, b < x) (hq : ∀ x ∈ q.weights.support, b < x)
    (h : ∀ r, b ≤ r → (∫ z in b..r, Cumulative p z) ≤ ∫ z in b..r, Cumulative q z) :
    ∃ C : FiniteCoupling p q, ∀ i, C.conditionalDrift i ≤ 0 := by
  obtain ⟨C, hc⟩ := supermartingaleCoupling_of_dominance
    ((proposition_6_14b p q b ((cumulative_zero_iff p b).mpr hp)
      ((cumulative_zero_iff q b).mpr hq)).mpr h)
  exact ⟨C, C.nonpositiveDrift_iff.mp hc⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Arrow–Pratt comparison with derivatives within the prize interval

Kreps I, Proposition 6.8, p. 129. Every hypothesis below concerns values and
derivatives within the monetary domain. At an included endpoint the relative
derivatives are one-sided. No smooth extension outside the interval is needed.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Absolute curvature using first and second derivatives within the prize interval. -/
noncomputable def IntervalRiskAversion (S : Set ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(derivWithin (derivWithin U S) S x) / derivWithin U S x

/-- The relative coefficient agrees with ordinary wealth risk at every interior point. -/
theorem intervalRiskAversion_eq_of_interior {S : Set ℝ} (U : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ interior S) : IntervalRiskAversion S U x = AbsoluteRiskAversion U x := by
  have he : derivWithin U S =ᶠ[𝓝 x] deriv U := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  rw [IntervalRiskAversion, AbsoluteRiskAversion,
    derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx), he.deriv_eq, he.self_of_nhds]

/-- Relative smoothness makes the coefficient continuous all the way to included endpoints. -/
theorem intervalRiskAversion_continuousOn {S : Set ℝ} (hS : UniqueDiffOn ℝ S) {U : ℝ → ℝ}
    (hU : ContDiffOn ℝ 2 U S) (hp : ∀ x ∈ S, 0 < derivWithin U S x) :
    ContinuousOn (IntervalRiskAversion S U) S := by
  have hd := hU.derivWithin hS (m := 1) (by norm_num)
  exact (hd.continuousOn_derivWithin hS (by norm_num)).neg.div
    (hU.continuousOn_derivWithin hS (by norm_num)) fun x hx => (hp x hx).ne'

/-- Supporting-line comparison from continuous utility and ordered marginal ratios within the
monetary interval. Derivatives are used only inside each nondegenerate secant segment. -/
theorem interval_marginal_support {S : Set ℝ} (hS : Convex ℝ S) {W V DW DV : ℝ → ℝ}
    (hcW : ContinuousOn W S) (hcV : ContinuousOn V S)
    (hdW : ∀ x ∈ interior S, HasDerivAt W (DW x) x)
    (hdV : ∀ x ∈ interior S, HasDerivAt V (DV x) x)
    (hVi : StrictMonoOn V S) (hpV : ∀ x ∈ S, 0 < DV x)
    (hR : AntitoneOn (fun x => DW x / DV x) S) {x z : ℝ} (hx : x ∈ S) (hz : z ∈ S) :
    W z ≤ W x + (DW x / DV x) * (V z - V x) := by
  have key {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      ∃ c ∈ Set.Ioo a b, c ∈ S ∧ W b - W a = (V b - V a) * (DW c / DV c) := by
    have hs := hS.ordConnected.out ha hb
    have ho : Set.Ioo a b ⊆ interior S := isOpen_Ioo.subset_interior_iff.mpr
      (Set.Ioo_subset_Icc_self.trans hs)
    obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope W DW hab (hcW.mono hs)
      (fun t ht => hdW t (ho ht)) V DV (hcV.mono hs) (fun t ht => hdV t (ho ht))
    have hcS := interior_subset (ho hc)
    refine ⟨c, hc, hcS, ?_⟩
    field_simp [(hpV c hcS).ne']
    linarith
  rcases lt_trichotomy x z with h | rfl | h
  · obtain ⟨c, hc, hcs, he⟩ := key hx hz h
    have hh := mul_le_mul_of_nonneg_left (hR hx hcs hc.1.le) (sub_nonneg.mpr (hVi hx hz h).le)
    change (V z - V x) * (DW c / DV c) ≤ (V z - V x) * (DW x / DV x) at hh
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs, he⟩ := key hz hx h
    have hh := mul_le_mul_of_nonneg_left (hR hcs hx hc.2.le) (sub_nonneg.mpr (hVi hz hx h).le)
    change (V x - V z) * (DW x / DV x) ≤ (V x - V z) * (DW c / DV c) at hh
    nlinarith

/-- **Proposition 6.8 on the original interval:** the coefficient inequality at every prize
characterizes the comparison of all simple lotteries, under purely relative smoothness. -/
theorem proposition_6_8_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {W V : ℝ → ℝ} (hW : ContDiffOn ℝ 2 W S) (hV : ContDiffOn ℝ 2 V S)
    (hVi : StrictMonoOn V S) (hpW : ∀ x ∈ S, 0 < derivWithin W S x)
    (hpV : ∀ x ∈ S, 0 < derivWithin V S x) :
    MoreRiskAverse S W V ↔ ∀ x ∈ S, IntervalRiskAversion S V x ≤ IntervalRiskAversion S W x := by
  have hD := uniqueDiffOn_convex hS hI
  have dW := hW.derivWithin hD (m := 1) (by norm_num)
  have dV := hV.derivWithin hD (m := 1) (by norm_num)
  constructor
  · intro h x hx
    have hxcl : x ∈ closure (interior S) := by
      rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
      exact subset_closure hx
    have := mem_closure_iff_nhdsWithin_neBot.mp hxcl
    apply le_of_tendsto_of_tendsto
      ((intervalRiskAversion_continuousOn hD hV hpV x hx).mono interior_subset)
      ((intervalRiskAversion_continuousOn hD hW hpW x hx).mono interior_subset)
    filter_upwards [self_mem_nhdsWithin (a := x) (s := interior S)] with y hy
    have hn := mem_interior_iff_mem_nhds.mp hy
    have hym := interior_subset hy
    rw [intervalRiskAversion_eq_of_interior V hy, intervalRiskAversion_eq_of_interior W hy]
    apply arrowPratt_le_of_moreRiskAverse_interior hy hVi h
      ((hW y hym).contDiffAt hn) ((hV y hym).contDiffAt hn)
    · simpa only [← derivWithin_of_mem_nhds (f := W) hn] using hpW y hym
    · simpa only [← derivWithin_of_mem_nhds (f := V) hn] using hpV y hym
  · intro h
    let R := fun x => derivWithin W S x / derivWithin V S x
    have ha : AntitoneOn R S := by
      have hd (x : ℝ) (hx : x ∈ S) := ((dW.differentiableOn_one x hx).hasDerivWithinAt.div
        (dV.differentiableOn_one x hx).hasDerivWithinAt (hpV x hx).ne')
      apply antitoneOn_of_hasDerivWithinAt_nonpos hS
        (dW.continuousOn.div dV.continuousOn (fun x hx => (hpV x hx).ne'))
        (fun x hx => (hd x (interior_subset hx)).mono interior_subset)
      intro x hx
      have hxs := interior_subset hx
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have he := (div_le_div_iff₀ (hpV x hxs) (hpW x hxs)).mp (h x hxs)
      nlinarith
    intro p x hx
    have hpt (z : S) : W z ≤ R x * V z + (W x - R x * V x) := by
      have hh := interval_marginal_support hS hW.continuousOn hV.continuousOn
        (fun y hy => ((hW.differentiableOn (by norm_num) y (interior_subset hy)).hasDerivWithinAt
          |>.hasDerivAt (mem_interior_iff_mem_nhds.mp hy)))
        (fun y hy => ((hV.differentiableOn (by norm_num) y (interior_subset hy)).hasDerivWithinAt
          |>.hasDerivAt (mem_interior_iff_mem_nhds.mp hy)))
        hVi hpV ha x.property z.property
      dsimp [R]
      linarith
    have he : ExpectedUtility (fun z : S => W z) p ≤
        ExpectedUtility (fun z : S => R x * V z + (W x - R x * V x)) p :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (p.nonneg z)
    rw [expectedUtility_affine_payoff] at he
    by_contra! hn
    have hpos : 0 < R x := div_pos (hpW x x.property) (hpV x x.property)
    nlinarith [mul_lt_mul_of_pos_left hn hpos]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Wealth comparisons at one-sided endpoints

Kreps I, Proposition 6.12, pp. 130–131. The relative derivative formulation
uses a separate feasible domain for each pair of shifted lotteries. When the
overlap has only one prize, every pair of certainty equivalents there agrees.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Translating the utility and restricting to any admissible nondegenerate overlap preserves
its first within-domain derivative at the translated wealth. -/
theorem derivWithin_wealth_shift {D S : Set ℝ} (hD : UniqueDiffOn ℝ D) (u : ℝ)
    (hm : Set.MapsTo (fun x : ℝ => x + u) D S) {U : ℝ → ℝ} (hd : DifferentiableOn ℝ U S)
    {x : ℝ} (hx : x ∈ D) :
    derivWithin (fun t => U (t + u)) D x = derivWithin U S (x + u) := by
  have h := ((hd (x + u) (hm hx)).hasDerivWithinAt.comp x
    ((hasDerivAt_id' x).add_const u).hasDerivWithinAt hm).derivWithin (hD x hx)
  simpa only [mul_one, Function.comp_def] using h

/-- The coefficient computed within a translated overlap is the coefficient in the original
interval, including all included endpoints. -/
theorem intervalRiskAversion_shift {D S : Set ℝ} (hD : UniqueDiffOn ℝ D)
    (hS : UniqueDiffOn ℝ S) (u : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + u) D S)
    {U : ℝ → ℝ} (hs : ContDiffOn ℝ 2 U S) {x : ℝ} (hx : x ∈ D) :
    IntervalRiskAversion D (fun t => U (t + u)) x = IntervalRiskAversion S U (x + u) := by
  have he : D.EqOn (derivWithin (fun t => U (t + u)) D) (fun t => derivWithin U S (t + u)) :=
    fun _ ht => derivWithin_wealth_shift hD u hm (hs.differentiableOn (by norm_num)) ht
  rw [IntervalRiskAversion, IntervalRiskAversion, derivWithin_congr he (he hx), he hx,
    derivWithin_wealth_shift hD u hm
      ((hs.derivWithin hS (m := 1) (by norm_num)).differentiableOn_one) hx]

/-- On an overlap with more than one prize, the premium comparison tests the original
within-domain coefficients at every shifted wealth. -/
theorem shiftPremiumOrder_iff_within_coefficients {S : Set ℝ} (hS : Convex ℝ S)
    (hI : (interior S).Nonempty) {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) (u v : ℝ) (hO : (interior (ShiftDomain S u v)).Nonempty) :
    ShiftPremiumOrder S U u v ↔ ∀ x ∈ ShiftDomain S u v,
      IntervalRiskAversion S U (x + v) ≤ IntervalRiskAversion S U (x + u) := by
  let D := ShiftDomain S u v
  have hcD : Convex ℝ D := shiftDomain_convex hS u v
  have hD := uniqueDiffOn_convex hcD hO
  have hSD := uniqueDiffOn_convex hS hI
  have hu : Set.MapsTo (fun x : ℝ => x + u) D S := fun _ hx => hx.1
  have hv : Set.MapsTo (fun x : ℝ => x + v) D S := fun _ hx => hx.2
  have hsm (t : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + t) D S) :
      ContDiffOn ℝ 2 (fun x => U (x + t)) D :=
    hU.comp ((contDiff_id.add contDiff_const).contDiffOn) hm
  have hpos (t : ℝ) (hm : Set.MapsTo (fun x : ℝ => x + t) D S) (x : ℝ) (hx : x ∈ D) :
      0 < derivWithin (fun y => U (y + t)) D x := by
    rw [derivWithin_wealth_shift hD t hm (hU.differentiableOn (by norm_num)) hx]
    exact hp _ (hm hx)
  rw [shiftPremiumOrder_iff hS hi hU.continuousOn, proposition_6_8_within hcD hO
    (hsm u hu) (hsm v hv) (fun _ hx _ hy h => hi (hv hx) (hv hy) (by linarith))
    (hpos u hu) (hpos v hv)]
  exact forall_congr' fun x => forall_congr' fun hx => by
    rw [intervalRiskAversion_shift hD hSD v hv hU hx, intervalRiskAversion_shift hD hSD u hu hU hx]

/-- Even with an empty or single-prize overlap, ordering the feasible coefficients orders premia. -/
theorem shiftPremiumOrder_of_within_coefficients {S : Set ℝ} (hS : Convex ℝ S)
    (hI : (interior S).Nonempty) {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) (u v : ℝ)
    (h : ∀ x ∈ ShiftDomain S u v, IntervalRiskAversion S U (x + v) ≤
      IntervalRiskAversion S U (x + u)) : ShiftPremiumOrder S U u v := by
  by_cases ho : (interior (ShiftDomain S u v)).Nonempty
  · exact (shiftPremiumOrder_iff_within_coefficients hS hI hi hU hp u v ho).mpr h
  · have hs := Set.not_nontrivial_iff.mp
        (ho ∘ (shiftDomain_convex hS u v).nontrivial_iff_nonempty_interior.mp)
    intro p x y _ _
    have he : x = y := Subtype.ext (hs x.property y.property)
    rw [he]

/-- When both shifted base wealth levels are interior, zero lies inside their common overlap. -/
theorem zero_mem_interior_shiftDomain {S : Set ℝ} {u v : ℝ} (hu : u ∈ interior S)
    (hv : v ∈ interior S) : 0 ∈ interior (ShiftDomain S u v) := by
  have hn (t : ℝ) (ht : t ∈ interior S) : ∀ᶠ e : ℝ in 𝓝 0, e + t ∈ S := by
    have he : Tendsto (fun e : ℝ => e + t) (𝓝 0) (𝓝 t) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add_const t
    exact he (mem_interior_iff_mem_nhds.mp ht)
  exact mem_interior_iff_mem_nhds.mpr ((hn u hu).and (hn v hv))

/-- **Proposition 6.12 on the original interval:** increasing, decreasing and constant
behavior of all premia corresponds to the same behavior of within-interval absolute curvature. -/
theorem proposition_6_12_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hi : StrictMonoOn U S) (hU : ContDiffOn ℝ 2 U S)
    (hp : ∀ x ∈ S, 0 < derivWithin U S x) :
    (NondecreasingRiskAversion S U ↔ MonotoneOn (IntervalRiskAversion S U) S) ∧
    (NonincreasingRiskAversion S U ↔ AntitoneOn (IntervalRiskAversion S U) S) ∧
    (ConstantRiskAversion S U ↔ ∃ k : ℝ, ∀ x ∈ S, IntervalRiskAversion S U x = k) := by
  have hc := intervalRiskAversion_continuousOn (uniqueDiffOn_convex hS hI) hU hp
  have hcompare {u v : ℝ} (hu : u ∈ interior S) (hv : v ∈ interior S)
      (h : ShiftPremiumOrder S U u v) :
      IntervalRiskAversion S U v ≤ IntervalRiskAversion S U u := by
    have hz := zero_mem_interior_shiftDomain hu hv
    simpa only [zero_add] using ((shiftPremiumOrder_iff_within_coefficients hS hI hi hU hp u v
      ⟨0, hz⟩).mp h 0 (interior_subset hz))
  have hinc : NondecreasingRiskAversion S U ↔ MonotoneOn (IntervalRiskAversion S U) S := by
    constructor
    · intro h
      exact monotoneOn_interval_of_interior hS hI hc fun _ hx _ hy hxy => hcompare hy hx (h _ _ hxy)
    · exact fun h u v huv => shiftPremiumOrder_of_within_coefficients hS hI hi hU hp v u
        fun _ hx => h hx.2 hx.1 (by linarith)
  have hdec : NonincreasingRiskAversion S U ↔ AntitoneOn (IntervalRiskAversion S U) S := by
    constructor
    · intro h
      have hm := monotoneOn_interval_of_interior hS hI hc.neg
        (fun _ hx _ hy hxy => neg_le_neg (hcompare hx hy (h _ _ hxy)))
      exact fun _ hx _ hy hxy => neg_le_neg_iff.mp (hm hx hy hxy)
    · exact fun h u v huv => shiftPremiumOrder_of_within_coefficients hS hI hi hU hp u v
        fun _ hx => h hx.1 hx.2 (by linarith)
  refine ⟨hinc, hdec, ?_⟩
  rw [ConstantRiskAversion, hdec, hinc]
  constructor
  · rintro ⟨ha, hm⟩
    obtain ⟨x, hx⟩ := hI
    refine ⟨IntervalRiskAversion S U x, fun y hy => ?_⟩
    rcases le_total x y with h | h
    · exact (ha (interior_subset hx) hy h).antisymm (hm (interior_subset hx) hy h)
    · exact (hm hy (interior_subset hx) h).antisymm (ha hy (interior_subset hx) h)
  · rintro ⟨k, hk⟩
    constructor <;> intro x hx y hy _ <;> rw [hk x hx, hk y hy]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Constant risk aversion on the original monetary interval

Kreps I, Proposition 6.12 and Problem 6.2, pp. 130–131 and 140–141. The
differential equation is integrated in the interior. Continuity determines
the utility at each included endpoint without using its exterior values.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Two continuous functions agreeing inside a nondegenerate interval agree at its endpoints. -/
theorem eqOn_interval_of_eqOn_interior {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {f g : ℝ → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (he : (interior S).EqOn f g) : S.EqOn f g := by
  intro x hx
  have hcl : x ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hI]
    exact subset_closure hx
  have := mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono interior_subset)
    ((hg x hx).mono interior_subset) (Filter.mem_of_superset self_mem_nhdsWithin he)

/-- **Proposition 6.12, relative CARA classification:** constant nonnegative curvature on the
whole interval determines the exponential or affine utility, including its boundary values. -/
theorem cara_representation_within {S : Set ℝ} (hS : Convex ℝ S) (hI : (interior S).Nonempty)
    {U : ℝ → ℝ} (hU : ContDiffOn ℝ 2 U S) (hp : ∀ x ∈ S, 0 < derivWithin U S x)
    (k : ℝ) (hk : ∀ x ∈ S, IntervalRiskAversion S U x = k) :
    (0 < k → ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * ExponentialUtility k x) ∧
      (k = 0 → ∃ A B : ℝ, 0 < B ∧ ∀ x ∈ S, U x = A + B * x) := by
  have hs (x : ℝ) (hx : x ∈ interior S) : ContDiffAt ℝ 2 U x :=
    (hU x (interior_subset hx)).contDiffAt (mem_interior_iff_mem_nhds.mp hx)
  have hd (x : ℝ) (hx : x ∈ interior S) := (hs x hx).differentiableAt (by norm_num)
  have hd' (x : ℝ) (hx : x ∈ interior S) :=
    ((hs x hx).derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hp' (x : ℝ) (hx : x ∈ interior S) : 0 < deriv U x := by
    rw [← derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)]
    exact hp x (interior_subset hx)
  have hk' (x : ℝ) (hx : x ∈ interior S) : AbsoluteRiskAversion U x = k := by
    rw [← intervalRiskAversion_eq_of_interior U hx]
    exact hk x (interior_subset hx)
  constructor
  · intro hpos
    obtain ⟨A, B, hB, he⟩ := proposition_6_12_exponential hS.interior hI hd hd' hp' hpos hk'
    refine ⟨A, B, hB, fun x hx => ?_⟩
    apply eqOn_interval_of_eqOn_interior hS hI hU.continuousOn _ (g := fun z =>
      A + B * ExponentialUtility k z) (fun _ hz => he _ hz) hx
    unfold ExponentialUtility
    fun_prop
  · rintro rfl
    obtain ⟨A, B, hB, he⟩ := proposition_6_12_affine hS.interior hI hd hd' hp' hk'
    refine ⟨A, B, hB, fun x hx => ?_⟩
    apply eqOn_interval_of_eqOn_interior hS hI hU.continuousOn _ (g := fun z =>
      A + B * z) (fun _ hz => he _ hz) hx
    fun_prop

/-- **Problem 6.2 on the exact prize interval:** one-sided endpoint smoothness suffices for
the personality and calibrated certainty equivalent to imply the complete ranking. -/
theorem problem_6_2_within {U : ℝ → ℝ} (hi : StrictMonoOn U CalibrationInterval)
    (hc : ConcaveOn ℝ CalibrationInterval U) (hs : ContDiffOn ℝ 2 U CalibrationInterval)
    (hp : ∀ x ∈ CalibrationInterval, 0 < derivWithin U CalibrationInterval x)
    (hC : ConstantRiskAversion CalibrationInterval U)
    (he : (U 5000 + U 0) / 2 = U 2400) : CalibratedChoicesRanked U := by
  have hz : (0 : ℝ) ∈ interior CalibrationInterval := by simp [CalibrationInterval]
  have hI := Set.nonempty_of_mem hz
  obtain ⟨k, hk⟩ := (proposition_6_12_within hc.1 hI hi hs hp).2.2.mp hC
  have hneg := (hc.antitoneOn_derivWithin (hs.differentiableOn (by norm_num))).derivWithin_nonpos
    (x := 0)
  have hnn : 0 ≤ IntervalRiskAversion CalibrationInterval U 0 :=
    div_nonneg (neg_nonneg.mpr hneg) (hp 0 (interior_subset hz)).le
  rw [hk 0 (interior_subset hz)] at hnn
  have hrep := cara_representation_within hc.1 hI hs hp k hk
  rcases hnn.eq_or_lt with hz' | hpos
  · obtain ⟨A, B, hB, h⟩ := hrep.2 hz'.symm
    rw [h 5000 (by norm_num [CalibrationInterval]), h 0 (by norm_num [CalibrationInterval]),
      h 2400 (by norm_num [CalibrationInterval])] at he
    linarith
  · obtain ⟨A, B, hB, h⟩ := hrep.1 hpos
    exact problem_6_2 hB hpos h he

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Derivatives on the inverse utility scale

Kreps I, p. 129. The inverse used in the comparison theorem is the actual inverse
of utility on the common prize interval. Near an interior wealth with nonzero
marginal utility, it agrees with the smooth inverse supplied by the inverse
function theorem.
-/

namespace Kreps.UtilityForMoney

open Filter Topology
open scoped ContDiff

/-- The interval inverse has the same smoothness as the utility and the reciprocal derivative
at every interior wealth where marginal utility is nonzero. -/
theorem inverse_utility_regularity {S : Set ℝ} {V : ℝ → ℝ} {x : ℝ} {n : ℕ∞ω}
    (hx : x ∈ interior S) (hi : Set.InjOn V S) (hs : ContDiffAt ℝ n V x) (hn : n ≠ 0)
    (hp : deriv V x ≠ 0) :
    ContDiffAt ℝ n (Function.invFunOn V S) (V x) ∧
      HasDerivAt (Function.invFunOn V S) (deriv V x)⁻¹ (V x) ∧
      (∀ᶠ t in 𝓝 (V x), V (Function.invFunOn V S t) = t) := by
  have hd := hs.hasStrictDerivAt hn
  let g := hd.localInverse V (deriv V x) x hp
  have hge : g (V x) = x := (hd.eventually_left_inverse hp).self_of_nhds
  have hgd : HasDerivAt g (deriv V x)⁻¹ (V x) := (hd.to_localInverse hp).hasDerivAt
  have hgs : ContDiffAt ℝ n g (V x) := hs.to_localInverse (hd.hasDerivAt.hasFDerivAt_equiv hp) hn
  have hg : Tendsto g (𝓝 (V x)) (𝓝 x) := by
    simpa only [hge] using hgd.continuousAt.tendsto
  have hright : ∀ᶠ t in 𝓝 (V x), V (g t) = t := hd.eventually_right_inverse hp
  have he : Function.invFunOn V S =ᶠ[𝓝 (V x)] g := by
    filter_upwards [hg (mem_interior_iff_mem_nhds.mp hx), hright] with t hmem ht
    calc Function.invFunOn V S t = Function.invFunOn V S (V (g t)) := congrArg _ ht.symm
         _ = g t := hi.leftInvOn_invFunOn hmem
  refine ⟨hgs.congr_of_eventuallyEq he, hgd.congr_of_eventuallyEq he, ?_⟩
  filter_upwards [he, hright] with t h₁ h₂
  simpa only [h₁] using h₂

/-- The derivative of the utility transform at an attained interior value is a marginal ratio. -/
theorem utilityTransform_hasDerivAt {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ} (hx : x ∈ interior S)
    (hi : Set.InjOn V S) (hV : ContDiffAt ℝ 1 V x) (hp : deriv V x ≠ 0)
    (hW : DifferentiableAt ℝ W x) :
    HasDerivAt (UtilityTransform S W V) (MarginalRatio W V x) (V x) := by
  have hInv := (inverse_utility_regularity hx hi hV one_ne_zero hp).2.1
  have he := hi.leftInvOn_invFunOn (interior_subset hx)
  have hf : HasDerivAt W (deriv W x) (Function.invFunOn V S (V x)) := by
    rw [he]
    exact hW.hasDerivAt
  change HasDerivAt (W ∘ Function.invFunOn V S) (deriv W x / deriv V x) (V x)
  rw [div_eq_mul_inv]
  exact hf.comp (V x) hInv

/-- The displayed formula in the proof of Proposition 6.8, on the interior of the monetary
interval. Twice continuous differentiability is inherited on the inverse utility scale. -/
theorem utilityTransform_second_derivative {S : Set ℝ} {W V : ℝ → ℝ} {x : ℝ} (hx : x ∈ interior S)
    (hi : Set.InjOn V S) (hV : ContDiffAt ℝ 2 V x) (hpV : deriv V x ≠ 0)
    (hW : ContDiffAt ℝ 2 W x) (hpW : deriv W x ≠ 0) :
    ContDiffAt ℝ 2 (UtilityTransform S W V) (V x) ∧
      deriv (deriv (UtilityTransform S W V)) (V x) = deriv W x / (deriv V x) ^ 2 *
        (deriv (deriv W) x / deriv W x - deriv (deriv V) x / deriv V x) := by
  let g := Function.invFunOn V S
  have hxg : g (V x) = x := hi.leftInvOn_invFunOn (interior_subset hx)
  obtain ⟨hgs, hgd, hright⟩ := inverse_utility_regularity hx hi hV (by norm_num) hpV
  have hg : Tendsto g (𝓝 (V x)) (𝓝 x) := by
    have h : Tendsto g (𝓝 (V x)) (𝓝 (g (V x))) := hgd.continuousAt.tendsto
    rwa [hxg] at h
  have hdW := hW.derivWithin (m := 1) (by norm_num)
  have hdV := hV.derivWithin (m := 1) (by norm_num)
  have hev : ∀ᶠ y in 𝓝 x, deriv V y ≠ 0 := hdV.continuousAt.eventually_ne hpV
  have hR := hdW.differentiableAt_one.hasDerivAt.div hdV.differentiableAt_one.hasDerivAt hpV
  have hRg : HasDerivAt (MarginalRatio W V)
      ((deriv (deriv W) x * deriv V x - deriv W x * deriv (deriv V) x) / deriv V x ^ 2)
      (g (V x)) := by rw [hxg]; exact hR
  have hlocal : deriv (UtilityTransform S W V) =ᶠ[𝓝 (V x)] (MarginalRatio W V ∘ g) := by
    filter_upwards [hg (isOpen_interior.mem_nhds hx), hright, hg hev,
      hg (hV.eventually (by norm_num)), hg (hW.eventually (by norm_num))] with y hy hre hpy hVy hWy
    change g y ∈ interior S at hy
    change deriv V (g y) ≠ 0 at hpy
    change ContDiffAt ℝ 2 V (g y) at hVy
    change ContDiffAt ℝ 2 W (g y) at hWy
    have hh := (utilityTransform_hasDerivAt hy hi (hVy.of_le (by norm_num)) hpy
      (hWy.differentiableAt (by norm_num))).deriv
    change V (g y) = y at hre
    rw [hre] at hh
    exact hh
  have hWg : ContDiffAt ℝ 2 W (g (V x)) := by rwa [hxg]
  refine ⟨hWg.comp (V x) hgs, ?_⟩
  rw [hlocal.deriv_eq, (hRg.comp (V x) hgd).deriv]
  field_simp

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk attitudes and finite Jensen induction

Kreps I, pp. 125–127 and Problem 6.1(b). The induction combines one new prize
with the normalized remaining lottery. It permits zero weights. The same binary
tests distinguish risk seeking, risk neutrality and risk aversion on intervals.
-/

namespace Kreps.UtilityForMoney

/-- The center-of-mass form of the induction requested in Problem 6.1(b). -/
theorem jensen_by_support_induction {I : Type*} {S : Set ℝ} {U : ℝ → ℝ} (hc : ConcaveOn ℝ S U)
    (w x : I → ℝ) (T : Finset I) (hn : ∀ i ∈ T, 0 ≤ w i) (hp : 0 < ∑ i ∈ T, w i)
    (hs : ∀ i ∈ T, x i ∈ S) :
    T.centerMass w (fun i => U (x i)) ≤ U (T.centerMass w x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at hp
  | @insert i T hi ih =>
    have hnt (j) (hj : j ∈ T) := hn j (Finset.mem_insert_of_mem hj)
    have hst (j) (hj : j ∈ T) := hs j (Finset.mem_insert_of_mem hj)
    have hni := hn i (Finset.mem_insert_self _ _)
    have hxi := hs i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi] at hp
    have hnT := Finset.sum_nonneg hnt
    rcases hnT.eq_or_lt with ht | ht
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg hnt).mp ht.symm
      have hzero (f : I → ℝ) : ∑ j ∈ T, w j * f j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]
      have hw : w i ≠ 0 := by linarith
      simp only [Finset.centerMass, Finset.sum_insert hi, smul_eq_mul, ht.symm,
        hzero, add_zero, inv_mul_cancel_left₀ hw, le_refl]
    · rw [Finset.centerMass_insert _ _ _ hi ht.ne', Finset.centerMass_insert _ _ _ hi ht.ne']
      let a := w i / (w i + ∑ j ∈ T, w j)
      let b := (∑ j ∈ T, w j) / (w i + ∑ j ∈ T, w j)
      have ha : 0 ≤ a := div_nonneg hni hp.le
      have hb : 0 ≤ b := div_nonneg ht.le hp.le
      have hab : a + b = 1 := by
        dsimp [a, b]
        rw [← add_div, div_self hp.ne']
      have h := hc.2 hxi (hc.1.centerMass_mem hnt ht hst) ha hb hab
      exact (add_le_add_right (mul_le_mul_of_nonneg_left (ih hnt ht hst) hb)
        (a * U (x i))).trans h

/-- Problem 6.1(b). Normalized weights give Jensen's inequality for every finite list. -/
theorem problem_6_1b_induction {I : Type*} {S : Set ℝ} {U : ℝ → ℝ} (hc : ConcaveOn ℝ S U)
    (w x : I → ℝ) (T : Finset I) (hn : ∀ i ∈ T, 0 ≤ w i) (hp : ∑ i ∈ T, w i = 1)
    (hs : ∀ i ∈ T, x i ∈ S) : (∑ i ∈ T, w i * U (x i)) ≤ U (∑ i ∈ T, w i * x i) := by
  simpa only [Finset.centerMass, hp, inv_one, smul_eq_mul, one_mul] using
    jensen_by_support_induction hc w x T hn (hp.symm ▸ zero_lt_one) hs

/-- Risk seeking on an interval is equivalent to convex prize utility there. -/
theorem riskSeeking_iff_convex {S : Set ℝ} (hS : Convex ℝ S) (U : ℝ → ℝ) :
    ConvexOn ℝ S U ↔ ∀ p : SimpleLottery S,
      U (ExpectedUtility Subtype.val p) ≤ ExpectedUtility (fun x : S => U x) p := by
  constructor
  · intro h p
    simpa only [ExpectedUtility, Finsupp.sum, smul_eq_mul] using h.map_sum_le
      (t := p.weights.support) (w := fun x => p.weights x) (p := fun x : S => x.val)
      (fun x _ => p.nonneg x) p.total (fun x _ => x.property)
  · intro h
    refine ⟨hS, ?_⟩
    intro x hx y hy a b ha hb hab
    have hwt : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    simpa only [expectedUtility_binary, smul_eq_mul, show 1 - a = b by linarith] using
      h (BinaryLottery (⟨x, hx⟩ : S) ⟨y, hy⟩ a hwt)

/-- Risk neutrality is equivalently both Jensen inequalities, hence equality on every mixture. -/
theorem riskNeutral_iff_affine_mixes {S : Set ℝ} (hS : Convex ℝ S) (U : ℝ → ℝ) :
    (∀ p : SimpleLottery S,
      ExpectedUtility (fun x : S => U x) p = U (ExpectedUtility Subtype.val p)) ↔
    ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      U (a * x + b * y) = a * U x + b * U y := by
  constructor
  · intro h x hx y hy a b ha hb hab
    have hw : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    simpa only [expectedUtility_binary, show 1 - a = b by linarith] using
      (h (BinaryLottery (⟨x, hx⟩ : S) ⟨y, hy⟩ a hw)).symm
  · intro h
    have hc : ConcaveOn ℝ S U :=
      ⟨hS, fun x hx y hy a b ha hb hab => (h x hx y hy a b ha hb hab).ge⟩
    have hv : ConvexOn ℝ S U :=
      ⟨hS, fun x hx y hy a b ha hb hab => (h x hx y hy a b ha hb hab).le⟩
    exact fun p => le_antisymm ((proposition_6_3 hS U).mp hc p)
      ((riskSeeking_iff_convex hS U).mp hv p)

/-- Figure 6.1. The 60/40 lottery has a certainty equivalent no higher than its mean. -/
theorem figure_6_1 {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ} (hc : ContinuousOn U S)
    (hU : ConcaveOn ℝ S U) (hm : StrictMonoOn U S) (x y : S) :
    let p := BinaryLottery x y (3 / 5) (by constructor <;> norm_num)
    ∃ c : S, IsCertaintyEquivalent (fun z : S => U z) p c ∧
      U c = (3 / 5) * U x + (2 / 5) * U y ∧ (c : ℝ) ≤ (3 / 5) * x.val + (2 / 5) * y.val := by
  intro p
  obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
  have hce := riskPremium_nonneg hU hm he
  have hval := he
  change U c = ExpectedUtility (fun z : S => U z) p at hval
  have hb (f : S → ℝ) : ExpectedUtility f p = (3 / 5) * f x + (2 / 5) * f y := by
    simpa only [show (1 : ℝ) - 3 / 5 = 2 / 5 by norm_num] using
      expectedUtility_binary f x y (3 / 5) (by constructor <;> norm_num)
  rw [hb] at hval
  unfold RiskPremium at hce
  rw [hb] at hce
  exact ⟨c, he, hval, by linarith⟩

/-- Concavity guarantees continuity at the interior monetary prizes. -/
theorem concaveUtility_continuousOn_interior {S : Set ℝ} {U : ℝ → ℝ} (h : ConcaveOn ℝ S U) :
    ContinuousOn U (interior S) := h.continuousOn_interior

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Monetary utility from primitive preferences over lotteries

Kreps I, opening of Chapter 6 and pp. 123–127. The copied Chapter 5 mixture
theorem supplies the prize utility from primitive preferences. The numbered
money-utility tests use the same order, point masses, expectations and notion
of indifference. The mean payoff remains inside the original prize interval.
-/

namespace Kreps.UtilityForMoney

open Convexity

/-- The three primitive axioms supply the expected-utility representation used throughout
the chapter, on arbitrary prize types and arbitrary finite supports. -/
theorem monetary_representation_of_axioms {X : Type*} {r : SimpleLottery X → SimpleLottery X → Prop}
    (h : LotteryTheory.MixtureAxioms r) :
    ∃ U : X → ℝ, ∀ p q, r p q ↔ ExpectedUtility U q ≤ ExpectedUtility U p :=
  LotteryTheory.proposition_5_3.mp h

/-- Proposition 6.1 expressed in the primitive strict preference over sure lotteries. -/
theorem strictMono_iff_sure_preference {X : Type*} [Preorder X]
    {r : SimpleLottery X → SimpleLottery X → Prop} {U : X → ℝ}
    (h : LotteryTheory.Represents (ExpectedUtility U) r) :
    StrictMono U ↔ ∀ x y : X, x < y → LotteryTheory.Strict r (.single y) (.single x) := by
  unfold LotteryTheory.Represents at h
  simp only [LotteryTheory.Strict, h, expectedUtility_single, ← lt_iff_le_not_ge]
  exact ⟨fun hm _ _ hxy => hm hxy, fun hm _ _ hxy => hm _ _ hxy⟩

/-- A certainty equivalent is equivalently primitive indifference between a sure prize and the
original monetary lottery. -/
theorem isCertaintyEquivalent_iff_indifferent {X : Type*}
    {r : SimpleLottery X → SimpleLottery X → Prop} {U : X → ℝ}
    (h : LotteryTheory.Represents (ExpectedUtility U) r) (p : SimpleLottery X) (x : X) :
    IsCertaintyEquivalent U p x ↔ LotteryTheory.Indifferent r (.single x) p := by
  unfold LotteryTheory.Represents at h
  simp only [IsCertaintyEquivalent, LotteryTheory.Indifferent, h, expectedUtility_single]
  exact ⟨fun he => ⟨he.ge, he.le⟩, fun hh => hh.2.antisymm hh.1⟩

/-- Proposition 6.3 stated with the actual primitive ranking of the sure mean and the lottery. -/
theorem concave_iff_sure_mean_preferred {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    {r : SimpleLottery S → SimpleLottery S → Prop}
    (h : LotteryTheory.Represents (ExpectedUtility (fun x : S => U x)) r) :
    ConcaveOn ℝ S U ↔ ∀ p : SimpleLottery S,
      r (.single ⟨ExpectedUtility Subtype.val p,
        expectedUtility_mem_of_convex hS Subtype.val Subtype.property p⟩) p := by
  unfold LotteryTheory.Represents at h
  simpa only [h, expectedUtility_single] using proposition_6_3 hS U

/-- On an interval, risk aversion is equivalent to nonnegative premia for every lottery. -/
theorem concave_iff_nonnegative_premia {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hc : ContinuousOn U S) (hi : StrictMonoOn U S) :
    ConcaveOn ℝ S U ↔ ∀ (p : SimpleLottery S) (c : S),
      IsCertaintyEquivalent (fun x : S => U x) p c → 0 ≤ RiskPremium p c := by
  refine ⟨fun h _ _ he => riskPremium_nonneg h hi he, ?_⟩
  intro h
  apply (proposition_6_3 hS U).mpr
  intro p
  obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
  have hmean := expectedUtility_mem_of_convex hS Subtype.val Subtype.property p
  exact he.ge.trans (hi.monotoneOn c.property hmean (sub_nonneg.mp (h p c he)))

/-- Risk neutrality is equivalently a zero premium for every lottery on the monetary interval. -/
theorem riskNeutral_iff_zero_premia {S : Set ℝ} (hS : Convex ℝ S) {U : ℝ → ℝ}
    (hc : ContinuousOn U S) (hi : StrictMonoOn U S) :
    (∀ p : SimpleLottery S,
      ExpectedUtility (fun x : S => U x) p = U (ExpectedUtility Subtype.val p)) ↔
    ∀ (p : SimpleLottery S) (c : S),
      IsCertaintyEquivalent (fun x : S => U x) p c → RiskPremium p c = 0 := by
  constructor
  · intro h p c he
    have hmean := expectedUtility_mem_of_convex hS Subtype.val Subtype.property p
    exact sub_eq_zero.mpr (hi.injOn c.property hmean (he.trans (h p))).symm
  · intro h p
    obtain ⟨c, he⟩ := proposition_6_5_exists hS hc p
    rw [sub_eq_zero.mp (h p c he)]
    exact he.symm

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Hedging and dominated risky assets

Kreps I, Problem 6.12, p. 145. These constructed two-state examples use unit
initial wealth, equal state probabilities, safe gross return two, and no short
sales of any asset. An asset with low mean can hedge exposure to another asset.
A strictly dominated asset with mean above the safe rate need never be held.
-/

namespace Kreps.UtilityForMoney

/-- No short sales: two risky positions and the remaining safe position are nonnegative. -/
def RiskyPairMenu : Set (ℝ × ℝ) :=
  Set.Icc (0, 0) (1, 1) ∩ {q | q.1 + q.2 ≤ 1}

/-- The second risky asset hedges the first. Their gross returns are (0,12) and (3,0). -/
noncomputable def HedgeValue (q : ℝ × ℝ) : ℝ :=
  (ExponentialUtility 5 (3 * q.2 + 2 * (1 - q.1 - q.2)) +
    ExponentialUtility 5 (12 * q.1 + 2 * (1 - q.1 - q.2))) / 2

/-- The no-short-sale portfolio menu is compact and includes all-safe investment. -/
theorem riskyPairMenu_compact : IsCompact RiskyPairMenu ∧ (0, 0) ∈ RiskyPairMenu := by
  refine ⟨isCompact_Icc.inter_right (isClosed_le (continuous_fst.add continuous_snd)
    continuous_const), ?_⟩
  norm_num [RiskyPairMenu, Set.mem_Icc, Prod.le_def]

/-- The negative-correlation witness has an attained expected-utility optimum. -/
theorem hedgeValue_attains : ∃ q ∈ RiskyPairMenu, IsMaxOn HedgeValue RiskyPairMenu q := by
  have hc : Continuous HedgeValue := by unfold HedgeValue ExponentialUtility; fun_prop
  exact riskyPairMenu_compact.1.exists_isMaxOn ⟨_, riskyPairMenu_compact.2⟩ hc.continuousOn

/-- **Problem 6.12:** every optimum demands the hedge despite its mean 3/2 being below 2. -/
theorem problem_6_12_hedge {q : ℝ × ℝ} (hq : q ∈ RiskyPairMenu)
    (ho : IsMaxOn HedgeValue RiskyPairMenu q) : 0 < q.2 := by
  by_contra! hn
  have hzero : q.2 = 0 := le_antisymm hn hq.1.1.2
  let z : ℝ × ℝ := (1 / 5, 4 / 5)
  have hz : z ∈ RiskyPairMenu := by norm_num [z, RiskyPairMenu, Set.mem_Icc, Prod.le_def]
  have hbest : HedgeValue z ≤ HedgeValue q := ho hz
  have heq : HedgeValue z = -Real.exp (-12) := by norm_num [HedgeValue, z, ExponentialUtility]
  rw [heq] at hbest
  have hc₁ : 3 * q.2 + 2 * (1 - q.1 - q.2) ≤ 2 := by
    rw [hzero]
    linarith [hq.1.1.1]
  have h₁ := (exponentialUtility_strictMono (by norm_num : (0 : ℝ) < 5)).monotone hc₁
  have h₂ : ExponentialUtility 5 (12 * q.1 + 2 * (1 - q.1 - q.2)) < 0 :=
    neg_lt_zero.mpr (Real.exp_pos _)
  have he : Real.exp (-10) = Real.exp (-12) * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  unfold HedgeValue at hbest
  have hv : ExponentialUtility 5 2 = -Real.exp (-10) := by norm_num [ExponentialUtility]
  rw [hv, he] at h₁
  nlinarith [Real.exp_pos (-12), Real.add_one_le_exp (2 : ℝ),
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 : ℝ)) (Real.exp_pos (-12)).le]

/-- The two risky assets have gross returns (3,4) and (4,5), respectively. -/
noncomputable def DominatedValue (U : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (U (3 * q.1 + 4 * q.2 + 2 * (1 - q.1 - q.2)) +
    U (4 * q.1 + 5 * q.2 + 2 * (1 - q.1 - q.2))) / 2

/-- **Problem 6.12:** all wealth goes to the dominating asset though both means exceed two. -/
theorem problem_6_12_dominated (U : ℝ → ℝ) (hU : StrictMono U) :
    (0, 1) ∈ RiskyPairMenu ∧ ∀ q ∈ RiskyPairMenu, q ≠ (0, 1) →
      DominatedValue U q < DominatedValue U (0, 1) := by
  refine ⟨by norm_num [RiskyPairMenu, Set.mem_Icc, Prod.le_def], fun q hq hn => ?_⟩
  have hpos : 0 < q.1 ∨ q.2 < 1 := by
    by_contra! hw
    exact hn (Prod.ext (le_antisymm hw.1 hq.1.1.1) (le_antisymm hq.1.2.2 hw.2))
  have hs : q.1 + q.2 ≤ 1 := hq.2
  have h₁ : 3 * q.1 + 4 * q.2 + 2 * (1 - q.1 - q.2) < 4 := by
    rcases hpos with h | h <;> linarith
  have h₂ : 4 * q.1 + 5 * q.2 + 2 * (1 - q.1 - q.2) < 5 := by
    rcases hpos with h | h <;> linarith
  unfold DominatedValue
  norm_num
  linarith [hU h₁, hU h₂]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Joint price and income risk

Kreps I, pp. 137–138. Draw income and prices independently from finite-support
lotteries, then choose an optimal bundle after observing both. The induced income
index is the price-weighted indirect utility. The source's two correlated
couplings of incomes 10,000 and 20,000 demonstrate why the marginal laws alone
do not determine the consumer's purchasing power.
-/

namespace Kreps.UtilityForMoney

open scoped NNReal
open Convexity

variable {k : ℕ}

/-- Draw one income, then use the same conditional price law at every income. -/
noncomputable def IndependentPriceIncome (P : SimpleLottery (Demand.PositivePrices k))
    (Q : SimpleLottery ℝ≥0) : SimpleLottery (Demand.PositivePrices k × ℝ≥0) :=
  Q.iConvexComb fun y => P.map fun p => (p, y)

/-- For a fixed independent price lottery, the income index averages indirect utility. -/
noncomputable def PriceAveragedValue (U : Demand.NonnegativeOrthant k → ℝ)
    (P : SimpleLottery (Demand.PositivePrices k)) (y : ℝ≥0) : ℝ :=
  ExpectedUtility (fun p => Demand.IndirectUtility U p y) P

/-- The expected value of the product draw is the iterated expected indirect utility. -/
theorem independent_price_income_value (U : Demand.NonnegativeOrthant k → ℝ)
    (P : SimpleLottery (Demand.PositivePrices k)) (Q : SimpleLottery ℝ≥0) :
    ExpectedUtility (fun py => Demand.IndirectUtility U py.1 py.2) (IndependentPriceIncome P Q) =
      ExpectedUtility (PriceAveragedValue U P) Q := by
  let g : Demand.PositivePrices k × ℝ≥0 → ℝ := fun py => Demand.IndirectUtility U py.1 py.2
  change ExpectedUtility g _ = _
  rw [expectedUtility_eq_affine, IndependentPriceIncome,
    (StdSimplex.affineMapMk g).isAffineMap.map_iConvexComb, iConvexComb_eq_sum]
  apply Finset.sum_congr rfl
  intro y _
  change _ * StdSimplex.affineMapMk g (P.map fun p => (p, y)) = _
  rw [← expectedUtility_eq_affine, expectedUtility_map]
  rfl

/-- Independent price risk preserves continuity in nonnegative income. -/
theorem priceAveragedValue_continuous {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (P : SimpleLottery (Demand.PositivePrices k)) : Continuous (PriceAveragedValue U P) := by
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (proposition_6_16a hu p)

/-- Positive support weights preserve strict increase of the income index. -/
theorem priceAveragedValue_strictMono {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (hi : Demand.LocallyInsatiable (Demand.UtilityPref U))
    (P : SimpleLottery (Demand.PositivePrices k)) : StrictMono (PriceAveragedValue U P) := by
  intro y z hyz
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum_of_nonempty P.support_weights_nonempty
  intro p hp
  have hpos := lt_of_le_of_ne (P.nonneg p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  exact mul_lt_mul_of_pos_left (proposition_6_16b hu hi p hyz) hpos

/-- Independent price risk preserves concavity of indirect utility in income. -/
theorem priceAveragedValue_concave {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (hc : Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U)
    (P : SimpleLottery (Demand.PositivePrices k)) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => PriceAveragedValue U P y.toNNReal) := by
  refine ⟨convex_Ici _, ?_⟩
  intro y hy z hz a b ha hb hab
  unfold PriceAveragedValue ExpectedUtility Finsupp.sum
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have he := (proposition_6_16c hu hc p).2 hy hz ha hb hab
  simp only [smul_eq_mul] at he
  calc
    _ = P.weights p * (a * Demand.IndirectUtility U p y.toNNReal +
        b * Demand.IndirectUtility U p z.toNNReal) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (P.nonneg p)

/-- A finite price lottery at fixed income is valued by indirect utility at each price. -/
theorem fixed_income_price_lottery_value {U : Demand.NonnegativeOrthant k → ℝ} (y : ℝ≥0)
    (P : SimpleLottery (Demand.PositivePrices k)) (buy : Demand.PositivePrices k →
      Demand.NonnegativeOrthant k) (hb : ∀ p, buy p ∈ Demand.MarshallianDemand U p y) :
    ExpectedUtility U (P.map buy) = PriceAveragedValue U P y := by
  rw [expectedUtility_map]
  exact congrArg (fun g => ExpectedUtility g P)
    (funext fun p => (Demand.indirectUtility_eq_of_mem (hb p)).symm)

/-- At fixed income indirect utility is continuous in the positive prices. -/
theorem indirectUtility_continuous_prices {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (y : ℝ≥0) : Continuous (fun p => Demand.IndirectUtility U p y) :=
  (Demand.proposition_3_3c hu).comp (continuous_id.prodMk continuous_const)

/-- Increasing any prices weakly shrinks the budget and weakly lowers attained indirect utility. -/
theorem indirectUtility_antitone_prices {U : Demand.NonnegativeOrthant k → ℝ} (hu : Continuous U)
    (y : ℝ≥0) {p q : Demand.PositivePrices k} (hpq : p.val ≤ q.val) :
    Demand.IndirectUtility U q y ≤ Demand.IndirectUtility U p y := by
  obtain ⟨x, hx⟩ := Demand.proposition_3_1b hu q y
  obtain ⟨w, hw⟩ := Demand.proposition_3_1b hu p y
  rw [Demand.indirectUtility_eq_of_mem hx, Demand.indirectUtility_eq_of_mem hw]
  apply hw.2 x
  apply le_trans _ (show Demand.Expenditure q x ≤ (y : ℝ) from hx.1)
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hpq i) (x.property i))

/-- Doubling prices and income preserves purchasing power; reversing their pairing does not. -/
theorem two_price_income_couplings (p : Demand.PositivePrices k) :
    Demand.BudgetSet (Demand.ScalePrices 2 (by norm_num) p) 20000 = Demand.BudgetSet p 10000 ∧
    Demand.BudgetSet (Demand.ScalePrices 2 (by norm_num) p) 10000 = Demand.BudgetSet p 5000 := by
  constructor
  · ext x
    change Demand.Expenditure _ x ≤ (20000 : ℝ) ↔ Demand.Expenditure p x ≤ (10000 : ℝ)
    rw [Demand.expenditure_scalePrices]
    constructor <;> intro h <;> linarith
  · ext x
    change Demand.Expenditure _ x ≤ (10000 : ℝ) ↔ Demand.Expenditure p x ≤ (5000 : ℝ)
    rw [Demand.expenditure_scalePrices]
    constructor <;> intro h <;> linarith

/-- The equal-probability purchasing-power lottery is constant or ranges from 5,000 to 20,000. -/
theorem two_price_income_values (U : Demand.NonnegativeOrthant k → ℝ)
    (p : Demand.PositivePrices k) :
    let q := Demand.ScalePrices 2 (by norm_num) p
    let v := fun py : Demand.PositivePrices k × ℝ≥0 => Demand.IndirectUtility U py.1 py.2
    ExpectedUtility v (BinaryLottery (p, 10000) (q, 20000) (1 / 2) (by norm_num)) =
        Demand.IndirectUtility U p 10000 ∧
      ExpectedUtility v (BinaryLottery (q, 10000) (p, 20000) (1 / 2) (by norm_num)) =
        (Demand.IndirectUtility U p 5000 + Demand.IndirectUtility U p 20000) / 2 := by
  dsimp only
  rw [expectedUtility_binary, expectedUtility_binary]
  simp only [Demand.IndirectUtility, two_price_income_couplings p |>.1,
    two_price_income_couplings p |>.2]
  constructor <;> ring

/-- Mapping a binary draw transforms each branch and keeps its probability. -/
theorem priceRisk_map_binary {X Y : Type*} (f : X → Y) (x z : X)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    (BinaryLottery x z a ha).map f = BinaryLottery (f x) (f z) a ha := by
  unfold BinaryLottery
  rw [(StdSimplex.isAffineMap_map ℝ f).map_convexCombPair, StdSimplex.map_single,
    StdSimplex.map_single]

/-- The two source couplings have exactly the same marginal distributions of prices and income. -/
theorem two_price_income_marginals (p : Demand.PositivePrices k) :
    let q := Demand.ScalePrices 2 (by norm_num) p
    let joint₁ := BinaryLottery (p, (10000 : ℝ≥0)) (q, 20000) (1 / 2) (by norm_num)
    let joint₂ := BinaryLottery (q, (10000 : ℝ≥0)) (p, 20000) (1 / 2) (by norm_num)
    joint₁.map Prod.fst = joint₂.map Prod.fst ∧ joint₁.map Prod.snd = joint₂.map Prod.snd := by
  dsimp only
  simp only [priceRisk_map_binary, and_true]
  unfold BinaryLottery
  rw [convexCombPair_symm]
  norm_num

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk in relative prices and the price level

Kreps I, Problem 6.8, p. 143. Linear ordinal tastes favor gambling on which
good is cheap. With complementary goods, a strictly increasing piecewise
linear concave index can favor the mean price. Each fixed concave index on
the real line eventually favors sufficiently dispersed price levels. Strict
comparisons require positive income, since zero income allows only the origin.
-/

namespace Kreps.UtilityForMoney

/-- Feasible two-good bundles at unit prices `p` and `q` and income `y`. -/
def TwoGoodBudget (p q y : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ p * x.1 + q * x.2 ≤ y}

/-- At prices (1,3) or (3,1), the cheap good alone attains total quantity equal to income. -/
theorem sum_bundle_risky_price_optima (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget 1 3 y, f (x.1 + x.2) = f y) ∧
    (∃ x ∈ TwoGoodBudget 3 1 y, f (x.1 + x.2) = f y) ∧
    ∀ x : ℝ × ℝ, x ∈ TwoGoodBudget 1 3 y ∨ x ∈ TwoGoodBudget 3 1 y →
      f (x.1 + x.2) ≤ f y := by
  refine ⟨⟨(y, 0), ⟨hy, le_rfl, by simp⟩, by simp⟩,
    ⟨(0, y), ⟨le_rfl, hy, by simp⟩, by simp⟩, fun x hx => hf.monotone ?_⟩
  rcases hx with ⟨_, hx, hc⟩ | ⟨hx, _, hc⟩ <;> linarith

/-- At the sure mean prices (2,2), maximal total quantity is half of income. -/
theorem sum_bundle_mean_price_optimum (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget 2 2 y, f (x.1 + x.2) = f (y / 2)) ∧
    ∀ x ∈ TwoGoodBudget 2 2 y, f (x.1 + x.2) ≤ f (y / 2) := by
  refine ⟨⟨(y / 2, 0), ⟨by positivity, le_rfl, by dsimp; linarith⟩, by simp⟩,
    fun x hx => hf.monotone (by linarith [hx.2.2])⟩

/-- **Problem 6.8(a):** every increasing cardinalization strictly favors the risky prices. -/
theorem problem_6_8a (f : ℝ → ℝ) (hf : StrictMono f) {y : ℝ} (hy : 0 < y) :
    f (y / 2) < (f y + f y) / 2 := by
  rw [add_self_div_two]
  exact hf (by linarith)

/-- Maximum utility with complementary goods when both prices equal the price level. -/
theorem complementary_bundle_value (f : ℝ → ℝ) (hf : StrictMono f) {p y : ℝ}
    (hp : 0 < p) (hy : 0 ≤ y) :
    (∃ x ∈ TwoGoodBudget p p y, f (min x.1 x.2) = f (y / (2 * p))) ∧
    ∀ x ∈ TwoGoodBudget p p y, f (min x.1 x.2) ≤ f (y / (2 * p)) := by
  let t := y / (2 * p)
  have ht : (2 * p) * t = y := by dsimp [t]; field_simp
  refine ⟨⟨(t, t), ⟨by dsimp [t]; positivity, by dsimp [t]; positivity, ?_⟩, by simp [t]⟩,
    fun x hx => hf.monotone ((le_div_iff₀ (by positivity)).mpr ?_)⟩
  · dsimp
    linarith
  · have h₁ := mul_le_mul_of_nonneg_left (min_le_left x.1 x.2) hp.le
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right x.1 x.2) hp.le
    linarith [hx.2.2]

/-- A kinked cardinalization with unit left slope and strictly positive right slope. -/
def KinkedPriceUtility (c e t : ℝ) : ℝ := min t (c + e * (t - c))

/-- Positive slopes on both pieces guarantee strict increase. -/
theorem kinkedPriceUtility_strictMono {c e : ℝ} (he : 0 < e) :
    StrictMono (KinkedPriceUtility c e) := by
  intro x y h
  exact lt_min ((min_le_left _ _).trans_lt h)
    ((min_le_right _ _).trans_lt (by nlinarith [mul_pos he (sub_pos.mpr h)]))

/-- A pointwise minimum of these two affine functions is concave everywhere. -/
theorem kinkedPriceUtility_concave (c e : ℝ) : ConcaveOn ℝ Set.univ (KinkedPriceUtility c e) := by
  have h : ConcaveOn ℝ Set.univ (fun t : ℝ => c + e * (t - c)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    nlinarith only [congrArg (fun v : ℝ => v * (c - e * c)) hab]
  exact (concaveOn_id convex_univ).inf h

/-- The low, sure and high quantities of a complementary good are strictly ordered. -/
theorem price_level_quantities_order {y g : ℝ} (hy : 0 < y) (hg : 1 < g) :
    y / (2 * g) < y / (g + g⁻¹) ∧ y / (g + g⁻¹) < y * g / 2 := by
  have hgp : 0 < g := by linarith
  have hi : g⁻¹ < 1 := (inv_lt_one₀ hgp).mpr hg
  constructor
  · exact div_lt_div_of_pos_left hy (by positivity) (by linarith)
  · apply (div_lt_iff₀ (by positivity)).mpr
    field_simp
    nlinarith [mul_pos hy (mul_pos (sub_pos.mpr hg) (by linarith : 0 < g + 1))]

/-- A fixed price dispersion admits an increasing concave index favoring the sure price. -/
theorem problem_6_8b_fixed_dispersion {y g : ℝ} (hy : 0 < y) (hg : 1 < g) :
    ∃ f : ℝ → ℝ, StrictMono f ∧ ConcaveOn ℝ Set.univ f ∧
      (f (y / (2 * g)) + f (y * g / 2)) / 2 < f (y / (g + g⁻¹)) := by
  let l := y / (2 * g)
  let c := y / (g + g⁻¹)
  let u := y * g / 2
  obtain ⟨hl, hu⟩ := price_level_quantities_order hy hg
  change l < c at hl
  change c < u at hu
  let e := (c - l) / (2 * (u - c))
  have he : 0 < e := div_pos (sub_pos.mpr hl) (by linarith)
  have hid : e * (2 * (u - c)) = c - l := div_mul_cancel₀ _ (by linarith)
  refine ⟨KinkedPriceUtility c e, kinkedPriceUtility_strictMono he, kinkedPriceUtility_concave ..,
    ?_⟩
  change (min l _ + min u _) / 2 < min c (c + e * (c - c))
  rw [sub_self, mul_zero, add_zero, min_self]
  nlinarith only [min_le_left l (c + e * (l - c)), min_le_right u (c + e * (u - c)), hid, hl]

/-- Each fixed increasing concave index eventually prefers sufficiently dispersed price levels. -/
theorem problem_6_8b_large_dispersion (f : ℝ → ℝ) (hf : StrictMono f)
    (hc : ConcaveOn ℝ Set.univ f) {y : ℝ} (hy : 0 < y) :
    ∃ G > (1 : ℝ), ∀ g ≥ G,
      f (y / (g + g⁻¹)) < (f (y / (2 * g)) + f (y * g / 2)) / 2 := by
  have hcont : Continuous f := continuousOn_univ.mp (by simpa using hc.continuousOn_interior)
  have hlt : f 0 < (f 0 + f 1) / 2 := by linarith [hf (show (0 : ℝ) < 1 by norm_num)]
  obtain ⟨ε, hε, hs⟩ := Metric.isOpen_iff.mp
    (isOpen_lt hcont continuous_const) 0 hlt
  refine ⟨max 2 (max (y / ε) (2 / y)) + 1, by linarith [le_max_left 2 (max (y / ε) (2 / y))],
    fun g hg => ?_⟩
  have hg' : 0 < g := by linarith [le_max_left 2 (max (y / ε) (2 / y))]
  have hgε : y / ε < g := by
    linarith [le_max_right 2 (max (y / ε) (2 / y)), le_max_left (y / ε) (2 / y)]
  have hgy : 2 / y < g := by
    linarith [le_max_right 2 (max (y / ε) (2 / y)), le_max_right (y / ε) (2 / y)]
  have hlow : 0 < y / (g + g⁻¹) := by positivity
  have hsmall : y / (g + g⁻¹) < ε := (div_lt_iff₀ (by positivity)).mpr (by
    nlinarith [(div_lt_iff₀ hε).mp hgε, mul_pos hε (inv_pos.mpr hg')])
  have hcval := hs (show y / (g + g⁻¹) ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hlow] using hsmall)
  exact hcval.trans_le (by
    have h₁ := hf.monotone (show 0 ≤ y / (2 * g) by positivity)
    have h₂ := hf.monotone (show 1 ≤ y * g / 2 by linarith [(div_lt_iff₀ hy).mp hgy])
    linarith)

/-- The price lotteries in Problem 6.8(b) pay the two statewise optimized quantities. -/
theorem price_risk_expectedUtility (f : ℝ → ℝ) (y : ℝ) {g : ℝ} (hg : 0 < g) :
    ExpectedUtility f (BinaryLottery (y / (2 * g)) (y / (2 * g⁻¹)) (1 / 2) (by norm_num)) =
      (f (y / (2 * g)) + f (y * g / 2)) / 2 := by
  have he : y / (2 * g⁻¹) = y * g / 2 := by field_simp
  rw [expectedUtility_binary, he]
  ring

/-- At zero income all three statewise maxima coincide, so neither price regime is preferred. -/
theorem price_risk_at_zero_income (f : ℝ → ℝ) (g : ℝ) :
    (f (0 / (2 * g)) + f (0 * g / 2)) / 2 = f (0 / (g + g⁻¹)) := by
  simp

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Continuity of utility in the monetary prizes

Kreps I, Proposition 6.2, pp. 123–124. Comparisons with every fixed lottery
remain strict in a neighborhood of a strictly ranked sure prize. Every real
threshold between attained prize utilities is itself the value of a binary
lottery, which supplies the converse for arbitrary relative prize domains.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Both strict comparisons between a sure prize and a fixed lottery persist locally. -/
def StablePrizeComparisons {X : Type*} [TopologicalSpace X] (U : X → ℝ) : Prop :=
  ∀ (x : X) (p : SimpleLottery X),
    (U x < ExpectedUtility U p → ∀ᶠ y in 𝓝 x, U y < ExpectedUtility U p) ∧
    (ExpectedUtility U p < U x → ∀ᶠ y in 𝓝 x, ExpectedUtility U p < U y)

/-- **Proposition 6.2:** the sure-prize stability criterion characterizes continuity. -/
theorem proposition_6_2 {X : Type*} [TopologicalSpace X] (U : X → ℝ) :
    Continuous U ↔ StablePrizeComparisons U := by
  constructor
  · intro h x p
    exact ⟨fun hx => h.continuousAt.eventually (isOpen_Iio.mem_nhds hx),
      fun hx => h.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)⟩
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_order.mpr
    constructor
    · intro t ht
      by_cases hy : ∃ y, U y ≤ t
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨p, hp⟩ := exists_lottery_of_between U y x hy ht.le
        have hs := (h x p).2 (hp ▸ ht)
        simpa only [hp] using hs
      · exact Eventually.of_forall fun y => lt_of_not_ge (fun hn => hy ⟨y, hn⟩)
    · intro t ht
      by_cases hy : ∃ y, t ≤ U y
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨p, hp⟩ := exists_lottery_of_between U x y ht.le hy
        have hs := (h x p).1 (hp ▸ ht)
        simpa only [hp] using hs
      · exact Eventually.of_forall fun y => lt_of_not_ge (fun hn => hy ⟨y, hn⟩)

/-- For a metric prize space, local stability uses the source's open neighborhoods and radii. -/
theorem stablePrizeComparisons_iff_metric {X : Type*} [PseudoMetricSpace X] (U : X → ℝ) :
    StablePrizeComparisons U ↔ ∀ (x : X) (p : SimpleLottery X),
      (U x < ExpectedUtility U p → ∃ ε > 0, ∀ y, dist y x < ε → U y < ExpectedUtility U p) ∧
      (ExpectedUtility U p < U x → ∃ ε > 0, ∀ y, dist y x < ε → ExpectedUtility U p < U y) := by
  simp only [StablePrizeComparisons, Metric.eventually_nhds_iff]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite cumulative probabilities and inverse-CDF bins

Kreps I, Problem 6.5(b), pp. 141–142. A support point occupies the interval
from its left limit (excluded) to its cumulative mass (included). The ordered
finite sum below establishes coverage, including the final endpoint one.
-/

namespace Kreps.UtilityForMoney

/-- Finite cumulative sum including a possible atom at the upper endpoint. -/
noncomputable def Prefix (s : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ t ∈ s, if t ≤ x then w t else 0

/-- Finite cumulative sum strictly before the upper endpoint. -/
noncomputable def Before (s : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ t ∈ s, if t < x then w t else 0

/-- The threshold-indicator expectation is the sum of the corresponding point masses. -/
theorem cumulative_eq_prefix (p : SimpleLottery ℝ) (x : ℝ) :
    Cumulative p x = Prefix p.weights.support p.weights x := by
  simp [Cumulative, Prefix, ExpectedUtility, Finsupp.sum, mul_ite]

/-- The jump of the cumulative sum is exactly the included point mass. -/
theorem prefix_sub_before {s : Finset ℝ} (w : ℝ → ℝ) {x : ℝ} (hx : x ∈ s) :
    Prefix s w x - Before s w x = w x := by
  rw [Prefix, Before, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · simp
  · intro t _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h.le, h]
    · simp [h.not_ge, h.not_gt]
  · simp [hx]

/-- Bins of two different ordered prizes do not overlap. -/
theorem prefix_le_before_of_lt (s : Finset ℝ) {w : ℝ → ℝ} (hn : ∀ i ∈ s, 0 ≤ w i)
    {x y : ℝ} (hxy : x < y) : Prefix s w x ≤ Before s w y := by
  apply Finset.sum_le_sum
  intro t ht
  split_ifs <;> first | exact le_rfl | exact hn t ht | linarith

/-- The cumulative sums in a probability law lie between zero and one. -/
theorem prefix_probability_bounds (p : SimpleLottery ℝ) (t : ℝ) :
    0 ≤ Before p.weights.support p.weights t ∧
      Before p.weights.support p.weights t ≤ Prefix p.weights.support p.weights t ∧
      Prefix p.weights.support p.weights t ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), Finset.sum_le_sum (fun i _ => ?_), ?_⟩
  · split_ifs <;> simp
  · split_ifs <;> first | exact le_rfl | exact p.nonneg i | linarith
  · rw [← p.total]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact le_rfl | exact p.nonneg i

/-- A sum of increments over all adjacent cumulative intervals telescopes. -/
theorem sum_prefix_increments (s : Finset ℝ) (w f : ℝ → ℝ) :
    ∑ i ∈ s, (f (Prefix s w i) - f (Before s w i)) = f (∑ i ∈ s, w i) - f 0 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp [Prefix, Before]
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have hp (i : ℝ) (hi : i ∈ s) : Prefix (insert a s) w i = Prefix s w i := by
      simp [Prefix, ha, (hmax i hi).not_ge]
    have hb (i : ℝ) (hi : i ∈ s) : Before (insert a s) w i = Before s w i := by
      simp [Before, ha, (hmax i hi).not_gt]
    have hp' : Prefix (insert a s) w a = w a + ∑ i ∈ s, w i := by
      simp only [Prefix, Finset.sum_insert ha, le_rfl, ite_true]
      congr 1
      exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi).le
    have hb' : Before (insert a s) w a = ∑ i ∈ s, w i := by
      simp only [Before, Finset.sum_insert ha, lt_irrefl, ite_false, zero_add]
      exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi)
    have he : (∑ i ∈ s, (f (Prefix (insert a s) w i) - f (Before (insert a s) w i))) =
        ∑ i ∈ s, (f (Prefix s w i) - f (Before s w i)) := by
      exact Finset.sum_congr rfl fun i hi => by rw [hp i hi, hb i hi]
    rw [Finset.sum_insert ha, hp', hb', Finset.sum_insert ha, he, ih]
    ring

/-- The half-open cumulative bins cover the full cumulative interval. -/
theorem exists_prefix_bin (s : Finset ℝ) (w : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (ht : u ≤ ∑ i ∈ s, w i) :
    ∃ i ∈ s, u ∈ Set.Ioc (Before s w i) (Prefix s w i) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp at ht; linarith
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    by_cases h : u ≤ ∑ i ∈ s, w i
    · obtain ⟨i, hi, hm⟩ := ih h
      refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
      simpa [Before, Prefix, ha, (hmax i hi).not_ge, (hmax i hi).not_gt] using hm
    · refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩
      · have he : Before (insert a s) w a = ∑ i ∈ s, w i := by
          simp only [Before, Finset.sum_insert ha, lt_irrefl, ite_false, zero_add]
          exact Finset.sum_congr rfl fun i hi => ite_eq_left (hmax i hi)
        exact he ▸ lt_of_not_ge h
      · have he : Prefix (insert a s) w a = ∑ i ∈ insert a s, w i := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ite_eq_left le_rfl
          · exact ite_eq_left (hmax i hi).le
        exact he ▸ ht

/-- The uniform-probability interval of a monetary prize. -/
noncomputable def QuantileBin (p : SimpleLottery ℝ) (x : ℝ) : Set ℝ :=
  Set.Ioc (Before p.weights.support p.weights x) (Prefix p.weights.support p.weights x)

/-- Choosing the prize of the unique bin implements inverse-CDF sampling on `(0,1]`. -/
noncomputable def QuantilePrize (p : SimpleLottery ℝ) (u : ℝ) : ℝ := by
  classical
  exact if h : ∃ x ∈ p.weights.support, u ∈ QuantileBin p x then h.choose
    else p.weights.support.min' p.support_weights_nonempty

/-- At the zero endpoint of the uniform draw the book assigns the smallest support prize. -/
theorem quantilePrize_zero (p : SimpleLottery ℝ) :
    QuantilePrize p 0 = p.weights.support.min' p.support_weights_nonempty := by
  have hn : ¬ ∃ x ∈ p.weights.support, 0 ∈ QuantileBin p x := by
    rintro ⟨x, _, hx⟩
    exact (not_lt_of_ge (prefix_probability_bounds p x).1) hx.1
  simp only [QuantilePrize, dite_eq_right hn]

/-- Every uniform draw in `(0,1]` lands on a support point and in that point's bin. -/
theorem quantilePrize_mem_bin (p : SimpleLottery ℝ) {u : ℝ} (hu : u ∈ Set.Ioc 0 1) :
    QuantilePrize p u ∈ p.weights.support ∧ u ∈ QuantileBin p (QuantilePrize p u) := by
  have h : ∃ x ∈ p.weights.support, u ∈ QuantileBin p x :=
    exists_prefix_bin _ _ _ hu.1 (by
      change u ≤ p.weights.sum (fun _ a => a)
      rw [p.total]
      exact hu.2)
  simpa only [QuantilePrize, dite_eq_left h] using h.choose_spec

/-- Bins meeting at the same draw have the same prize. -/
theorem quantileBin_unique (p : SimpleLottery ℝ) {u x y : ℝ}
    (hx : u ∈ QuantileBin p x) (hy : u ∈ QuantileBin p y) : x = y := by
  have h {i j : ℝ} := @prefix_le_before_of_lt p.weights.support p.weights
    (fun i _ => p.nonneg i) i j
  rcases lt_trichotomy x y with hxy | he | hyx
  · exact False.elim ((not_lt_of_ge (hx.2.trans (h hxy))) hy.1)
  · exact he
  · exact False.elim ((not_lt_of_ge (hy.2.trans (h hyx))) hx.1)

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order dominance by common uniform draws

Kreps I, Propositions 6.14(a) and 6.15(a), and Problem 6.5(b–d), pp. 132–133,
141–142. A uniform draw selects the support point of its half-open cumulative
interval. The joint probability of two prizes is the length of the intersection
of their intervals, which gives the two specified margins.
-/

namespace Kreps.UtilityForMoney

open MeasureTheory

/-- Each quantile bin lies in the unit draw interval. -/
theorem quantileBin_subset_unit (p : SimpleLottery ℝ) (x : ℝ) :
    QuantileBin p x ⊆ Set.Ioc 0 1 := by
  intro u hu
  have hb := prefix_probability_bounds p x
  exact ⟨hb.1.trans_lt hu.1, hu.2.trans hb.2.2⟩

/-- **Problem 6.5(b):** inverse-CDF sampling has each exact prescribed point mass. -/
theorem quantilePrize_uniform_mass (p : SimpleLottery ℝ) (x : ℝ) :
    volume {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = ENNReal.ofReal (p.weights x) := by
  by_cases hx : x ∈ p.weights.support
  · have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = QuantileBin p x := by
      ext u
      constructor
      · rintro ⟨hu, rfl⟩
        exact (quantilePrize_mem_bin p hu).2
      · intro hu
        have h := quantileBin_subset_unit p x hu
        exact ⟨h, quantileBin_unique p (quantilePrize_mem_bin p h).2 hu⟩
    rw [he, QuantileBin, Real.volume_Ioc, prefix_sub_before _ hx]
  · have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, he⟩
      exact hx (he ▸ (quantilePrize_mem_bin p hu).1)
    rw [he, measure_empty, Finsupp.notMem_support_iff.mp hx, ENNReal.ofReal_zero]

/-- Length of the intersection of two real probability bins, by inclusion and exclusion. -/
def Overlap (a b c d : ℝ) : ℝ := (min b d - min b c) - (min a d - min a c)

/-- The overlap agrees with the nonnegative part of the difference of its endpoints. -/
theorem overlap_eq_length {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    Overlap a b c d = max (min b d - max a c) 0 := by
  unfold Overlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Exchanging the bins does not change their overlap. -/
theorem overlap_comm (a b c d : ℝ) : Overlap a b c d = Overlap c d a b := by
  unfold Overlap
  rw [min_comm b d, min_comm b c, min_comm a d, min_comm a c]
  ring

/-- The sum of intersections of a fixed unit subinterval with all bins equals its length. -/
theorem sum_overlap_bins (p : SimpleLottery ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∑ j : p.weights.support, Overlap a b (Before p.weights.support p.weights j.val)
      (Prefix p.weights.support p.weights j.val) = b - a := by
  classical
  rw [Finset.sum_coe_sort p.weights.support (fun j =>
    Overlap a b (Before p.weights.support p.weights j) (Prefix p.weights.support p.weights j))]
  unfold Overlap
  rw [Finset.sum_sub_distrib,
    sum_prefix_increments p.weights.support p.weights (fun t => min b t),
    sum_prefix_increments p.weights.support p.weights (fun t => min a t)]
  have h₁ : ∑ x ∈ p.weights.support, p.weights x = 1 := p.total
  rw [h₁, min_eq_left hb, min_eq_left (hab.trans hb), min_eq_right (ha.trans hab), min_eq_right ha]
  ring

/-- The joint table formed from the shared uniform draw. -/
noncomputable def QuantileCoupling (p q : SimpleLottery ℝ) : FiniteCoupling p q where
  mass i j := Overlap (Before p.weights.support p.weights i.val)
    (Prefix p.weights.support p.weights i.val) (Before q.weights.support q.weights j.val)
    (Prefix q.weights.support q.weights j.val)
  nonneg i j := by
    rw [overlap_eq_length (prefix_probability_bounds p i.val).2.1
      (prefix_probability_bounds q j.val).2.1]
    exact le_max_right _ _
  row_sum i := by
    have h := prefix_probability_bounds p i.val
    rw [sum_overlap_bins q h.1 h.2.1 h.2.2, prefix_sub_before _ i.property]
  col_sum j := by
    have h := prefix_probability_bounds q j.val
    simp_rw [overlap_comm _ _ (Before q.weights.support q.weights j.val)
      (Prefix q.weights.support q.weights j.val)]
    rw [sum_overlap_bins p h.1 h.2.1 h.2.2, prefix_sub_before _ j.property]

/-- A nonnegative supplement, in matrix form, holds at every joint atom of positive mass. -/
def FiniteCoupling.Ordered {p q : SimpleLottery ℝ} (C : FiniteCoupling p q) : Prop :=
  ∀ i j, 0 < C.mass i j → j.val ≤ i.val

/-- **Problem 6.5(c):** the ordered CDFs put the first quantile weakly above the second. -/
theorem quantileCoupling_ordered {p q : SimpleLottery ℝ}
    (h : ∀ r, Cumulative p r ≤ Cumulative q r) :
    (QuantileCoupling p q).Ordered := by
  intro i j hm
  by_contra! hlt
  have hp := prefix_le_before_of_lt q.weights.support (fun t _ => q.nonneg t) hlt
  have he := (cumulative_eq_prefix p i.val).symm.le.trans
    ((h i.val).trans (cumulative_eq_prefix q i.val).le)
  change 0 < Overlap _ _ _ _ at hm
  rw [overlap_eq_length (prefix_probability_bounds p i.val).2.1
    (prefix_probability_bounds q j.val).2.1] at hm
  have hmin := min_le_left (Prefix p.weights.support p.weights i.val)
    (Prefix q.weights.support q.weights j.val)
  have hmax := le_max_right (Before p.weights.support p.weights i.val)
    (Before q.weights.support q.weights j.val)
  rw [max_eq_right (sub_nonpos.mpr ((hmin.trans he).trans (hp.trans hmax)))] at hm
  exact (lt_irrefl _ hm)

/-- **Problem 6.5(d):** a nonnegative supplement increases all nondecreasing expected utilities. -/
theorem firstOrder_of_ordered_coupling {p q : SimpleLottery ℝ} (C : FiniteCoupling p q)
    (ho : C.Ordered) : FirstOrderDominates p q := by
  intro U hi
  rw [← C.first_marginal, ← C.second_marginal]
  unfold ExpectedUtility
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  rintro ⟨i, j⟩ _
  change C.mass i j * U j.val ≤ C.mass i j * U i.val
  rcases (C.nonneg i j).eq_or_lt with he | hpos
  · simp [← he]
  · exact mul_le_mul_of_nonneg_left (hi (ho i j hpos)) hpos.le

/-- **Proposition 6.14(a):** first-order dominance iff the cumulative probabilities are ordered. -/
theorem proposition_6_14a (p q : SimpleLottery ℝ) :
    FirstOrderDominates p q ↔ ∀ r, Cumulative p r ≤ Cumulative q r :=
  ⟨cumulative_le_of_firstOrder, fun h =>
    firstOrder_of_ordered_coupling _ (quantileCoupling_ordered h)⟩

/-- **Proposition 6.15(a):** first-order dominance iff there is a common ordered coupling. -/
theorem proposition_6_15a (p q : SimpleLottery ℝ) :
    FirstOrderDominates p q ↔ ∃ C : FiniteCoupling p q, C.Ordered :=
  ⟨fun h => ⟨QuantileCoupling p q, quantileCoupling_ordered ((proposition_6_14a p q).mp h)⟩,
    fun ⟨C, hc⟩ => firstOrder_of_ordered_coupling C hc⟩

/-- Intersections of the two inverse-CDF bins give the actual joint law under the same uniform
draw, including atoms shared by the two marginal laws. -/
theorem quantile_uniform_joint_mass (p q : SimpleLottery ℝ)
    (i : p.weights.support) (j : q.weights.support) :
    volume {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = i.val ∧ QuantilePrize q u = j.val} =
      ENNReal.ofReal ((QuantileCoupling p q).mass i j) := by
  have he : {u ∈ Set.Ioc (0 : ℝ) 1 | QuantilePrize p u = i.val ∧ QuantilePrize q u = j.val} =
      QuantileBin p i.val ∩ QuantileBin q j.val := by
    ext u
    constructor
    · rintro ⟨hu, hp, hq⟩
      exact ⟨hp ▸ (quantilePrize_mem_bin p hu).2, hq ▸ (quantilePrize_mem_bin q hu).2⟩
    · rintro ⟨hp, hq⟩
      have hu := quantileBin_subset_unit p _ hp
      exact ⟨hu, quantileBin_unique p (quantilePrize_mem_bin p hu).2 hp,
        quantileBin_unique q (quantilePrize_mem_bin q hu).2 hq⟩
  rw [he, QuantileBin, QuantileBin, Set.Ioc_inter_Ioc, Real.volume_Ioc]
  change _ = ENNReal.ofReal (Overlap _ _ _ _)
  rw [overlap_eq_length (prefix_probability_bounds p _).2.1 (prefix_probability_bounds q _).2.1]
  simp

/-- Ordered CDFs give ordered realized prizes for every common draw in the unit interval. -/
theorem quantilePrize_ordered {p q : SimpleLottery ℝ} (h : ∀ r, Cumulative p r ≤ Cumulative q r)
    {u : ℝ} (hu : u ∈ Set.Ioc 0 1) : QuantilePrize q u ≤ QuantilePrize p u := by
  have hp := (quantilePrize_mem_bin p hu).2
  have hq := (quantilePrize_mem_bin q hu).2
  by_contra! hlt
  have he := prefix_le_before_of_lt q.weights.support (fun t _ => q.nonneg t) hlt
  have hc := (cumulative_eq_prefix p _).symm.le.trans
    ((h (QuantilePrize p u)).trans (cumulative_eq_prefix q _).le)
  exact (not_lt_of_ge (hp.2.trans (hc.trans he))) hq.1

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Proportional gambles and relative risk aversion

Kreps I, pp. 131–132. With strictly positive wealth and gross returns, the
certainty-equivalent rate is the sure gross return that matches the lottery.
The printed equivalence on p. 132 has a reversed monotonicity direction for
the relative Arrow–Pratt coefficient.
-/

namespace Kreps.UtilityForMoney

/-- Derivatives of a utility scaled in its wealth input. -/
theorem deriv_scaled_wealth (U : ℝ → ℝ) (w x : ℝ) :
    deriv (fun t => U (w * t)) x = deriv U (w * x) * w := by
  simpa [mul_comm] using deriv_comp_mul_left (f := U) w x

/-- Absolute risk with respect to the rate equals relative wealth risk divided by the rate. -/
theorem absoluteRiskAversion_scaled {U : ℝ → ℝ} {w t : ℝ} (hw : 0 < w) (ht : 0 < t)
    (h₂ : DifferentiableAt ℝ (deriv U) (w * t)) :
    AbsoluteRiskAversion (fun z => U (w * z)) t = RelativeRiskAversion U (w * t) / t := by
  have hd := funext (deriv_scaled_wealth U w)
  have he := (h₂.hasDerivAt.comp t ((hasDerivAt_id' t).const_mul w)).mul_const w
  have h₂eq : deriv (fun x => deriv U (w * x) * w) t =
      deriv (deriv U) (w * t) * w * w := by
    simpa only [mul_one, Function.comp_def] using he.deriv
  rw [AbsoluteRiskAversion, hd, h₂eq]
  unfold RelativeRiskAversion AbsoluteRiskAversion
  field_simp

/-- The riskier gross return yields a weakly lower certainty-equivalent rate at higher wealth. -/
def NonincreasingCertaintyReturn (U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, 0 < u → u ≤ v → ∀ (p : SimpleLottery (Set.Ioi (0 : ℝ)))
    (c d : Set.Ioi (0 : ℝ)),
    IsCertaintyEquivalent (fun t : Set.Ioi (0 : ℝ) => U (u * t)) p c →
    IsCertaintyEquivalent (fun t : Set.Ioi (0 : ℝ) => U (v * t)) p d → d ≤ c

/-- Reversing the certainty-equivalent rates is equivalent to comparing all acceptance decisions. -/
theorem nonincreasingCertaintyReturn_iff {U : ℝ → ℝ} (hi : StrictMonoOn U (Set.Ioi 0))
    (hc : ContinuousOn U (Set.Ioi 0)) :
    NonincreasingCertaintyReturn U ↔ ∀ u v : ℝ, 0 < u → u ≤ v →
      MoreRiskAverse (Set.Ioi 0) (fun t => U (v * t)) (fun t => U (u * t)) := by
  have hm (w : ℝ) (hw : 0 < w) : StrictMonoOn (fun t => U (w * t)) (Set.Ioi 0) :=
    fun _ hx _ hy h => hi (mul_pos hw hx) (mul_pos hw hy) (mul_lt_mul_of_pos_left h hw)
  have hcont (w : ℝ) (hw : 0 < w) : ContinuousOn (fun t => U (w * t)) (Set.Ioi 0) :=
    hc.comp (continuous_const.mul continuous_id).continuousOn (fun _ ht => mul_pos hw ht)
  constructor
  · intro h u v hu huv
    apply (premiumOrder_iff_moreRiskAverse (convex_Ioi _) (hm v (hu.trans_le huv))
      (hm u hu) (hcont v (hu.trans_le huv)) (hcont u hu)).mp
    intro p d c hd hc'
    have hdc : (d : ℝ) ≤ c := h u v hu huv p c d hc' hd
    exact sub_le_sub_left hdc _
  · intro h u v hu huv p c d hc' hd
    have he := (premiumOrder_iff_moreRiskAverse (convex_Ioi _) (hm v (hu.trans_le huv))
      (hm u hu) (hcont v (hu.trans_le huv)) (hcont u hu)).mpr (h u v hu huv) p d c hd hc'
    unfold RiskPremium at he
    change (d : ℝ) ≤ c
    linarith

/-- Corrected p. 132 equivalence: falling certainty-equivalent rates correspond to *rising*
relative risk aversion as wealth increases. -/
theorem nonincreasingCertaintyReturn_iff_relative {U : ℝ → ℝ} (hi : StrictMonoOn U (Set.Ioi 0))
    (hU : ∀ x > 0, ContDiffAt ℝ 2 U x) (hp : ∀ x > 0, 0 < deriv U x) :
    NonincreasingCertaintyReturn U ↔ MonotoneOn (RelativeRiskAversion U) (Set.Ioi 0) := by
  have hc : ContinuousOn U (Set.Ioi 0) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  rw [nonincreasingCertaintyReturn_iff hi hc]
  have hsm (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      ContDiffAt ℝ 2 (fun z => U (w * z)) t :=
    (hU _ (mul_pos hw ht)).comp t (contDiffAt_const.mul contDiffAt_id)
  have hpos (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      0 < deriv (fun z => U (w * z)) t := by
    rw [deriv_scaled_wealth]
    exact mul_pos (hp _ (mul_pos hw ht)) hw
  have hder (w : ℝ) (hw : 0 < w) (t : ℝ) (ht : 0 < t) :=
    absoluteRiskAversion_scaled (U := U) hw ht
      (((hU _ (mul_pos hw ht)).derivWithin (m := 1) (by norm_num)).differentiableAt_one)
  have hiff (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :=
    proposition_6_8 (convex_Ioi (0 : ℝ)) (by simp : (interior (Set.Ioi (0 : ℝ))).Nonempty)
      (hsm v hv) (hsm u hu) (fun _ hx _ hy h =>
        hi (mul_pos hu hx) (mul_pos hu hy) (mul_lt_mul_of_pos_left h hu)) (hpos v hv) (hpos u hu)
  constructor
  · intro h u hu v hv huv
    have he := (hiff u v hu hv).mp (h u v hu huv) 1 (by norm_num)
    simpa [hder u hu 1 (by norm_num), hder v hv 1 (by norm_num)] using he
  · intro h u v hu huv
    apply (hiff u v hu (hu.trans_le huv)).mpr
    intro t ht
    rw [hder u hu t ht, hder v (hu.trans_le huv) t ht]
    exact div_le_div_of_nonneg_right (h (mul_pos hu ht) (mul_pos (hu.trans_le huv) ht)
      (mul_le_mul_of_nonneg_right huv ht.le)) ht.le

/-- Exact counterexample to the printed direction: negative exponential utility has increasing
relative risk aversion and nonincreasing certainty-equivalent gross returns. -/
theorem relativeRisk_printed_counterexample :
    NonincreasingCertaintyReturn (ExponentialUtility 1) ∧
      ¬ AntitoneOn (RelativeRiskAversion (ExponentialUtility 1)) (Set.Ioi 0) := by
  have he (x : ℝ) : RelativeRiskAversion (ExponentialUtility 1) x = x := by
    rw [RelativeRiskAversion, absoluteRiskAversion_exponential one_ne_zero, mul_one]
  refine ⟨?_, ?_⟩
  · apply (nonincreasingCertaintyReturn_iff_relative
      ((exponentialUtility_strictMono zero_lt_one).strictMonoOn _)
      (fun x _ => by unfold ExponentialUtility; fun_prop)
      (fun x _ => by rw [(exponentialUtility_hasDerivAt 1 x).deriv]; positivity)).mpr
    intro x _ y _ h
    simpa [he] using h
  · intro h
    have hh := h (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rw [he, he] at hh
    norm_num at hh

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Independent repetitions of the favorable-mean gamble

Kreps I, Problem 6.14, pp. 146–147. Every fresh trial pays 1,000 with
probability 2/5 and costs 500 with probability 3/5. The finite-horizon law
branches independently of past wealth. Exponential utility with coefficient
log(2)/500 gives an exact expected-utility multiplier of 13/10 per trial.
-/

namespace Kreps.UtilityForMoney

/-- An independent fresh branch with the printed win probability. -/
noncomputable def TrialBranch {X : Type*} (win lose : SimpleLottery X) : SimpleLottery X :=
  LotteryTheory.Mix ⟨2 / 5, by norm_num⟩ win lose

/-- Evaluation of a fresh trial averages its two continuation lotteries. -/
theorem trialBranch_value {X : Type*} (u : X → ℝ) (win lose : SimpleLottery X) :
    ExpectedUtility u (TrialBranch win lose) =
      (2 * ExpectedUtility u win + 3 * ExpectedUtility u lose) / 5 := by
  have he := LotteryTheory.expectedUtility_affine u (⟨2 / 5, by norm_num⟩ : LotteryTheory.Weight)
    win lose
  change ExpectedUtility u (TrialBranch win lose) =
    2 / 5 * ExpectedUtility u win + (1 - 2 / 5) * ExpectedUtility u lose at he
  rw [he]
  ring

/-- Terminal-wealth lottery with a fixed number of independent trials and no bankruptcy stop. -/
noncomputable def RepeatedLaw : ℕ → ℝ → SimpleLottery ℝ
  | 0, w => Convexity.StdSimplex.single w
  | n + 1, w => TrialBranch (RepeatedLaw n (w + 1000)) (RepeatedLaw n (w - 500))

/-- The source gamble has positive expected monetary gain of exactly 100 per trial. -/
theorem repeatedLaw_mean (n : ℕ) (w : ℝ) : ExpectedUtility id (RepeatedLaw n w) = w + 100 * n := by
  induction n generalizing w with
  | zero => simp [RepeatedLaw, expectedUtility_single]
  | succ n ih =>
    rw [RepeatedLaw, trialBranch_value, ih, ih]
    push_cast
    ring

/-- A win divides this negative exponential utility by four; a loss doubles it. -/
theorem repeated_exponential_steps (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    V (w + 1000) = V w / 4 ∧ V (w - 500) = 2 * V w := by
  dsimp only [ExponentialUtility]
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  constructor
  · rw [show -(Real.log 2 / 500) * (w + 1000) =
      -(Real.log 2 / 500) * w + -(Real.log 2 + Real.log 2) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_add, he]
    ring
  · rw [show -(Real.log 2 / 500) * (w - 500) =
      -(Real.log 2 / 500) * w + Real.log 2 by ring, Real.exp_add, he]
    ring

/-- Exact expected utility for all finite numbers of independent copies. -/
theorem repeatedLaw_exponential (n : ℕ) (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    ExpectedUtility V (RepeatedLaw n w) = (13 / 10 : ℝ) ^ n * V w := by
  intro V
  induction n generalizing w with
  | zero => simp [RepeatedLaw, expectedUtility_single]
  | succ n ih =>
    have he : V (w + 1000) = V w / 4 ∧ V (w - 500) = 2 * V w := repeated_exponential_steps w
    rw [RepeatedLaw, trialBranch_value, ih, ih, he.1, he.2, pow_succ]
    ring

/-- **Problem 6.14, interpretation 1:** a rational risk-averse consumer rejects every horizon. -/
theorem problem_6_14_unrestricted {n : ℕ} (hn : 0 < n) (w : ℝ) :
    let V := ExponentialUtility (Real.log 2 / 500)
    StrictMono V ∧ StrictConcaveOn ℝ Set.univ V ∧ ExpectedUtility V (RepeatedLaw n w) < V w := by
  intro V
  have h : 0 < Real.log 2 / 500 := by positivity
  refine ⟨exponentialUtility_strictMono h, exponentialUtility_strictConcave h, ?_⟩
  rw [repeatedLaw_exponential]
  have hz : V w < 0 := neg_lt_zero.mpr (Real.exp_pos _)
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr (one_lt_pow₀ (by norm_num : (1 : ℝ) < 13 / 10)
    hn.ne')) hz]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Buying a small share of a favorable gamble

Kreps I, Problem 6.13, pp. 145–146. The first-order gain is the expected product
of statewise marginal utility and net payoff. It factors at fixed wealth or
under independence. A kink at initial wealth and dependence on background
wealth can each reverse the comparison.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Expected utility of adding a fractional net gain to possibly random initial wealth. -/
noncomputable def ShareValue {I : Type*} (V : ℝ → ℝ) (p : SimpleLottery I)
    (w g : I → ℝ) (a : ℝ) : ℝ := ExpectedUtility (fun i => V (w i + a * g i)) p

/-- The marginal value is the expectation of marginal utility times the net gain. -/
theorem shareValue_hasDerivAt_zero {I : Type*} (V : ℝ → ℝ) (p : SimpleLottery I)
    (w g : I → ℝ) (hd : ∀ i, DifferentiableAt ℝ V (w i)) :
    HasDerivAt (ShareValue V p w g) (ExpectedUtility (fun i => deriv V (w i) * g i) p) 0 := by
  unfold ShareValue ExpectedUtility Finsupp.sum
  apply HasDerivAt.fun_sum
  intro i _
  have hw : HasDerivAt (fun a : ℝ => w i + a * g i) (g i) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const (g i)).const_add (w i))
  have hv : HasDerivAt V (deriv V (w i)) (w i + 0 * g i) := by simpa using (hd i).hasDerivAt
  exact ((hv.comp 0 hw).const_mul (p.weights i))

/-- **Problem 6.13(a):** at fixed wealth every sufficiently small positive share is desirable. -/
theorem problem_6_13a {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V) (hi : StrictMono V)
    (p : SimpleLottery ℝ) (w b : ℝ) (hw : DifferentiableAt ℝ V w)
    (hE : 0 < ExpectedUtility id p) (hb : b < 1) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), V w < ShareValue V p (fun _ => w)
      (fun x => x - b * ExpectedUtility id p) a := by
  let E := ExpectedUtility id p
  have hd := shareValue_hasDerivAt_zero V p (fun _ => w) (fun x => x - b * E) (fun _ => hw)
  have he : ExpectedUtility (fun x => deriv V w * (x - b * E)) p = deriv V w * ((1 - b) * E) := by
    rw [show (fun x => deriv V w * (x - b * E)) = fun x => deriv V w * id x +
      (-(deriv V w * b * E)) by funext x; dsimp; ring, expectedUtility_affine_payoff]
    dsimp [E]
    ring
  rw [he] at hd
  have hg := improves_small_positive hd
    (mul_pos (deriv_pos_of_concave_strictMono hc hi hw) (mul_pos (sub_pos.mpr hb) hE))
  simpa only [ShareValue, zero_mul, add_zero, expectedUtility_const] using hg

/-- The result persists with independent finite background wealth by conditioning on its value. -/
theorem small_share_independent_wealth {V : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ V)
    (hi : StrictMono V) (hd : Differentiable ℝ V) (p q : SimpleLottery ℝ) (b : ℝ)
    (hE : 0 < ExpectedUtility id p) (hb : b < 1) : ∀ᶠ a in 𝓝[>] (0 : ℝ),
    ExpectedUtility V q < ExpectedUtility (fun w => ShareValue V p (fun _ => w)
      (fun x => x - b * ExpectedUtility id p) a) q := by
  have he := (Filter.eventually_all_finset q.weights.support).mpr
    (fun w _ => problem_6_13a hc hi p w b (hd w) hE hb)
  filter_upwards [he] with a ha
  unfold ExpectedUtility Finsupp.sum
  apply Finset.sum_lt_sum_of_nonempty q.support_weights_nonempty
  intro w hw
  exact mul_lt_mul_of_pos_left (ha w hw) (lt_of_le_of_ne (q.nonneg w)
    (Ne.symm (Finsupp.mem_support_iff.mp hw)))

/-- A fair binary draw with net gains minus one or plus three has mean plus one. -/
noncomputable def SmallShareLaw : SimpleLottery ℝ :=
  BinaryLottery (-1) 3 (1 / 2) (by norm_num)

/-- The exact positive mean of the small-share example. -/
theorem smallShareLaw_mean : ExpectedUtility id SmallShareLaw = 1 := by
  rw [SmallShareLaw, expectedUtility_binary]
  norm_num

/-- A kink at initial wealth gives a strict loss for every positive share of the favorable draw. -/
theorem small_share_kink {a : ℝ} (ha : 0 < a) :
    ShareValue (KinkedPriceUtility 0 (1 / 4)) SmallShareLaw (fun _ => 0) id a <
      KinkedPriceUtility 0 (1 / 4) 0 := by
  rw [ShareValue, SmallShareLaw, expectedUtility_binary]
  simp only [id_eq, KinkedPriceUtility, zero_add, sub_zero, mul_zero, min_self, mul_neg, mul_one]
  rw [min_eq_left (by linarith), min_eq_right (by linarith)]
  linarith

/-- The counterexample's utility is increasing and concave and genuinely lacks the derivative. -/
theorem small_share_kink_nondifferentiable :
    StrictMono (KinkedPriceUtility 0 (1 / 4)) ∧
    ConcaveOn ℝ Set.univ (KinkedPriceUtility 0 (1 / 4)) ∧
    ¬DifferentiableAt ℝ (KinkedPriceUtility 0 (1 / 4)) 0 := by
  have hi := kinkedPriceUtility_strictMono (c := 0) (by norm_num : (0 : ℝ) < 1 / 4)
  have hc := kinkedPriceUtility_concave 0 (1 / 4)
  refine ⟨hi, hc, fun hd => ?_⟩
  have h := problem_6_13a hc hi SmallShareLaw 0 0 hd (by rw [smallShareLaw_mean]; norm_num)
    (by norm_num)
  have hp : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hv⟩ := (hp.and h).exists
  simp only [zero_mul, sub_zero] at hv
  exact (small_share_kink ha).not_gt hv

/-- An adverse wealth correlation reverses the small-share comparison even with smooth utility. -/
theorem small_share_correlated_loss :
    let wealth := fun x : ℝ => if x = -1 then 0 else 2
    ∀ᶠ a in 𝓝[>] (0 : ℝ), ShareValue (ExponentialUtility 1) SmallShareLaw wealth id a <
      ShareValue (ExponentialUtility 1) SmallShareLaw wealth id 0 := by
  intro wealth
  have hd := (shareValue_hasDerivAt_zero (ExponentialUtility 1) SmallShareLaw wealth id
    (fun i => (exponentialUtility_hasDerivAt 1 _).differentiableAt)).neg
  apply (improves_small_positive hd ?_).mono
  · intro a ha
    exact neg_lt_neg_iff.mp ha
  · rw [SmallShareLaw, expectedUtility_binary]
    simp only [(exponentialUtility_hasDerivAt 1 _).deriv, wealth, id_eq]
    norm_num
    rw [show Real.exp (-2) = (Real.exp 2)⁻¹ by rw [Real.exp_neg]]
    have he : 3 < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two]
    have he' := (div_lt_one (Real.exp_pos 2)).mpr he
    rw [div_eq_mul_inv] at he'
    linarith

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Repeating the gamble with absorption at bankruptcy

Kreps I, Problem 6.14, p. 147. In units of 500 dollars the walk goes up two
with probability 2/5 or down one with probability 3/5, starting at four.
The finite terminal law stops at zero. Geometric test functions bound both
the mass at zero and the mass at small positive wealth.
-/

namespace Kreps.UtilityForMoney

/-- Exact finite terminal wealth law, measured in 500-dollar units, stopped at bankruptcy. -/
noncomputable def StoppedLaw : ℕ → ℕ → SimpleLottery ℕ
  | 0, k => Convexity.StdSimplex.single k
  | _ + 1, 0 => Convexity.StdSimplex.single 0
  | n + 1, k + 1 => TrialBranch (StoppedLaw n (k + 3)) (StoppedLaw n k)

/-- Expected terminal utility at horizon `n` and initial wealth `k` units. -/
noncomputable def StoppedValue (U : ℕ → ℝ) (n k : ℕ) : ℝ := ExpectedUtility U (StoppedLaw n k)

/-- At zero horizon the initial wealth is retained. -/
theorem stoppedValue_initial (U : ℕ → ℝ) (k : ℕ) : StoppedValue U 0 k = U k :=
  expectedUtility_single U k

/-- Bankruptcy is absorbing at every subsequent horizon. -/
theorem stoppedValue_bankrupt (U : ℕ → ℝ) (n : ℕ) : StoppedValue U n 0 = U 0 := by
  cases n <;> exact expectedUtility_single U 0

/-- From positive wealth the next draw has the source's fixed two branch probabilities. -/
theorem stoppedValue_step (U : ℕ → ℝ) (n k : ℕ) :
    StoppedValue U (n + 1) (k + 1) =
      (2 * StoppedValue U n (k + 3) + 3 * StoppedValue U n k) / 5 :=
  trialBranch_value U _ _

/-- Expected-utility evaluation preserves pointwise inequalities. -/
theorem expectedUtility_mono {I : Type*} (p : SimpleLottery I) {f g : I → ℝ}
    (h : ∀ i, f i ≤ g i) : ExpectedUtility f p ≤ ExpectedUtility g p :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (p.nonneg i)

/-- The multiplier for the geometric test `s^k` at positive wealth. -/
noncomputable def WalkFactor (s : ℝ) : ℝ := (2 * s ^ 2 + 3 / s) / 5

/-- A single interior step multiplies the geometric test by its scalar factor. -/
theorem walk_geometric_step {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (2 * s ^ (k + 3) + 3 * s ^ k) / 5 = WalkFactor s * s ^ (k + 1) := by
  rw [pow_add, pow_succ]
  unfold WalkFactor
  field_simp
  ring

/-- A factor below one bounds the stopped geometric moment at every horizon. -/
theorem stopped_power_le {s : ℝ} (hs : 0 < s) (hc : WalkFactor s ≤ 1) (n k : ℕ) :
    StoppedValue (fun j => s ^ j) n k ≤ s ^ k := by
  induction n generalizing k with
  | zero => rw [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => rw [stoppedValue_bankrupt]
    | succ k =>
      rw [stoppedValue_step]
      calc
        _ ≤ (2 * s ^ (k + 3) + 3 * s ^ k) / 5 := by linarith [ih (k + 3), ih k]
        _ = _ := walk_geometric_step hs k
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg hs.le (k + 1))

/-- A factor above one reverses the stopped geometric-moment comparison. -/
theorem stopped_power_ge {s : ℝ} (hs : 0 < s) (hc : 1 ≤ WalkFactor s) (n k : ℕ) :
    s ^ k ≤ StoppedValue (fun j => s ^ j) n k := by
  induction n generalizing k with
  | zero => rw [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => rw [stoppedValue_bankrupt]
    | succ k =>
      rw [stoppedValue_step]
      calc
        _ ≤ WalkFactor s * s ^ (k + 1) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg hs.le (k + 1))
        _ = _ := (walk_geometric_step hs k).symm
        _ ≤ _ := by linarith [ih (k + 3), ih k]

/-- The geometric test restricted to the survival event. -/
noncomputable def AlivePower (s : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else s ^ k

/-- The survival-weighted geometric moment is at most the geometric power of the factor. -/
theorem alivePower_bound {s : ℝ} (hs : 0 < s) (n k : ℕ) :
    StoppedValue (AlivePower s) n k ≤ WalkFactor s ^ n * AlivePower s k := by
  have hfac : 0 ≤ WalkFactor s := by unfold WalkFactor; positivity
  induction n generalizing k with
  | zero => simp [stoppedValue_initial]
  | succ n ih =>
    cases k with
    | zero => simp [stoppedValue_bankrupt, AlivePower]
    | succ k =>
      rw [stoppedValue_step]
      have ha : AlivePower s k ≤ s ^ k := by
        unfold AlivePower
        split
        · positivity
        · exact le_rfl
      have hb : AlivePower s (k + 3) = s ^ (k + 3) := by simp [AlivePower]
      have hbase : AlivePower s (k + 1) = s ^ (k + 1) := by simp [AlivePower]
      have hk := mul_le_mul_of_nonneg_left ha (pow_nonneg hfac n)
      have h := walk_geometric_step hs k
      rw [pow_succ, hbase]
      calc
        _ ≤ WalkFactor s ^ n * ((2 * s ^ (k + 3) + 3 * s ^ k) / 5) := by
          have h₁ := ih (k + 3)
          rw [hb] at h₁
          linarith only [h₁, ih k, hk]
        _ = _ := by rw [h]; ring

/-- The two bounded example utilities strictly increase and have the finite upper bound one. -/
theorem bounded_walk_utility {s : ℝ} (hp : 0 < s) (hl : s < 1) :
    StrictMono (fun k : ℕ => 1 - s ^ k) ∧ ∀ k : ℕ, 1 - s ^ k < 1 :=
  ⟨fun _ _ h => sub_lt_sub_left (pow_lt_pow_right_of_lt_one₀ hp hl h) _,
    fun k => sub_lt_self _ (pow_pos hp k)⟩

/-- **Problem 6.14(b):** two bounded increasing utilities make opposite choices at every horizon. -/
theorem problem_6_14_bounded (n : ℕ) :
    1 - (9 / 10 : ℝ) ^ 4 < StoppedValue (fun k => 1 - (9 / 10 : ℝ) ^ k) (n + 1) 4 ∧
      StoppedValue (fun k => 1 - (1 / 2 : ℝ) ^ k) (n + 1) 4 < 1 - (1 / 2 : ℝ) ^ 4 := by
  have hlin (s : ℝ) : StoppedValue (fun k => 1 - s ^ k) (n + 1) 4 =
      1 - StoppedValue (fun k => s ^ k) (n + 1) 4 := by
    simpa [StoppedValue, sub_eq_add_neg, add_comm] using
      expectedUtility_affine_payoff (StoppedLaw (n + 1) 4) (fun k => s ^ k) (-1) 1
  rw [hlin, hlin, show 4 = 3 + 1 by decide, stoppedValue_step, stoppedValue_step]
  constructor
  · have h := stopped_power_le (by norm_num : (0 : ℝ) < 9 / 10)
      (by norm_num [WalkFactor]) n
    norm_num at *
    linarith [h 6, h 3]
  · have h := stopped_power_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num [WalkFactor]) n
    norm_num at *
    linarith [h 6, h 3]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Growing horizons under the bankruptcy rule

Kreps I, Problem 6.14(a), p. 147. A geometric moment bounds bankruptcy risk. A
second moment, killed at zero, makes the remaining probability of low positive
wealth vanish. This gives an eventual strict gain for every unbounded increasing
utility that is finite at zero, without assuming the utility increases at a
particular rate.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- The finite stopped lottery preserves constants plus two linear payoff terms. -/
theorem stoppedValue_affine_two (n k : ℕ) (f g : ℕ → ℝ) (A B C : ℝ) :
    StoppedValue (fun j => A + B * f j + C * g j) n k =
      A + B * StoppedValue f n k + C * StoppedValue g n k := by
  unfold StoppedValue
  rw [show (fun j => A + B * f j + C * g j) =
    fun j => 1 * (B * f j + C * g j) + A by funext j; ring, expectedUtility_affine_payoff,
    expectedUtility_linear_combination]
  ring

/-- A lower bound on utility in terms of the full and killed geometric moments. -/
theorem stopped_utility_lower (U : ℕ → ℝ) (hm : Monotone U) (M n k : ℕ) :
    let s : ℝ := 9 / 10
    let D := U M - U 0
    U 0 + D * (1 - s ^ k - (WalkFactor s ^ n * AlivePower s k) / s ^ M) ≤
      StoppedValue U n k := by
  intro s D
  have hs : 0 < s := by norm_num [s]
  have hs' : s ≤ 1 := by norm_num [s]
  have hc : WalkFactor s ≤ 1 := by norm_num [WalkFactor, s]
  have hd : 0 ≤ D := sub_nonneg.mpr (hm (Nat.zero_le M))
  have hM : 0 < s ^ M := pow_pos hs M
  have hlo (j : ℕ) : U 0 + D + (-D) * s ^ j + (-(D / s ^ M)) * AlivePower s j ≤ U j := by
    by_cases hj : j = 0
    · subst j
      simp [AlivePower]
    have ha : AlivePower s j = s ^ j := by simp [AlivePower, hj]
    rw [ha]
    have hdv := div_nonneg hd hM.le
    by_cases hcut : M ≤ j
    · have h₁ := mul_nonneg hd (pow_nonneg hs.le j)
      have h₂ := mul_nonneg hdv (pow_nonneg hs.le j)
      dsimp [D] at *
      linarith [hm hcut]
    · have hp := pow_le_pow_of_le_one hs.le hs' (le_of_not_ge hcut)
      have h₁ := mul_le_mul_of_nonneg_left hp hdv
      rw [div_mul_cancel₀ _ hM.ne'] at h₁
      linarith [hm (Nat.zero_le j), mul_nonneg hd (pow_nonneg hs.le j)]
  have he := expectedUtility_mono (StoppedLaw n k) hlo
  change StoppedValue _ n k ≤ StoppedValue U n k at he
  rw [stoppedValue_affine_two] at he
  have h₁ := mul_le_mul_of_nonneg_left (stopped_power_le hs hc n k) hd
  have h₂ := mul_le_mul_of_nonneg_left (alivePower_bound hs n k) (div_nonneg hd hM.le)
  simp only [div_eq_mul_inv] at he h₂ ⊢
  nlinarith only [he, h₁, h₂]

/-- **Problem 6.14(a):** every sufficiently long horizon improves unbounded increasing utility. -/
theorem problem_6_14_unbounded (U : ℕ → ℝ) (hm : StrictMono U) (hu : ∀ v : ℝ, ∃ M, v < U M)
    {k : ℕ} (hk : 0 < k) : ∀ᶠ n : ℕ in atTop, U k < StoppedValue U n k := by
  let s : ℝ := 9 / 10
  have hs : 0 < s := by norm_num [s]
  have hs' : s < 1 := by norm_num [s]
  have hsurv : 0 < 1 - s ^ k := sub_pos.mpr (pow_lt_one₀ hs.le hs' hk.ne')
  obtain ⟨M, hM⟩ := hu (U 0 + (U k - U 0) / (1 - s ^ k))
  let D := U M - U 0
  have ht : U k < U 0 + D * (1 - s ^ k) := by
    have he : (U k - U 0) / (1 - s ^ k) < D := by dsimp [D]; linarith
    linarith [(div_lt_iff₀ hsurv).mp he]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num [WalkFactor, s] : 0 ≤ WalkFactor s)
    (by norm_num [WalkFactor, s] : WalkFactor s < 1)
  have hlim : Tendsto (fun n : ℕ =>
      U 0 + D * (1 - s ^ k - (WalkFactor s ^ n * AlivePower s k) / s ^ M)) atTop
      (𝓝 (U 0 + D * (1 - s ^ k))) := by
    have he := ((hp.mul_const (AlivePower s k)).div_const (s ^ M)).const_sub (1 - s ^ k)
    simpa using (he.const_mul D).const_add (U 0)
  filter_upwards [hlim.eventually (isOpen_Ioi.mem_nhds ht)] with n hn
  exact hn.trans_le (stopped_utility_lower U hm.monotone M n k)

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Limiting bankruptcy probability

Kreps I, Problem 6.14, p. 147. For the walk with increments plus two and minus
one, the positive root below one of the harmonic moment equation is
`(sqrt 7 - 1)/2`. Its stopped moment is constant. The surviving part of that
moment tends to zero, leaving the exact limit of the bankruptcy probability.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- The smaller positive solution of the walk's harmonic moment equation. -/
noncomputable def BankruptcyBase : ℝ := (Real.sqrt 7 - 1) / 2

/-- The harmonic root is positive and lies below the decaying test base 9/10. -/
theorem bankruptcyBase_bounds : 0 < BankruptcyBase ∧ BankruptcyBase < 9 / 10 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hn := Real.sqrt_nonneg 7
  unfold BankruptcyBase
  constructor <;> nlinarith

/-- The geometric moment with the harmonic root has exactly unit drift factor. -/
theorem bankruptcyBase_harmonic : WalkFactor BankruptcyBase = 1 := by
  have hq : 2 * BankruptcyBase ^ 2 + 2 * BankruptcyBase = 3 := by
    unfold BankruptcyBase
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
  have h₁ := congrArg (fun x : ℝ => x * BankruptcyBase) hq
  unfold WalkFactor
  field_simp [bankruptcyBase_bounds.1.ne']
  nlinarith only [hq, h₁]

/-- Indicator of zero terminal wealth. -/
def BankruptcyIndicator (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- The expected indicator is the actual point mass at zero in the terminal wealth law. -/
theorem bankruptcy_mass (n k : ℕ) : StoppedValue BankruptcyIndicator n k =
    (StoppedLaw n k).weights 0 := by
  unfold StoppedValue ExpectedUtility BankruptcyIndicator
  rw [Finsupp.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The harmonic stopped moment splits into the bankruptcy probability and the surviving moment. -/
theorem bankruptcy_probability_identity (n k : ℕ) :
    StoppedValue BankruptcyIndicator n k =
      BankruptcyBase ^ k - StoppedValue (AlivePower BankruptcyBase) n k := by
  have he : StoppedValue (fun j => BankruptcyBase ^ j) n k = BankruptcyBase ^ k :=
    le_antisymm (stopped_power_le bankruptcyBase_bounds.1 bankruptcyBase_harmonic.le n k)
      (stopped_power_ge bankruptcyBase_bounds.1 bankruptcyBase_harmonic.ge n k)
  have hp (j : ℕ) : 0 + 1 * BankruptcyIndicator j + 1 * AlivePower BankruptcyBase j =
      BankruptcyBase ^ j := by
    by_cases hj : j = 0 <;> simp [AlivePower, BankruptcyIndicator, hj]
  have hlin := stoppedValue_affine_two n k BankruptcyIndicator (AlivePower BankruptcyBase) 0 1 1
  rw [funext hp, he] at hlin
  linarith

/-- Every survival-weighted moment up to base 9/10 tends to zero. -/
theorem alivePower_tendsto {q : ℝ} (hq : 0 ≤ q) (hle : q ≤ 9 / 10) (k : ℕ) :
    Tendsto (fun n => StoppedValue (AlivePower q) n k) atTop (𝓝 0) := by
  let s : ℝ := 9 / 10
  have hs : 0 < s := by norm_num [s]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num [s, WalkFactor] : 0 ≤ WalkFactor s)
    (by norm_num [s, WalkFactor] : WalkFactor s < 1)
  have hl (n : ℕ) : 0 ≤ StoppedValue (AlivePower q) n k := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg ((StoppedLaw n k).nonneg i)
    unfold AlivePower
    split
    · exact le_rfl
    · exact pow_nonneg hq _
  apply squeeze_zero hl (fun n => le_trans ?_ (alivePower_bound hs n k))
    (by simpa only [zero_mul] using hp.mul_const (AlivePower s k))
  apply expectedUtility_mono
  intro i
  unfold AlivePower
  split
  · exact le_rfl
  · exact pow_le_pow_left₀ hq hle _

/-- The probability of hitting bankruptcy by the horizon converges to the exact ruin probability. -/
theorem bankruptcy_probability_limit (k : ℕ) :
    Tendsto (fun n => StoppedValue BankruptcyIndicator n k) atTop (𝓝 (BankruptcyBase ^ k)) := by
  simp_rw [bankruptcy_probability_identity]
  simpa only [sub_zero] using (alivePower_tendsto bankruptcyBase_bounds.1.le
    bankruptcyBase_bounds.2.le k).const_sub (BankruptcyBase ^ k)

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A limiting criterion for bounded utility in the stopped gamble

Kreps I, final question of Problem 6.14, p. 147. A bounded increasing utility
tends to its supremum at high wealth. The limiting expected utility is the
bankruptcy value weighted by the ruin probability plus the supremum weighted
by survival. Strict comparison to current utility gives eventual acceptance
or rejection.
-/

namespace Kreps.UtilityForMoney

open Filter Topology

/-- Expected bounded utility cannot exceed the upper utility level on surviving paths. -/
theorem stopped_bounded_upper (U : ℕ → ℝ) {L : ℝ} (hU : ∀ j, U j ≤ L) (n k : ℕ) :
    StoppedValue U n k ≤ L + (U 0 - L) * StoppedValue BankruptcyIndicator n k := by
  have hv (j : ℕ) : U j ≤ (U 0 - L) * BankruptcyIndicator j + L := by
    by_cases hz : j = 0
    · subst j
      simp [BankruptcyIndicator]
    · simpa [BankruptcyIndicator, hz] using hU j
  have he := expectedUtility_mono (StoppedLaw n k) hv
  rw [expectedUtility_affine_payoff] at he
  simpa only [StoppedValue, add_comm] using he

/-- A cutoff lower bound keeps the exact bankruptcy probability; only low positive wealth costs
an error term that vanishes with the horizon. -/
theorem stopped_bounded_lower (U : ℕ → ℝ) (hm : Monotone U) (M n k : ℕ) :
    let s : ℝ := 9 / 10
    U M + (U 0 - U M) * StoppedValue BankruptcyIndicator n k -
        (U M - U 0) / s ^ M * StoppedValue (AlivePower s) n k ≤ StoppedValue U n k := by
  intro s
  have hs : 0 < s := by norm_num [s]
  have hd := sub_nonneg.mpr (hm (Nat.zero_le M))
  have hp : 0 < s ^ M := pow_pos hs M
  have hv (j : ℕ) : U M + (U 0 - U M) * BankruptcyIndicator j +
      (-((U M - U 0) / s ^ M)) * AlivePower s j ≤ U j := by
    by_cases hz : j = 0
    · subst j
      simp [BankruptcyIndicator, AlivePower]
    simp [BankruptcyIndicator, AlivePower, hz]
    by_cases hcut : M ≤ j
    · have hp' := mul_nonneg (div_nonneg hd hp.le) (pow_nonneg hs.le j)
      linarith [hm hcut]
    · have he := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le
        (by norm_num [s] : s ≤ 1) (le_of_not_ge hcut)) (div_nonneg hd hp.le)
      rw [div_mul_cancel₀ _ hp.ne'] at he
      linarith [hm (Nat.zero_le j)]
  have he := expectedUtility_mono (StoppedLaw n k) hv
  change StoppedValue _ n k ≤ StoppedValue U n k at he
  rw [stoppedValue_affine_two, neg_mul] at he
  linarith

/-- The exact limiting expected utility under the stopped independent trials. -/
theorem stopped_bounded_limit (U : ℕ → ℝ) (hm : Monotone U) {L : ℝ}
    (hlim : Tendsto U atTop (𝓝 L)) (k : ℕ) :
    Tendsto (fun n => StoppedValue U n k) atTop (𝓝 (L + (U 0 - L) * BankruptcyBase ^ k)) := by
  have hupper (j : ℕ) : U j ≤ L := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_atTop.2 ⟨j, fun i hi => hm hi⟩)
  have hruin := bankruptcy_probability_limit k
  have hdecay := alivePower_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 10) le_rfl k
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hcut := hlim.add ((hlim.const_sub (U 0)).mul_const (BankruptcyBase ^ k))
    obtain ⟨M, hM⟩ := (hcut.eventually (isOpen_Ioi.mem_nhds ha)).exists
    change a < U M + (U 0 - U M) * BankruptcyBase ^ k at hM
    have hlow := ((hruin.const_mul (U 0 - U M)).const_add (U M)).sub
      (hdecay.const_mul ((U M - U 0) / (9 / 10 : ℝ) ^ M))
    simp only [mul_zero, sub_zero] at hlow
    filter_upwards [hlow.eventually (isOpen_Ioi.mem_nhds hM)] with n hn
    exact hn.trans_le (stopped_bounded_lower U hm M n k)
  · intro b hb
    have hhigh := (hruin.const_mul (U 0 - L)).const_add L
    filter_upwards [hhigh.eventually (isOpen_Iio.mem_nhds hb)] with n hn
    exact (stopped_bounded_upper U hupper n k).trans_lt hn

/-- **Problem 6.14, bounded-utility criterion:** strict comparison to the limiting value
decides the preference for all sufficiently long horizons. -/
theorem stopped_bounded_criterion (U : ℕ → ℝ) (hm : Monotone U) (hb : BddAbove (Set.range U))
    (k : ℕ) :
    let L := ⨆ j, U j
    let e := L + (U 0 - L) * BankruptcyBase ^ k
    (U k < e → ∀ᶠ n : ℕ in atTop, U k < StoppedValue U n k) ∧
    (e < U k → ∀ᶠ n : ℕ in atTop, StoppedValue U n k < U k) := by
  intro L e
  have h := stopped_bounded_limit U hm (tendsto_atTop_ciSup hm hb) k
  exact ⟨fun he => h.eventually (isOpen_Ioi.mem_nhds he),
    fun he => h.eventually (isOpen_Iio.mem_nhds he)⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Committing to a consumption quantity before learning income

Kreps I, Problem 6.7, pp. 142–143. Both prices equal one. Write `w = 1 + x₁`
and `Nᵢ = yᵢ + 2`. Spending the remaining income in state `i` gives
`1 + x₂ = Nᵢ - w`. A single choice of `w` must be feasible in every state.
The logarithmic support inequalities adapt Chapter 3's `LogarithmicSupport`
at commit `f9c357ada1d9965dabd9eec694720ba585faf575`.
-/

namespace Kreps.UtilityForMoney

/-- Feasible precommitments in the shifted variable, including both consumption boundaries. -/
def TimingMenu {n : ℕ} (N : Fin n → ℝ) : Set ℝ :=
  {w | 1 ≤ w ∧ ∀ i, w ≤ N i - 1}

/-- Mean indirect utility at one common first-good commitment in equiprobable states. -/
noncomputable def TimingValue {n : ℕ} (N : Fin n → ℝ) (w : ℝ) : ℝ :=
  ((n : ℝ) * Real.log w + ∑ i, Real.log (N i - w)) / n

/-- Sum of the marginal utilities of precommitting more first-good consumption. -/
noncomputable def TimingMarginal {n : ℕ} (N : Fin n → ℝ) (w : ℝ) : ℝ :=
  (n : ℝ) / w - ∑ i, 1 / (N i - w)

/-- For fixed first consumption, greater second consumption strictly increases bundle utility. -/
theorem spending_remainder_optimal {y x z : ℝ} (hz : 0 ≤ z) (hslack : x + z < y) :
    Real.log (x + 1) + Real.log (z + 1) < Real.log (x + 1) + Real.log (y - x + 1) := by
  have hg := Real.log_lt_log (by linarith : 0 < z + 1) (by linarith : z + 1 < y - x + 1)
  linarith

/-- Log utility lies below its tangent at every positive consumption. -/
theorem timing_log_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log z - Real.log x ≤ (z - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz hx)
  rw [Real.log_div hz.ne' hx.ne'] at h
  convert h using 1
  field_simp

/-- The tangent bound is strict for a different positive consumption. -/
theorem timing_log_tangent_strict {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (hn : z ≠ x) :
    Real.log z - Real.log x < (z - x) / x := by
  have h := Real.log_lt_sub_one_of_pos (div_pos hz hx)
    (fun h => hn ((div_eq_one_iff_eq hx.ne').mp h))
  rw [Real.log_div hz.ne' hx.ne'] at h
  convert h using 1
  field_simp

/-- A feasible zero marginal is the unique global optimum among common commitments. -/
theorem timing_unique_of_marginal {n : ℕ} (hn : 0 < n) (N : Fin n → ℝ) {w : ℝ}
    (hw : w ∈ TimingMenu N) (hopt : TimingMarginal N w = 0) {z : ℝ}
    (hz : z ∈ TimingMenu N) (hne : z ≠ w) : TimingValue N z < TimingValue N w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfst := timing_log_tangent_strict (zero_lt_one.trans_le hw.1)
    (zero_lt_one.trans_le hz.1) hne
  have hsnd : ∑ i, (Real.log (N i - z) - Real.log (N i - w)) ≤
      (w - z) * ∑ i, 1 / (N i - w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hp := timing_log_tangent (by linarith [hw.2 i] : 0 < N i - w)
      (by linarith [hz.2 i] : 0 < N i - z)
    convert hp using 1
    ring
  have he : ∑ i, 1 / (N i - w) = (n : ℝ) / w := (sub_eq_zero.mp hopt).symm
  rw [Finset.sum_sub_distrib, he] at hsnd
  have heq : (n : ℝ) * ((z - w) / w) + (w - z) * (n / w) = 0 := by ring
  unfold TimingValue
  apply (div_lt_div_iff_of_pos_right hn').mpr
  linarith only [hsnd, mul_lt_mul_of_pos_left hfst hn', heq]

/-- The two shifted incomes for the source's equal lottery over 98 and 178. -/
def TimingTwo : Fin 2 → ℝ := ![100, 180]

/-- The sure income is the printed finite decimal, interpreted exactly. -/
def TimingSure : Fin 1 → ℝ := fun _ => 128.948391819

/-- The three shifted incomes, with equal probabilities. -/
def TimingThree : Fin 3 → ℝ := ![100, 180, 128.948391819]

/-- The common commitment in the binary lottery is exactly 59 units of the first good. -/
theorem timing_two_optimum :
    (60 : ℝ) ∈ TimingMenu TimingTwo ∧
      ∀ z ∈ TimingMenu TimingTwo, z ≠ 60 → TimingValue TimingTwo z < TimingValue TimingTwo 60 := by
  have h : (60 : ℝ) ∈ TimingMenu TimingTwo :=
    ⟨by norm_num, fun i => by fin_cases i <;> norm_num [TimingTwo]⟩
  exact ⟨h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h
    (by norm_num [TimingMarginal, TimingTwo, Fin.sum_univ_two]) hz hn⟩

/-- The certain-income commitment is 63.4741959095 units of the first good. -/
theorem timing_sure_optimum :
    (64.4741959095 : ℝ) ∈ TimingMenu TimingSure ∧ ∀ z ∈ TimingMenu TimingSure,
      z ≠ 64.4741959095 → TimingValue TimingSure z < TimingValue TimingSure 64.4741959095 := by
  have h : (64.4741959095 : ℝ) ∈ TimingMenu TimingSure :=
    ⟨by norm_num, fun _ => by norm_num [TimingSure]⟩
  exact ⟨h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h
    (by norm_num [TimingMarginal, TimingSure, Fin.sum_univ_one]) hz hn⟩

/-- The three-state first-order condition has a root inside the certified decimal bracket. -/
theorem timing_three_root : ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610,
    TimingMarginal TimingThree w = 0 := by
  have hc : ContinuousOn (TimingMarginal TimingThree) (Set.Icc 61.2389938609 61.2389938610) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div continuousOn_id fun x hx => by linarith [hx.1]
    · apply continuousOn_finsetSum
      intro i _
      apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      intro x hx
      fin_cases i <;> norm_num [TimingThree] <;> linarith [hx.2]
  apply intermediate_value_Icc' (by norm_num) hc
  constructor <;> norm_num [TimingMarginal, TimingThree, Fin.sum_univ_succ]

/-- Every distinct feasible precommitment is worse than the three-state root. -/
theorem timing_three_optimum : ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610,
    w ∈ TimingMenu TimingThree ∧ ∀ z ∈ TimingMenu TimingThree,
      z ≠ w → TimingValue TimingThree z < TimingValue TimingThree w := by
  obtain ⟨w, hbounds, hw⟩ := timing_three_root
  have h : w ∈ TimingMenu TimingThree := by
    refine ⟨by linarith [hbounds.1], fun i => ?_⟩
    fin_cases i <;> norm_num [TimingThree] <;> linarith [hbounds.2]
  exact ⟨w, hbounds, h, fun _ hz hn => timing_unique_of_marginal (by decide) _ h hw hz hn⟩

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Certified numerical optimum values for precommitted consumption

Kreps I, Problem 6.7, pp. 142–143. Combine logarithms into the log of a positive
product. Rescale each product by a power of two and apply the fourth-order
logarithm remainder bound and Mathlib's rational bounds on log two. The
three-state product is enclosed throughout the proven narrow optimizer interval.
-/

namespace Kreps.UtilityForMoney

/-- At feasible positive consumptions, combine the statewise logs into one product. -/
theorem timingValue_eq_log_product {n : ℕ} (N : Fin n → ℝ) {w : ℝ} (hw : w ∈ TimingMenu N) :
    TimingValue N w = Real.log (w ^ n * ∏ i, (N i - w)) / n := by
  have hp : 0 < w := zero_lt_one.trans_le hw.1
  have hpos (i) : 0 < N i - w := by linarith [hw.2 i]
  rw [TimingValue, Real.log_mul (pow_ne_zero _ hp.ne') (Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hpos i).ne')), Real.log_pow, Real.log_prod (fun i _ => (hpos i).ne')]

/-- Rescaling a logarithm by a power of two gives an explicit finite Taylor error certificate. -/
theorem timing_log_certificate (k : ℕ) (p : ℝ) (hp : 0 < p)
    (h : |1 - p / 2 ^ k| < 1) :
    |(∑ i ∈ Finset.range 4, (1 - p / 2 ^ k) ^ (i + 1) / (i + 1)) +
      (Real.log p - (k : ℝ) * Real.log 2)| ≤ |1 - p / 2 ^ k| ^ 5 / (1 - |1 - p / 2 ^ k|) := by
  have he := Real.abs_log_sub_add_sum_range_le h 4
  rwa [sub_sub_cancel, Real.log_div hp.ne' (by positivity), Real.log_pow] at he

/-- Binary-income optimum utility rounds to 8.3325 to four places. -/
theorem timing_two_value_bounds :
    8.33252 < TimingValue TimingTwo 60 ∧ TimingValue TimingTwo 60 < 8.33254 := by
  rw [timingValue_eq_log_product TimingTwo timing_two_optimum.1]
  norm_num [TimingTwo, Fin.prod_univ_two]
  have he := timing_log_certificate 24 17280000 (by norm_num) (by norm_num)
  rw [abs_le] at he
  norm_num [Finset.sum_range_succ] at he
  constructor <;> linarith [he.1, he.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Certain-income optimum utility also rounds to 8.3325 to four places. -/
theorem timing_sure_value_bounds :
    8.33252 < TimingValue TimingSure 64.4741959095 ∧
      TimingValue TimingSure 64.4741959095 < 8.33254 := by
  rw [timingValue_eq_log_product TimingSure timing_sure_optimum.1]
  have he := timing_log_certificate 12 (64.4741959095 ^ 2) (by norm_num) (by norm_num)
  rw [abs_le] at he
  norm_num [Finset.sum_range_succ] at he
  norm_num [TimingSure, Fin.prod_univ_one]
  constructor <;> linarith [he.1, he.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The three-state log-product lies within these rational bounds throughout the root bracket. -/
theorem timing_three_product_bounds {w : ℝ}
    (hw : w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610) :
    71581699040 ≤ w ^ 3 * ∏ i, (TimingThree i - w) ∧
      w ^ 3 * ∏ i, (TimingThree i - w) ≤ 71581699060 := by
  let L : ℝ := 61.2389938609
  let H : ℝ := 61.2389938610
  have hlo : L ≤ w := hw.1
  have hhi : w ≤ H := hw.2
  have hpos : 0 ≤ w := by linarith [hw.1]
  have h₁ : 0 ≤ 100 - w := by linarith [hw.2]
  have h₂ : 0 ≤ 180 - w := by linarith [hw.2]
  have h₃ : 0 ≤ 128.948391819 - w := by linarith [hw.2]
  have h₄ := mul_nonneg (mul_nonneg h₁ h₂) h₃
  simp only [Fin.prod_univ_three, TimingThree, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  constructor
  · calc
      71581699040 ≤ L ^ 3 * ((100 - H) * (180 - H) * (128.948391819 - H)) := by norm_num [L, H]
      _ ≤ _ := by gcongr
  · calc
      _ ≤ H ^ 3 * ((100 - L) * (180 - L) * (128.948391819 - L)) := by
        gcongr
      _ ≤ 71581699060 := by norm_num [L, H]

/-- The maximal three-state utility rounds to 8.3314 to four places. -/
theorem timing_three_value_bounds {w : ℝ}
    (hw : w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610) (hm : w ∈ TimingMenu TimingThree) :
    8.33136 < TimingValue TimingThree w ∧ TimingValue TimingThree w < 8.33138 := by
  obtain ⟨hl, hu⟩ := timing_three_product_bounds hw
  have hL := timing_log_certificate 36 71581699040 (by norm_num) (by norm_num)
  have hU := timing_log_certificate 36 71581699060 (by norm_num) (by norm_num)
  rw [abs_le] at hL hU
  norm_num [Finset.sum_range_succ] at hL hU
  rw [timingValue_eq_log_product TimingThree hm]
  norm_num only [Nat.cast_ofNat]
  have hlogL := Real.log_le_log (by norm_num : (0 : ℝ) < 71581699040) hl
  have hlogU := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 71581699040) hl) hu
  constructor <;> linarith [hL.1, hU.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Why income lotteries fail the expected-utility test under precommitment

Kreps I, Problem 6.7, pp. 142–143. The three-state income lottery is a mixture of
the two-state lottery and the sure income. Their respective optimal commitments
differ. The mixed optimal value is strictly below both component optima, even
though every fixed commitment is evaluated by expected utility of final bundles.
-/

namespace Kreps.UtilityForMoney

/-- The printed binary lottery over incomes. -/
noncomputable def TimingIncomeTwo : SimpleLottery ℝ :=
  BinaryLottery 98 178 (1 / 2) (by norm_num)

/-- The printed certain income. -/
noncomputable def TimingIncomeSure : SimpleLottery ℝ := Convexity.StdSimplex.single 126.948391819

/-- The two-thirds/one-third mixture gives probability one third to each income. -/
noncomputable def TimingIncomeThree : SimpleLottery ℝ :=
  LotteryTheory.Mix ⟨2 / 3, by norm_num⟩ TimingIncomeTwo TimingIncomeSure

/-- Holding the first choice fixed gives the bundle utility in the realized income state. -/
noncomputable def TimingBundleIndex (w y : ℝ) : ℝ := Real.log w + Real.log (y + 2 - w)

/-- Any income index evaluates the ternary lottery as the specified mixture of components. -/
theorem timing_income_mixture_value (U : ℝ → ℝ) :
    ExpectedUtility U TimingIncomeThree =
      (2 * ExpectedUtility U TimingIncomeTwo + ExpectedUtility U TimingIncomeSure) / 3 := by
  have he := LotteryTheory.expectedUtility_affine U
    (⟨2 / 3, by norm_num⟩ : LotteryTheory.Weight) TimingIncomeTwo TimingIncomeSure
  change ExpectedUtility U TimingIncomeThree =
    2 / 3 * ExpectedUtility U TimingIncomeTwo +
      (1 - 2 / 3) * ExpectedUtility U TimingIncomeSure at he
  rw [he]
  ring

/-- Each committed-consumption objective is exactly expected utility over realized bundles. -/
theorem timing_values_as_expectations (w : ℝ) :
    ExpectedUtility (TimingBundleIndex w) TimingIncomeTwo = TimingValue TimingTwo w ∧
    ExpectedUtility (TimingBundleIndex w) TimingIncomeSure = TimingValue TimingSure w ∧
    ExpectedUtility (TimingBundleIndex w) TimingIncomeThree = TimingValue TimingThree w := by
  have h₂ : ExpectedUtility (TimingBundleIndex w) TimingIncomeTwo = TimingValue TimingTwo w := by
    rw [TimingIncomeTwo, expectedUtility_binary]
    norm_num [TimingBundleIndex, TimingValue, TimingTwo, Fin.sum_univ_two]
    ring
  have h₁ : ExpectedUtility (TimingBundleIndex w) TimingIncomeSure = TimingValue TimingSure w := by
    rw [TimingIncomeSure, expectedUtility_single]
    norm_num [TimingBundleIndex, TimingValue, TimingSure]
  refine ⟨h₂, h₁, ?_⟩
  rw [timing_income_mixture_value, h₂, h₁]
  norm_num [TimingValue, TimingThree, TimingTwo, TimingSure, Fin.sum_univ_succ]
  ring

/-- The ternary optimum is below both component optima when first consumption is committed. -/
theorem timing_optimized_mixture_worse :
    ∃ w ∈ Set.Icc (61.2389938609 : ℝ) 61.2389938610, w ∈ TimingMenu TimingThree ∧
      (∀ z ∈ TimingMenu TimingThree, z ≠ w →
        TimingValue TimingThree z < TimingValue TimingThree w) ∧
      TimingValue TimingThree w < TimingValue TimingTwo 60 ∧
      TimingValue TimingThree w < TimingValue TimingSure 64.4741959095 := by
  obtain ⟨w, hI, hm, hw⟩ := timing_three_optimum
  have he := (timing_three_value_bounds hI hm).2
  exact ⟨w, hI, hm, hw, by linarith [timing_two_value_bounds.1],
    by linarith [timing_sure_value_bounds.1]⟩

/-- **Problem 6.7:** no expected-utility index over incomes can have both optimized comparisons. -/
theorem problem_6_7_no_income_index : ¬∃ U : ℝ → ℝ,
    ExpectedUtility U TimingIncomeThree < ExpectedUtility U TimingIncomeTwo ∧
    ExpectedUtility U TimingIncomeThree < ExpectedUtility U TimingIncomeSure := by
  rintro ⟨U, h₂, h₁⟩
  linarith [timing_income_mixture_value U]

end Kreps.UtilityForMoney

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Changing finite supports and uniformly bounded utilities

Kreps I, footnote 2, p. 124. Outside the limiting lottery's finite support,
the total probability vanishes. A single bound on the utilities of all extra
prizes makes their combined contribution vanish, even when infinitely many
different prizes occur through the sequence.
-/

namespace Kreps.UtilityForMoney

open Filter
open scoped Topology

/-- A limiting prize with positive mass eventually belongs to every approximating support. -/
theorem eventually_mem_lottery_support {X : Type*} (p : SimpleLottery X) (q : ℕ → SimpleLottery X)
    {x : X} (hx : x ∈ p.weights.support)
    (hw : Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x))) :
    ∀ᶠ n in atTop, x ∈ (q n).weights.support := by
  have hp : 0 < p.weights x := lt_of_le_of_ne (p.nonneg x) (Finsupp.mem_support_iff.mp hx).symm
  filter_upwards [hw.eventually (lt_mem_nhds hp)] with n hn
  exact Finsupp.mem_support_iff.mpr hn.ne'

/-- The portion outside any finite set is bounded by its probability times the utility bound. -/
theorem outside_prize_bound {X : Type*} (U : X → ℝ) (p : SimpleLottery X) (T : Finset X)
    (M : ℝ) (hM : ∀ x ∈ p.weights.support, x ∉ T → |U x| ≤ M) :
    |ExpectedUtility U p - ∑ x ∈ T, p.weights x * U x| ≤
      M * (1 - ∑ x ∈ T, p.weights x) := by
  classical
  let D := T ∪ p.weights.support
  have hsub : T ⊆ D := Finset.subset_union_left
  have hsplit (f : X → ℝ) :
      ExpectedUtility f p - ∑ x ∈ T, p.weights x * f x =
        ∑ x ∈ D \ T, p.weights x * f x := by
    rw [expectedUtility_sum_over f p D Finset.subset_union_right]
    have h := Finset.sum_sdiff (f := fun x => p.weights x * f x) hsub
    linarith
  have mass : (∑ x ∈ D \ T, p.weights x) = 1 - ∑ x ∈ T, p.weights x := by
    have h := hsplit (fun _ => 1)
    simpa only [ExpectedUtility, mul_one, p.total] using h.symm
  rw [hsplit, ← mass, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  refine Finset.sum_le_sum fun x hx => ?_
  obtain ⟨hxD, hn⟩ := Finset.mem_sdiff.mp hx
  have hp := (Finset.mem_union.mp hxD).resolve_left hn
  simpa only [abs_mul, abs_of_nonneg (p.nonneg x), mul_comm M] using
    (show |p.weights x * U x| ≤ p.weights x * M by
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hM x hp hn) (p.nonneg x))

/-- Coordinate convergence on the limiting support and bounded extra prizes imply EU convergence. -/
theorem expectedUtility_tendsto_bounded_extra_prizes {X : Type*} (U : X → ℝ)
    (p : SimpleLottery X) (q : ℕ → SimpleLottery X)
    (hw : ∀ x ∈ p.weights.support, Tendsto (fun n => (q n).weights x) atTop (𝓝 (p.weights x)))
    (M : ℝ) (hM : ∀ n x, x ∈ (q n).weights.support → x ∉ p.weights.support → |U x| ≤ M) :
    Tendsto (fun n => ExpectedUtility U (q n)) atTop (𝓝 (ExpectedUtility U p)) := by
  let T := p.weights.support
  have mass : Tendsto (fun n => ∑ x ∈ T, (q n).weights x) atTop (𝓝 1) := by
    rw [← p.total]
    exact tendsto_finsetSum T (fun x hx => hw x hx)
  have core : Tendsto (fun n => ∑ x ∈ T, (q n).weights x * U x) atTop
      (𝓝 (ExpectedUtility U p)) := tendsto_finsetSum T fun x hx => (hw x hx).mul_const _
  have tail : Tendsto (fun n => ExpectedUtility U (q n) - ∑ x ∈ T, (q n).weights x * U x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => outside_prize_bound U (q n) T M (hM n))
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub mass).const_mul M
  simpa only [sub_add_cancel, zero_add] using tail.add core

end Kreps.UtilityForMoney

set_option linter.style.longLine false
#print axioms Kreps.UtilityForMoney.SimpleLottery
#print axioms Kreps.UtilityForMoney.ExpectedUtility
#print axioms Kreps.UtilityForMoney.BinaryLottery
#print axioms Kreps.UtilityForMoney.expectedUtility_eq_affine
#print axioms Kreps.UtilityForMoney.expectedUtility_single
#print axioms Kreps.UtilityForMoney.expectedUtility_binary
#print axioms Kreps.UtilityForMoney.proposition_6_1
#print axioms Kreps.UtilityForMoney.exists_lottery_of_between
#print axioms Kreps.UtilityForMoney.expectedUtility_mem_of_convex
#print axioms Kreps.UtilityForMoney.expectedUtility_jensen
#print axioms Kreps.UtilityForMoney.proposition_6_3
#print axioms Kreps.UtilityForMoney.IsCertaintyEquivalent
#print axioms Kreps.UtilityForMoney.proposition_6_5_exists
#print axioms Kreps.UtilityForMoney.proposition_6_5_unique
#print axioms Kreps.UtilityForMoney.RiskPremium
#print axioms Kreps.UtilityForMoney.riskPremium_nonneg
#print axioms Kreps.UtilityForMoney.MoreRiskAverse
#print axioms Kreps.UtilityForMoney.UtilityTransform
#print axioms Kreps.UtilityForMoney.utilityTransform_apply
#print axioms Kreps.UtilityForMoney.utilityTransform_strictMonoOn
#print axioms Kreps.UtilityForMoney.proposition_6_7
#print axioms Kreps.UtilityForMoney.AbsoluteRiskAversion
#print axioms Kreps.UtilityForMoney.RelativeRiskAversion
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_nonneg
#print axioms Kreps.UtilityForMoney.PowerUtility
#print axioms Kreps.UtilityForMoney.powerUtility_hasDerivAt
#print axioms Kreps.UtilityForMoney.powerUtility_second_deriv
#print axioms Kreps.UtilityForMoney.problem_6_4
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_affine
#print axioms Kreps.UtilityForMoney.InsuranceUtility
#print axioms Kreps.UtilityForMoney.insuranceUtility_one
#print axioms Kreps.UtilityForMoney.insuranceUtility_le_mean
#print axioms Kreps.UtilityForMoney.proposition_6_17a
#print axioms Kreps.UtilityForMoney.deriv_pos_of_concave_strictMono
#print axioms Kreps.UtilityForMoney.insuranceUtility_hasDerivAt_one
#print axioms Kreps.UtilityForMoney.proposition_6_17b
#print axioms Kreps.UtilityForMoney.expectedUtility_affine_payoff
#print axioms Kreps.UtilityForMoney.expectedUtility_const
#print axioms Kreps.UtilityForMoney.PortfolioWealth
#print axioms Kreps.UtilityForMoney.PortfolioValue
#print axioms Kreps.UtilityForMoney.PortfolioOptima
#print axioms Kreps.UtilityForMoney.expected_portfolioWealth
#print axioms Kreps.UtilityForMoney.portfolioValue_zero
#print axioms Kreps.UtilityForMoney.portfolioValue_le_mean
#print axioms Kreps.UtilityForMoney.proposition_6_18b
#print axioms Kreps.UtilityForMoney.proposition_6_18a
#print axioms Kreps.UtilityForMoney.portfolioValue_hasDerivAt_zero
#print axioms Kreps.UtilityForMoney.improves_small_positive
#print axioms Kreps.UtilityForMoney.proposition_6_18c
#print axioms Kreps.UtilityForMoney.MarginalRatio
#print axioms Kreps.UtilityForMoney.antitoneOn_marginalRatio
#print axioms Kreps.UtilityForMoney.utility_le_marginalRatio_support
#print axioms Kreps.UtilityForMoney.moreRiskAverse_of_arrowPratt
#print axioms Kreps.UtilityForMoney.local_second_order_remainder
#print axioms Kreps.UtilityForMoney.SymmetricUtility
#print axioms Kreps.UtilityForMoney.symmetricUtility_remainder
#print axioms Kreps.UtilityForMoney.symmetricUtility_quotient
#print axioms Kreps.UtilityForMoney.symmetric_premium_of_certainty_equivalent
#print axioms Kreps.UtilityForMoney.proposition_6_9
#print axioms Kreps.UtilityForMoney.arrowPratt_le_of_moreRiskAverse_interior
#print axioms Kreps.UtilityForMoney.proposition_6_8
#print axioms Kreps.UtilityForMoney.PremiumOrder
#print axioms Kreps.UtilityForMoney.premiumOrder_iff_moreRiskAverse
#print axioms Kreps.UtilityForMoney.ShiftDomain
#print axioms Kreps.UtilityForMoney.shiftDomain_convex
#print axioms Kreps.UtilityForMoney.ShiftPremiumOrder
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_shift
#print axioms Kreps.UtilityForMoney.shiftPremiumOrder_iff
#print axioms Kreps.UtilityForMoney.shiftPremiumOrder_of_coefficient
#print axioms Kreps.UtilityForMoney.coefficient_le_of_shiftPremiumOrder
#print axioms Kreps.UtilityForMoney.monotoneOn_interval_of_interior
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_continuousOn
#print axioms Kreps.UtilityForMoney.NonincreasingRiskAversion
#print axioms Kreps.UtilityForMoney.NondecreasingRiskAversion
#print axioms Kreps.UtilityForMoney.ConstantRiskAversion
#print axioms Kreps.UtilityForMoney.proposition_6_12_nondecreasing
#print axioms Kreps.UtilityForMoney.proposition_6_12_nonincreasing
#print axioms Kreps.UtilityForMoney.proposition_6_12_constant
#print axioms Kreps.UtilityForMoney.ExponentialUtility
#print axioms Kreps.UtilityForMoney.exponentialUtility_hasDerivAt
#print axioms Kreps.UtilityForMoney.exponentialUtility_strictMono
#print axioms Kreps.UtilityForMoney.exponentialUtility_strictConcave
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_exponential
#print axioms Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero
#print axioms Kreps.UtilityForMoney.marginal_of_constant_coefficient
#print axioms Kreps.UtilityForMoney.proposition_6_12_exponential
#print axioms Kreps.UtilityForMoney.proposition_6_12_affine
#print axioms Kreps.UtilityForMoney.CalibrationGap
#print axioms Kreps.UtilityForMoney.calibrationGap_identity
#print axioms Kreps.UtilityForMoney.calibrationGap_monotone
#print axioms Kreps.UtilityForMoney.calibration_bounds
#print axioms Kreps.UtilityForMoney.calibrated_root_exists
#print axioms Kreps.UtilityForMoney.calibrated_disutility_rankings
#print axioms Kreps.UtilityForMoney.CalibratedChoicesRanked
#print axioms Kreps.UtilityForMoney.exponential_calibration_prizes
#print axioms Kreps.UtilityForMoney.problem_6_2
#print axioms Kreps.UtilityForMoney.CalibrationInterval
#print axioms Kreps.UtilityForMoney.problem_6_2_behavioral
#print axioms Kreps.UtilityForMoney.problem_6_2_compatible_consumer
#print axioms Kreps.UtilityForMoney.certaintyEquivalent_of_equal_premia
#print axioms Kreps.UtilityForMoney.calibration_shift_affine
#print axioms Kreps.UtilityForMoney.calibrated_grid_ranking
#print axioms Kreps.UtilityForMoney.problem_6_2_of_constant_premia
#print axioms Kreps.UtilityForMoney.portfolioValue_affine
#print axioms Kreps.UtilityForMoney.proposition_6_18d
#print axioms Kreps.UtilityForMoney.expectedUtility_lt_of_support
#print axioms Kreps.UtilityForMoney.proposition_6_18e
#print axioms Kreps.UtilityForMoney.expectedUtility_linear_combination
#print axioms Kreps.UtilityForMoney.portfolioValue_strictConcave
#print axioms Kreps.UtilityForMoney.proposition_6_18f
#print axioms Kreps.UtilityForMoney.cara_unit_value
#print axioms Kreps.UtilityForMoney.cara_portfolio_factor
#print axioms Kreps.UtilityForMoney.cara_unit_attains
#print axioms Kreps.UtilityForMoney.cara_optima_scale
#print axioms Kreps.UtilityForMoney.problem_6_11
#print axioms Kreps.UtilityForMoney.cara_position_antitone
#print axioms Kreps.UtilityForMoney.support_mass_sum
#print axioms Kreps.UtilityForMoney.lottery_support_nonempty
#print axioms Kreps.UtilityForMoney.FiniteCoupling
#print axioms Kreps.UtilityForMoney.FiniteCoupling.mk
#print axioms Kreps.UtilityForMoney.FiniteCoupling.mass
#print axioms Kreps.UtilityForMoney.FiniteCoupling.nonneg
#print axioms Kreps.UtilityForMoney.FiniteCoupling.row_sum
#print axioms Kreps.UtilityForMoney.FiniteCoupling.col_sum
#print axioms Kreps.UtilityForMoney.FiniteCoupling.NonpositiveDrift
#print axioms Kreps.UtilityForMoney.FiniteCoupling.conditionalDrift
#print axioms Kreps.UtilityForMoney.FiniteCoupling.nonpositiveDrift_iff
#print axioms Kreps.UtilityForMoney.FiniteCoupling.jointLaw
#print axioms Kreps.UtilityForMoney.FiniteCoupling.first_marginal
#print axioms Kreps.UtilityForMoney.FiniteCoupling.second_marginal
#print axioms Kreps.UtilityForMoney.CouplingMoments
#print axioms Kreps.UtilityForMoney.RowDirection
#print axioms Kreps.UtilityForMoney.ColumnDirection
#print axioms Kreps.UtilityForMoney.DriftDirection
#print axioms Kreps.UtilityForMoney.PairMoments
#print axioms Kreps.UtilityForMoney.momentSum_fst
#print axioms Kreps.UtilityForMoney.momentSum_snd
#print axioms Kreps.UtilityForMoney.pairMoments_evaluate
#print axioms Kreps.UtilityForMoney.marginal_functional
#print axioms Kreps.UtilityForMoney.coupling_or_separation
#print axioms Kreps.UtilityForMoney.DominanceTools.FiniteMinimum
#print axioms Kreps.UtilityForMoney.DominanceTools.finiteMinimum_le
#print axioms Kreps.UtilityForMoney.DominanceTools.le_finiteMinimum
#print axioms Kreps.UtilityForMoney.DominanceTools.finiteMinimum_attained
#print axioms Kreps.UtilityForMoney.DominanceTools.finiteMinimum_continuous
#print axioms Kreps.UtilityForMoney.DominanceTools.finiteMinimum_strictMono
#print axioms Kreps.UtilityForMoney.DominanceTools.finiteMinimum_concaveOn
#print axioms Kreps.UtilityForMoney.FirstOrderDominates
#print axioms Kreps.UtilityForMoney.SecondOrderDominates
#print axioms Kreps.UtilityForMoney.Cumulative
#print axioms Kreps.UtilityForMoney.ExpectedShortfall
#print axioms Kreps.UtilityForMoney.FirstOrderDominates.secondOrder
#print axioms Kreps.UtilityForMoney.cumulative_le_of_firstOrder
#print axioms Kreps.UtilityForMoney.cappedPrizeUtility_properties
#print axioms Kreps.UtilityForMoney.expectedShortfall_le_of_secondOrder
#print axioms Kreps.UtilityForMoney.increasing_concave_envelope
#print axioms Kreps.UtilityForMoney.sum_support_utility
#print axioms Kreps.UtilityForMoney.supermartingaleCoupling_of_dominance
#print axioms Kreps.UtilityForMoney.FiniteCoupling.row_utility_le
#print axioms Kreps.UtilityForMoney.secondOrder_of_supermartingaleCoupling
#print axioms Kreps.UtilityForMoney.proposition_6_15b
#print axioms Kreps.UtilityForMoney.Demand.Complete
#print axioms Kreps.UtilityForMoney.Demand.TransitivePref
#print axioms Kreps.UtilityForMoney.Demand.Rational
#print axioms Kreps.UtilityForMoney.Demand.PrefChoice
#print axioms Kreps.UtilityForMoney.Demand.UtilityPref
#print axioms Kreps.UtilityForMoney.Demand.Represents
#print axioms Kreps.UtilityForMoney.Demand.Strict
#print axioms Kreps.UtilityForMoney.Demand.Indifferent
#print axioms Kreps.UtilityForMoney.Demand.utilityPref_rational
#print axioms Kreps.UtilityForMoney.Demand.NonnegativeOrthant
#print axioms Kreps.UtilityForMoney.Demand.LocallyInsatiable
#print axioms Kreps.UtilityForMoney.Demand.Mix
#print axioms Kreps.UtilityForMoney.Demand.ConvexMenu
#print axioms Kreps.UtilityForMoney.Demand.ConvexPreference
#print axioms Kreps.UtilityForMoney.Demand.StrictlyConvexPreference
#print axioms Kreps.UtilityForMoney.Demand.ConcaveUtility
#print axioms Kreps.UtilityForMoney.Demand.QuasiConcaveUtility
#print axioms Kreps.UtilityForMoney.Demand.StrictlyQuasiConcaveUtility
#print axioms Kreps.UtilityForMoney.Demand.PositivePrices
#print axioms Kreps.UtilityForMoney.Demand.ZeroBundle
#print axioms Kreps.UtilityForMoney.Demand.Expenditure
#print axioms Kreps.UtilityForMoney.Demand.BudgetSet
#print axioms Kreps.UtilityForMoney.Demand.expenditure_zero
#print axioms Kreps.UtilityForMoney.Demand.expenditure_nonneg
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_nonempty
#print axioms Kreps.UtilityForMoney.Demand.commodity_expenditure_le
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_coordinate_bound
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_zero
#print axioms Kreps.UtilityForMoney.Demand.expenditure_continuous
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_isClosed
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_isCompact
#print axioms Kreps.UtilityForMoney.Demand.expenditure_mix
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_convex
#print axioms Kreps.UtilityForMoney.Demand.ScalePrices
#print axioms Kreps.UtilityForMoney.Demand.expenditure_scalePrices
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_scale
#print axioms Kreps.UtilityForMoney.Demand.SequentialUpper
#print axioms Kreps.UtilityForMoney.Demand.SequentialLower
#print axioms Kreps.UtilityForMoney.Demand.ParametricMaxima
#print axioms Kreps.UtilityForMoney.Demand.parametricMaxima_nonempty
#print axioms Kreps.UtilityForMoney.Demand.parametricMaxima_sequentialUpper
#print axioms Kreps.UtilityForMoney.Demand.sequentialUpper_upperHemicontinuousAt
#print axioms Kreps.UtilityForMoney.Demand.sequentialLower_of_continuous_selections
#print axioms Kreps.UtilityForMoney.Demand.LocalCompactBound
#print axioms Kreps.UtilityForMoney.Demand.ParametricValue
#print axioms Kreps.UtilityForMoney.Demand.parametricValue_eq_of_maximum
#print axioms Kreps.UtilityForMoney.Demand.parametricValue_continuous
#print axioms Kreps.UtilityForMoney.Demand.LocalCompactBound.mono
#print axioms Kreps.UtilityForMoney.Demand.SequentialUpper.isClosed
#print axioms Kreps.UtilityForMoney.Demand.SequentialUpper.isCompact
#print axioms Kreps.UtilityForMoney.Demand.continuous_of_singleton_correspondence
#print axioms Kreps.UtilityForMoney.Demand.SameObjectiveUpperBounds
#print axioms Kreps.UtilityForMoney.Demand.maximum_theorem_auxiliary
#print axioms Kreps.UtilityForMoney.Demand.maximum_theorem
#print axioms Kreps.UtilityForMoney.Demand.sameObjectiveUpperBounds_iff_value_eq
#print axioms Kreps.UtilityForMoney.Demand.PriceIncome
#print axioms Kreps.UtilityForMoney.Demand.ScaleBundle
#print axioms Kreps.UtilityForMoney.Demand.scaleBundle_zero
#print axioms Kreps.UtilityForMoney.Demand.scaleBundle_one
#print axioms Kreps.UtilityForMoney.Demand.expenditure_scaleBundle
#print axioms Kreps.UtilityForMoney.Demand.expenditure_pos
#print axioms Kreps.UtilityForMoney.Demand.expenditure_price_continuous
#print axioms Kreps.UtilityForMoney.Demand.expenditure_joint_continuous
#print axioms Kreps.UtilityForMoney.Demand.BudgetAdjustmentFactor
#print axioms Kreps.UtilityForMoney.Demand.BudgetAdjustment
#print axioms Kreps.UtilityForMoney.Demand.budgetAdjustment_self
#print axioms Kreps.UtilityForMoney.Demand.budgetAdjustment_feasible
#print axioms Kreps.UtilityForMoney.Demand.budgetAdjustment_continuous
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_continuous_selection
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_sequentialLower
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_sequentialUpper
#print axioms Kreps.UtilityForMoney.Demand.budgetSet_localCompactBound
#print axioms Kreps.UtilityForMoney.Demand.MarshallianDemand
#print axioms Kreps.UtilityForMoney.Demand.mem_marshallianDemand_iff
#print axioms Kreps.UtilityForMoney.Demand.mem_marshallianDemand_iff_isMaxOn
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_1a
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_1b
#print axioms Kreps.UtilityForMoney.Demand.marshallianDemand_zero
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_1c_convex
#print axioms Kreps.UtilityForMoney.Demand.marshallianDemand_subsingleton
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_1c_unique
#print axioms Kreps.UtilityForMoney.Demand.preferenceChoice_exhausts_budget
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_1d
#print axioms Kreps.UtilityForMoney.Demand.IndirectUtility
#print axioms Kreps.UtilityForMoney.Demand.indirectUtility_eq_of_mem
#print axioms Kreps.UtilityForMoney.Demand.indirectUtility_zero
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_3a
#print axioms Kreps.UtilityForMoney.Demand.consumer_maximum_theorem
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_3b
#print axioms Kreps.UtilityForMoney.Demand.marshallianDemand_localCompactBound
#print axioms Kreps.UtilityForMoney.Demand.marshallianDemand_isCompact
#print axioms Kreps.UtilityForMoney.Demand.marshallianDemand_upperHemicontinuous
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_3c
#print axioms Kreps.UtilityForMoney.Demand.proposition_3_3b_unique
#print axioms Kreps.UtilityForMoney.LotteryTheory.FullMenus
#print axioms Kreps.UtilityForMoney.LotteryTheory.ChoiceRule
#print axioms Kreps.UtilityForMoney.LotteryTheory.FeasibleOn
#print axioms Kreps.UtilityForMoney.LotteryTheory.Feasible
#print axioms Kreps.UtilityForMoney.LotteryTheory.FiniteNonempty
#print axioms Kreps.UtilityForMoney.LotteryTheory.CoherentOn
#print axioms Kreps.UtilityForMoney.LotteryTheory.Coherent
#print axioms Kreps.UtilityForMoney.LotteryTheory.Complete
#print axioms Kreps.UtilityForMoney.LotteryTheory.TransitivePref
#print axioms Kreps.UtilityForMoney.LotteryTheory.Rational
#print axioms Kreps.UtilityForMoney.LotteryTheory.PrefChoice
#print axioms Kreps.UtilityForMoney.LotteryTheory.UtilityPref
#print axioms Kreps.UtilityForMoney.LotteryTheory.UtilityChoice
#print axioms Kreps.UtilityForMoney.LotteryTheory.Represents
#print axioms Kreps.UtilityForMoney.LotteryTheory.Revealed
#print axioms Kreps.UtilityForMoney.LotteryTheory.Strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.Indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.NoBetterThan
#print axioms Kreps.UtilityForMoney.LotteryTheory.complete_refl
#print axioms Kreps.UtilityForMoney.LotteryTheory.prefChoice_feasible
#print axioms Kreps.UtilityForMoney.LotteryTheory.feasible_empty
#print axioms Kreps.UtilityForMoney.LotteryTheory.represents_choice
#print axioms Kreps.UtilityForMoney.LotteryTheory.coherent_iff_on_full
#print axioms Kreps.UtilityForMoney.LotteryTheory.AsymmetricPref
#print axioms Kreps.UtilityForMoney.LotteryTheory.NegativelyTransitive
#print axioms Kreps.UtilityForMoney.LotteryTheory.WeakFromStrict
#print axioms Kreps.UtilityForMoney.LotteryTheory.IndifferenceFromStrict
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9a
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9b
#print axioms Kreps.UtilityForMoney.LotteryTheory.strict_weak_trans
#print axioms Kreps.UtilityForMoney.LotteryTheory.weak_strict_trans
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9c
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9d
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9e
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9f
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9g
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_9h
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_1_10
#print axioms Kreps.UtilityForMoney.LotteryTheory.problem_1_9
#print axioms Kreps.UtilityForMoney.LotteryTheory.Weight
#print axioms Kreps.UtilityForMoney.LotteryTheory.Mix
#print axioms Kreps.UtilityForMoney.LotteryTheory.AffineInMix
#print axioms Kreps.UtilityForMoney.LotteryTheory.BackgroundIndependent
#print axioms Kreps.UtilityForMoney.LotteryTheory.MixtureContinuous
#print axioms Kreps.UtilityForMoney.LotteryTheory.MixtureAxioms
#print axioms Kreps.UtilityForMoney.LotteryTheory.Complement
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_self
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_zero
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_one
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_swap
#print axioms Kreps.UtilityForMoney.LotteryTheory.WeightMean
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_mix
#print axioms Kreps.UtilityForMoney.LotteryTheory.WeakBackgroundIndependent
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_5_some_iff
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_5_weak_iff
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_5_indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_shift
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_step_weak
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_step_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.GridWeight
#print axioms Kreps.UtilityForMoney.LotteryTheory.gridWeight_last
#print axioms Kreps.UtilityForMoney.LotteryTheory.gridWeight_zero
#print axioms Kreps.UtilityForMoney.LotteryTheory.gridWeight_step
#print axioms Kreps.UtilityForMoney.LotteryTheory.grid_chain
#print axioms Kreps.UtilityForMoney.LotteryTheory.grid_weak
#print axioms Kreps.UtilityForMoney.LotteryTheory.grid_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.exists_gridWeight_between
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_base_weak
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_mono
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_base_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_7_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_bounds
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_7_indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_6_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_6_indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_monotone
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_strict
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_8
#print axioms Kreps.UtilityForMoney.LotteryTheory.Between
#print axioms Kreps.UtilityForMoney.LotteryTheory.segment_compare_iff
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_9
#print axioms Kreps.UtilityForMoney.LotteryTheory.lemma_5_9_unique
#print axioms Kreps.UtilityForMoney.LotteryTheory.AnchorWeight
#print axioms Kreps.UtilityForMoney.LotteryTheory.anchorWeight_indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.mix_congr_indifferent
#print axioms Kreps.UtilityForMoney.LotteryTheory.between_mix
#print axioms Kreps.UtilityForMoney.LotteryTheory.anchorWeight_represents
#print axioms Kreps.UtilityForMoney.LotteryTheory.anchorWeight_affine
#print axioms Kreps.UtilityForMoney.LotteryTheory.representation_with_best_worst
#print axioms Kreps.UtilityForMoney.LotteryTheory.Calibrates
#print axioms Kreps.UtilityForMoney.LotteryTheory.exists_calibration
#print axioms Kreps.UtilityForMoney.LotteryTheory.exists_preference_enclosure
#print axioms Kreps.UtilityForMoney.LotteryTheory.normalized_interval_utility
#print axioms Kreps.UtilityForMoney.LotteryTheory.calibration_eq_local
#print axioms Kreps.UtilityForMoney.LotteryTheory.SimpleLottery
#print axioms Kreps.UtilityForMoney.LotteryTheory.PureLottery
#print axioms Kreps.UtilityForMoney.LotteryTheory.ExpectedUtility
#print axioms Kreps.UtilityForMoney.LotteryTheory.expectedUtility_eq_affineMap
#print axioms Kreps.UtilityForMoney.LotteryTheory.expectedUtility_pure
#print axioms Kreps.UtilityForMoney.LotteryTheory.lottery_mix_weight
#print axioms Kreps.UtilityForMoney.LotteryTheory.expectedUtility_affine
#print axioms Kreps.UtilityForMoney.LotteryTheory.expectedUtility_eq_sum
#print axioms Kreps.UtilityForMoney.LotteryTheory.affineInMix_eq_expectedUtility
#print axioms Kreps.UtilityForMoney.LotteryTheory.problem_5_3
#print axioms Kreps.UtilityForMoney.LotteryTheory.mixtureAxioms_of_representation
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_5_4
#print axioms Kreps.UtilityForMoney.LotteryTheory.proposition_5_3
#print axioms Kreps.UtilityForMoney.expectedUtility_map
#print axioms Kreps.UtilityForMoney.InducedIncomePreference
#print axioms Kreps.UtilityForMoney.incomeLottery_value
#print axioms Kreps.UtilityForMoney.proposition_6_16
#print axioms Kreps.UtilityForMoney.proposition_6_16a
#print axioms Kreps.UtilityForMoney.proposition_6_16b
#print axioms Kreps.UtilityForMoney.proposition_6_16c
#print axioms Kreps.UtilityForMoney.incomeLottery_risk_averse
#print axioms Kreps.UtilityForMoney.Figure62States
#print axioms Kreps.UtilityForMoney.Figure62Initial
#print axioms Kreps.UtilityForMoney.Figure62Supplement
#print axioms Kreps.UtilityForMoney.Figure62Final
#print axioms Kreps.UtilityForMoney.figure62_states_value
#print axioms Kreps.UtilityForMoney.figure62_initial_law
#print axioms Kreps.UtilityForMoney.figure62_final_law
#print axioms Kreps.UtilityForMoney.figure62_supplement_law
#print axioms Kreps.UtilityForMoney.figure62_conditional_means
#print axioms Kreps.UtilityForMoney.figure62_secondOrder
#print axioms Kreps.UtilityForMoney.expectedUtility_add_scaled
#print axioms Kreps.UtilityForMoney.last_secant_le
#print axioms Kreps.UtilityForMoney.exists_cap_interpolant
#print axioms Kreps.UtilityForMoney.secondOrder_iff_shortfalls
#print axioms Kreps.UtilityForMoney.LotteryTheory.MeasureCombination
#print axioms Kreps.UtilityForMoney.LotteryTheory.measureCombination_event
#print axioms Kreps.UtilityForMoney.LotteryTheory.probabilityMeasure_ext_real
#print axioms Kreps.UtilityForMoney.LotteryTheory.BorelConvexSpace
#print axioms Kreps.UtilityForMoney.LotteryTheory.borelMix_event
#print axioms Kreps.UtilityForMoney.LotteryTheory.AtomicProbability
#print axioms Kreps.UtilityForMoney.LotteryTheory.integral_measureCombination
#print axioms Kreps.UtilityForMoney.LotteryTheory.integral_atomicProbability
#print axioms Kreps.UtilityForMoney.LotteryTheory.measureCombination_eq_barycenter
#print axioms Kreps.UtilityForMoney.LotteryTheory.affineInMix_barycenter
#print axioms Kreps.UtilityForMoney.LotteryTheory.affineInMix_atomicProbability
#print axioms Kreps.UtilityForMoney.LotteryTheory.ImageWeights
#print axioms Kreps.UtilityForMoney.LotteryTheory.SimpleImageLottery
#print axioms Kreps.UtilityForMoney.LotteryTheory.simpleImageLottery_law
#print axioms Kreps.UtilityForMoney.LotteryTheory.exists_simpleLotteries_tendsto
#print axioms Kreps.UtilityForMoney.LotteryTheory.OpenStrictSections
#print axioms Kreps.UtilityForMoney.LotteryTheory.affine_attains_between
#print axioms Kreps.UtilityForMoney.LotteryTheory.openStrictSections_iff_continuous
#print axioms Kreps.UtilityForMoney.LotteryTheory.integral_affineInMix
#print axioms Kreps.UtilityForMoney.LotteryTheory.weakMix_tendsto
#print axioms Kreps.UtilityForMoney.LotteryTheory.continuous_affine_bounded
#print axioms Kreps.UtilityForMoney.expectedUtility_sum_over
#print axioms Kreps.UtilityForMoney.expectedUtility_tendsto_fixed_support
#print axioms Kreps.UtilityForMoney.lottery_strict_rankings_eventually
#print axioms Kreps.UtilityForMoney.expectedUtility_tendsto_moving_prizes
#print axioms Kreps.UtilityForMoney.nearby_money_lotteries
#print axioms Kreps.UtilityForMoney.expectedUtility_tendsto_weak
#print axioms Kreps.UtilityForMoney.expectedUtility_tendsto_on_compact
#print axioms Kreps.UtilityForMoney.capped_values_equal
#print axioms Kreps.UtilityForMoney.finite_prize_gap
#print axioms Kreps.UtilityForMoney.secondOrder_antisymm
#print axioms Kreps.UtilityForMoney.firstOrder_antisymm
#print axioms Kreps.UtilityForMoney.dominance_reflexive
#print axioms Kreps.UtilityForMoney.dominance_transitive
#print axioms Kreps.UtilityForMoney.midpoint_gap_nonneg
#print axioms Kreps.UtilityForMoney.concavity_of_equal_probability_gambles
#print axioms Kreps.UtilityForMoney.binaryLottery_law
#print axioms Kreps.UtilityForMoney.RareWeight
#print axioms Kreps.UtilityForMoney.rareLottery_weak_limit
#print axioms Kreps.UtilityForMoney.unbounded_prize_reversal
#print axioms Kreps.UtilityForMoney.OpenWealthUtility
#print axioms Kreps.UtilityForMoney.openWealthUtility_regular
#print axioms Kreps.UtilityForMoney.bounded_prizes_open_endpoint
#print axioms Kreps.UtilityForMoney.GeneralQuantile
#print axioms Kreps.UtilityForMoney.generalQuantile_le_iff
#print axioms Kreps.UtilityForMoney.generalQuantile_measurable
#print axioms Kreps.UtilityForMoney.generalQuantile_uniform_law
#print axioms Kreps.UtilityForMoney.ImperfectLoss
#print axioms Kreps.UtilityForMoney.imperfect_policy_fair
#print axioms Kreps.UtilityForMoney.ImperfectValue
#print axioms Kreps.UtilityForMoney.imperfectValue_expectedUtility
#print axioms Kreps.UtilityForMoney.imperfectValue_hasDerivAt
#print axioms Kreps.UtilityForMoney.wealth_concave_tangent
#print axioms Kreps.UtilityForMoney.imperfect_full_iff
#print axioms Kreps.UtilityForMoney.BalancedMarginalUtility
#print axioms Kreps.UtilityForMoney.balancedMarginal_derivative
#print axioms Kreps.UtilityForMoney.balancedMarginal_regular
#print axioms Kreps.UtilityForMoney.problem_6_9_full
#print axioms Kreps.UtilityForMoney.problem_6_9_not_full
#print axioms Kreps.UtilityForMoney.insuranceUtility_concave
#print axioms Kreps.UtilityForMoney.insuranceUtility_hasDerivAt
#print axioms Kreps.UtilityForMoney.insurance_optimal_iff_marginals
#print axioms Kreps.UtilityForMoney.fair_affine_insurance
#print axioms Kreps.UtilityForMoney.expensive_insurance_no_maximum
#print axioms Kreps.UtilityForMoney.cumulative_zero_iff
#print axioms Kreps.UtilityForMoney.atom_cdf_integral
#print axioms Kreps.UtilityForMoney.integrated_cumulative_eq_shortfall
#print axioms Kreps.UtilityForMoney.expectedShortfall_zero_of_le
#print axioms Kreps.UtilityForMoney.proposition_6_14b
#print axioms Kreps.UtilityForMoney.problem_6_6a
#print axioms Kreps.UtilityForMoney.problem_6_6c
#print axioms Kreps.UtilityForMoney.IntervalRiskAversion
#print axioms Kreps.UtilityForMoney.intervalRiskAversion_eq_of_interior
#print axioms Kreps.UtilityForMoney.intervalRiskAversion_continuousOn
#print axioms Kreps.UtilityForMoney.interval_marginal_support
#print axioms Kreps.UtilityForMoney.proposition_6_8_within
#print axioms Kreps.UtilityForMoney.derivWithin_wealth_shift
#print axioms Kreps.UtilityForMoney.intervalRiskAversion_shift
#print axioms Kreps.UtilityForMoney.shiftPremiumOrder_iff_within_coefficients
#print axioms Kreps.UtilityForMoney.shiftPremiumOrder_of_within_coefficients
#print axioms Kreps.UtilityForMoney.zero_mem_interior_shiftDomain
#print axioms Kreps.UtilityForMoney.proposition_6_12_within
#print axioms Kreps.UtilityForMoney.eqOn_interval_of_eqOn_interior
#print axioms Kreps.UtilityForMoney.cara_representation_within
#print axioms Kreps.UtilityForMoney.problem_6_2_within
#print axioms Kreps.UtilityForMoney.inverse_utility_regularity
#print axioms Kreps.UtilityForMoney.utilityTransform_hasDerivAt
#print axioms Kreps.UtilityForMoney.utilityTransform_second_derivative
#print axioms Kreps.UtilityForMoney.jensen_by_support_induction
#print axioms Kreps.UtilityForMoney.problem_6_1b_induction
#print axioms Kreps.UtilityForMoney.riskSeeking_iff_convex
#print axioms Kreps.UtilityForMoney.riskNeutral_iff_affine_mixes
#print axioms Kreps.UtilityForMoney.figure_6_1
#print axioms Kreps.UtilityForMoney.concaveUtility_continuousOn_interior
#print axioms Kreps.UtilityForMoney.monetary_representation_of_axioms
#print axioms Kreps.UtilityForMoney.strictMono_iff_sure_preference
#print axioms Kreps.UtilityForMoney.isCertaintyEquivalent_iff_indifferent
#print axioms Kreps.UtilityForMoney.concave_iff_sure_mean_preferred
#print axioms Kreps.UtilityForMoney.concave_iff_nonnegative_premia
#print axioms Kreps.UtilityForMoney.riskNeutral_iff_zero_premia
#print axioms Kreps.UtilityForMoney.RiskyPairMenu
#print axioms Kreps.UtilityForMoney.HedgeValue
#print axioms Kreps.UtilityForMoney.riskyPairMenu_compact
#print axioms Kreps.UtilityForMoney.hedgeValue_attains
#print axioms Kreps.UtilityForMoney.problem_6_12_hedge
#print axioms Kreps.UtilityForMoney.DominatedValue
#print axioms Kreps.UtilityForMoney.problem_6_12_dominated
#print axioms Kreps.UtilityForMoney.IndependentPriceIncome
#print axioms Kreps.UtilityForMoney.PriceAveragedValue
#print axioms Kreps.UtilityForMoney.independent_price_income_value
#print axioms Kreps.UtilityForMoney.priceAveragedValue_continuous
#print axioms Kreps.UtilityForMoney.priceAveragedValue_strictMono
#print axioms Kreps.UtilityForMoney.priceAveragedValue_concave
#print axioms Kreps.UtilityForMoney.fixed_income_price_lottery_value
#print axioms Kreps.UtilityForMoney.indirectUtility_continuous_prices
#print axioms Kreps.UtilityForMoney.indirectUtility_antitone_prices
#print axioms Kreps.UtilityForMoney.two_price_income_couplings
#print axioms Kreps.UtilityForMoney.two_price_income_values
#print axioms Kreps.UtilityForMoney.priceRisk_map_binary
#print axioms Kreps.UtilityForMoney.two_price_income_marginals
#print axioms Kreps.UtilityForMoney.TwoGoodBudget
#print axioms Kreps.UtilityForMoney.sum_bundle_risky_price_optima
#print axioms Kreps.UtilityForMoney.sum_bundle_mean_price_optimum
#print axioms Kreps.UtilityForMoney.problem_6_8a
#print axioms Kreps.UtilityForMoney.complementary_bundle_value
#print axioms Kreps.UtilityForMoney.KinkedPriceUtility
#print axioms Kreps.UtilityForMoney.kinkedPriceUtility_strictMono
#print axioms Kreps.UtilityForMoney.kinkedPriceUtility_concave
#print axioms Kreps.UtilityForMoney.price_level_quantities_order
#print axioms Kreps.UtilityForMoney.problem_6_8b_fixed_dispersion
#print axioms Kreps.UtilityForMoney.problem_6_8b_large_dispersion
#print axioms Kreps.UtilityForMoney.price_risk_expectedUtility
#print axioms Kreps.UtilityForMoney.price_risk_at_zero_income
#print axioms Kreps.UtilityForMoney.StablePrizeComparisons
#print axioms Kreps.UtilityForMoney.proposition_6_2
#print axioms Kreps.UtilityForMoney.stablePrizeComparisons_iff_metric
#print axioms Kreps.UtilityForMoney.Prefix
#print axioms Kreps.UtilityForMoney.Before
#print axioms Kreps.UtilityForMoney.cumulative_eq_prefix
#print axioms Kreps.UtilityForMoney.prefix_sub_before
#print axioms Kreps.UtilityForMoney.prefix_le_before_of_lt
#print axioms Kreps.UtilityForMoney.prefix_probability_bounds
#print axioms Kreps.UtilityForMoney.sum_prefix_increments
#print axioms Kreps.UtilityForMoney.exists_prefix_bin
#print axioms Kreps.UtilityForMoney.QuantileBin
#print axioms Kreps.UtilityForMoney.QuantilePrize
#print axioms Kreps.UtilityForMoney.quantilePrize_zero
#print axioms Kreps.UtilityForMoney.quantilePrize_mem_bin
#print axioms Kreps.UtilityForMoney.quantileBin_unique
#print axioms Kreps.UtilityForMoney.quantileBin_subset_unit
#print axioms Kreps.UtilityForMoney.quantilePrize_uniform_mass
#print axioms Kreps.UtilityForMoney.Overlap
#print axioms Kreps.UtilityForMoney.overlap_eq_length
#print axioms Kreps.UtilityForMoney.overlap_comm
#print axioms Kreps.UtilityForMoney.sum_overlap_bins
#print axioms Kreps.UtilityForMoney.QuantileCoupling
#print axioms Kreps.UtilityForMoney.FiniteCoupling.Ordered
#print axioms Kreps.UtilityForMoney.quantileCoupling_ordered
#print axioms Kreps.UtilityForMoney.firstOrder_of_ordered_coupling
#print axioms Kreps.UtilityForMoney.proposition_6_14a
#print axioms Kreps.UtilityForMoney.proposition_6_15a
#print axioms Kreps.UtilityForMoney.quantile_uniform_joint_mass
#print axioms Kreps.UtilityForMoney.quantilePrize_ordered
#print axioms Kreps.UtilityForMoney.deriv_scaled_wealth
#print axioms Kreps.UtilityForMoney.absoluteRiskAversion_scaled
#print axioms Kreps.UtilityForMoney.NonincreasingCertaintyReturn
#print axioms Kreps.UtilityForMoney.nonincreasingCertaintyReturn_iff
#print axioms Kreps.UtilityForMoney.nonincreasingCertaintyReturn_iff_relative
#print axioms Kreps.UtilityForMoney.relativeRisk_printed_counterexample
#print axioms Kreps.UtilityForMoney.TrialBranch
#print axioms Kreps.UtilityForMoney.trialBranch_value
#print axioms Kreps.UtilityForMoney.RepeatedLaw
#print axioms Kreps.UtilityForMoney.repeatedLaw_mean
#print axioms Kreps.UtilityForMoney.repeated_exponential_steps
#print axioms Kreps.UtilityForMoney.repeatedLaw_exponential
#print axioms Kreps.UtilityForMoney.problem_6_14_unrestricted
#print axioms Kreps.UtilityForMoney.ShareValue
#print axioms Kreps.UtilityForMoney.shareValue_hasDerivAt_zero
#print axioms Kreps.UtilityForMoney.problem_6_13a
#print axioms Kreps.UtilityForMoney.small_share_independent_wealth
#print axioms Kreps.UtilityForMoney.SmallShareLaw
#print axioms Kreps.UtilityForMoney.smallShareLaw_mean
#print axioms Kreps.UtilityForMoney.small_share_kink
#print axioms Kreps.UtilityForMoney.small_share_kink_nondifferentiable
#print axioms Kreps.UtilityForMoney.small_share_correlated_loss
#print axioms Kreps.UtilityForMoney.StoppedLaw
#print axioms Kreps.UtilityForMoney.StoppedValue
#print axioms Kreps.UtilityForMoney.stoppedValue_initial
#print axioms Kreps.UtilityForMoney.stoppedValue_bankrupt
#print axioms Kreps.UtilityForMoney.stoppedValue_step
#print axioms Kreps.UtilityForMoney.expectedUtility_mono
#print axioms Kreps.UtilityForMoney.WalkFactor
#print axioms Kreps.UtilityForMoney.walk_geometric_step
#print axioms Kreps.UtilityForMoney.stopped_power_le
#print axioms Kreps.UtilityForMoney.stopped_power_ge
#print axioms Kreps.UtilityForMoney.AlivePower
#print axioms Kreps.UtilityForMoney.alivePower_bound
#print axioms Kreps.UtilityForMoney.bounded_walk_utility
#print axioms Kreps.UtilityForMoney.problem_6_14_bounded
#print axioms Kreps.UtilityForMoney.stoppedValue_affine_two
#print axioms Kreps.UtilityForMoney.stopped_utility_lower
#print axioms Kreps.UtilityForMoney.problem_6_14_unbounded
#print axioms Kreps.UtilityForMoney.BankruptcyBase
#print axioms Kreps.UtilityForMoney.bankruptcyBase_bounds
#print axioms Kreps.UtilityForMoney.bankruptcyBase_harmonic
#print axioms Kreps.UtilityForMoney.BankruptcyIndicator
#print axioms Kreps.UtilityForMoney.bankruptcy_mass
#print axioms Kreps.UtilityForMoney.bankruptcy_probability_identity
#print axioms Kreps.UtilityForMoney.alivePower_tendsto
#print axioms Kreps.UtilityForMoney.bankruptcy_probability_limit
#print axioms Kreps.UtilityForMoney.stopped_bounded_upper
#print axioms Kreps.UtilityForMoney.stopped_bounded_lower
#print axioms Kreps.UtilityForMoney.stopped_bounded_limit
#print axioms Kreps.UtilityForMoney.stopped_bounded_criterion
#print axioms Kreps.UtilityForMoney.TimingMenu
#print axioms Kreps.UtilityForMoney.TimingValue
#print axioms Kreps.UtilityForMoney.TimingMarginal
#print axioms Kreps.UtilityForMoney.spending_remainder_optimal
#print axioms Kreps.UtilityForMoney.timing_log_tangent
#print axioms Kreps.UtilityForMoney.timing_log_tangent_strict
#print axioms Kreps.UtilityForMoney.timing_unique_of_marginal
#print axioms Kreps.UtilityForMoney.TimingTwo
#print axioms Kreps.UtilityForMoney.TimingSure
#print axioms Kreps.UtilityForMoney.TimingThree
#print axioms Kreps.UtilityForMoney.timing_two_optimum
#print axioms Kreps.UtilityForMoney.timing_sure_optimum
#print axioms Kreps.UtilityForMoney.timing_three_root
#print axioms Kreps.UtilityForMoney.timing_three_optimum
#print axioms Kreps.UtilityForMoney.timingValue_eq_log_product
#print axioms Kreps.UtilityForMoney.timing_log_certificate
#print axioms Kreps.UtilityForMoney.timing_two_value_bounds
#print axioms Kreps.UtilityForMoney.timing_sure_value_bounds
#print axioms Kreps.UtilityForMoney.timing_three_product_bounds
#print axioms Kreps.UtilityForMoney.timing_three_value_bounds
#print axioms Kreps.UtilityForMoney.TimingIncomeTwo
#print axioms Kreps.UtilityForMoney.TimingIncomeSure
#print axioms Kreps.UtilityForMoney.TimingIncomeThree
#print axioms Kreps.UtilityForMoney.TimingBundleIndex
#print axioms Kreps.UtilityForMoney.timing_income_mixture_value
#print axioms Kreps.UtilityForMoney.timing_values_as_expectations
#print axioms Kreps.UtilityForMoney.timing_optimized_mixture_worse
#print axioms Kreps.UtilityForMoney.problem_6_7_no_income_index
#print axioms Kreps.UtilityForMoney.eventually_mem_lottery_support
#print axioms Kreps.UtilityForMoney.outside_prize_bound
#print axioms Kreps.UtilityForMoney.expectedUtility_tendsto_bounded_extra_prizes
