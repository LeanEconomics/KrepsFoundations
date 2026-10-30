/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CalculusOptimality

/-!
# Smooth increasing concave component utilities

Kreps I, Problems 3.8-3.9, p. 65. The derivatives are finite real values and are
taken within the nonnegative half-line, including zero. Continuity of the
marginal is the source's continuous differentiability assumption. The common
toolkit permits weakly concave components so the linear numeraire in Problem 3.9
is included; Problem 3.8 separately supplies strict concavity of every component.
-/

namespace Kreps.ConsumerDemand

open Set
open scoped NNReal

/-- Primitive component functions and their continuous within-domain marginal utilities. -/
structure SeparableMarginals (k : ℕ) where
  utility : Fin k → ℝ → ℝ
  marginal : Fin k → ℝ → ℝ
  concave : ∀ j, ConcaveOn ℝ (Ici 0) (utility j)
  increasing : ∀ j, StrictMonoOn (utility j) (Ici 0)
  hasDeriv : ∀ j t, 0 ≤ t → HasDerivWithinAt (utility j) (marginal j t) (Ici 0) t
  continuous_marginal : ∀ j, ContinuousOn (marginal j) (Ici 0)

variable {k : ℕ} (U : SeparableMarginals k)

/-- The additively separable objective, interpreted on the nonnegative orthant. -/
def SeparableMarginals.total (x : Fin k → ℝ) : ℝ := ∑ j, U.utility j (x j)

/-- The derivative of the total objective is the sum of coordinate marginal maps. -/
noncomputable def SeparableMarginals.derivative (x : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ j, U.marginal j (x j) • ContinuousLinearMap.proj j

/-- The stated marginal is positive at every finite consumption level. -/
theorem SeparableMarginals.marginal_pos (j : Fin k) {t : ℝ} (ht : 0 ≤ t) :
    0 < U.marginal j t := by
  have hu := U.increasing j ht (show (0 : ℝ) ≤ t + 1 by linarith)
    (show t < t + 1 by linarith)
  have hs := (U.concave j).slope_le_of_hasDerivWithinAt ht
    (show (0 : ℝ) ≤ t + 1 by linarith) (show t < t + 1 by linarith) (U.hasDeriv j t ht)
  simp only [slope_def_field, add_sub_cancel_left, div_one] at hs
  linarith

/-- Strict concavity makes the marginal curve strictly decreasing, including at zero. -/
theorem SeparableMarginals.marginal_strictAnti (j : Fin k)
    (hs : StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictAntiOn (U.marginal j) (Ici 0) := by
  intro x hx z hz hxz
  exact (hs.lt_slope_of_hasDerivWithinAt hx hz hxz (U.hasDeriv j z hz)).trans
    (hs.slope_lt_of_hasDerivWithinAt hx hz hxz (U.hasDeriv j x hx))

/-- Concavity alone makes each marginal curve nonincreasing. -/
theorem SeparableMarginals.marginal_antitone (j : Fin k) :
    AntitoneOn (U.marginal j) (Ici 0) := by
  intro x hx z hz hxz
  rcases hxz.eq_or_lt with he | hlt
  · subst z
    exact le_rfl
  · exact ((U.concave j).le_slope_of_hasDerivWithinAt hx hz hlt
      (U.hasDeriv j z hz)).trans
      ((U.concave j).slope_le_of_hasDerivWithinAt hx hz hlt (U.hasDeriv j x hx))

/-- The component chain rule and finite sum give the genuine within-orthant derivative. -/
theorem SeparableMarginals.hasFDeriv {x : Fin k → ℝ} (hx : 0 ≤ x) :
    HasFDerivWithinAt U.total (U.derivative x) (Ici 0) x := by
  have h (j : Fin k) (_ : j ∈ Finset.univ) :
      HasFDerivWithinAt (fun z : Fin k → ℝ => U.utility j (z j))
        (U.marginal j (x j) • ContinuousLinearMap.proj j) (Ici 0) x :=
    (U.hasDeriv j (x j) (hx j)).comp_hasFDerivWithinAt (𝕜 := ℝ)
      (f := fun z : Fin k → ℝ => z j)
      (f' := (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ))
      (s := Ici (0 : Fin k → ℝ)) x
      (hasFDerivWithinAt_apply (𝕜 := ℝ) j x (Ici (0 : Fin k → ℝ))) (fun _ hz => hz j)
  convert HasFDerivWithinAt.sum h using 1
  · ext z
    simp [SeparableMarginals.total]
  · rfl

/-- Coordinate values of the total derivative are exactly the supplied scalar marginals. -/
theorem SeparableMarginals.marginalUtility (x : Fin k → ℝ) (j : Fin k) :
    MarginalUtility (U.derivative x) j = U.marginal j (x j) := by
  classical
  simp [MarginalUtility, SeparableMarginals.derivative, Pi.single_apply]

/-- The total utility is continuous on the full nonnegative orthant. -/
theorem SeparableMarginals.continuous_total :
    Continuous (fun x : NonnegativeOrthant k => U.total x.val) := by
  apply continuous_finsetSum
  intro j _
  have hc : ContinuousOn (U.utility j) (Ici 0) :=
    fun t ht => (U.hasDeriv j t ht).continuousWithinAt
  exact hc.comp_continuous ((continuous_apply j).comp continuous_subtype_val)
    (fun x => x.property j)

/-- The sum of the component concavity inequalities is concavity of total utility. -/
theorem SeparableMarginals.concave_total : ConcaveOn ℝ (Ici 0) U.total := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz a b ha hb hab
  simp only [SeparableMarginals.total, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => (U.concave j).2 (hx j) (hz j) ha hb hab)

/-- Strict concavity of all components gives strict concavity on the product domain. -/
theorem SeparableMarginals.strictConcave_total
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictConcaveOn ℝ (Ici 0) U.total := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz hne a b ha hb hab
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ z j := by
    by_contra! he
    exact hne (funext he)
  simp only [SeparableMarginals.total, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · exact fun i _ => (U.concave i).2 (hx i) (hz i) ha.le hb.le hab
  · exact ⟨j, Finset.mem_univ j, (hs j).2 (hx j) (hz j) hj ha hb hab⟩

/-- Strict concavity supplies the internal strict quasi-concavity used by demand uniqueness. -/
theorem SeparableMarginals.strictQuasiConcave_total
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j)) :
    StrictlyQuasiConcaveUtility (convex_Ici (0 : Fin k → ℝ))
      (fun x : NonnegativeOrthant k => U.total x.val) := by
  intro x z hne hxz a ha
  have h := (U.strictConcave_total hs).2 x.property z.property
    (fun he => hne (Subtype.ext he)) ha.1 (sub_pos.mpr ha.2) (by ring : a + (1 - a) = 1)
  change U.total z.val < U.total (a • x.val + (1 - a) • z.val)
  simp only [smul_eq_mul] at h
  nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr hxz)]

/-- Primitive strict-component hypotheses give a unique demand at every income, including zero. -/
theorem SeparableMarginals.unique_demand
    (hs : ∀ j, StrictConcaveOn ℝ (Ici 0) (U.utility j))
    (p : PositivePrices k) (y : ℝ≥0) :
    ∃! x, x ∈ MarshallianDemand (fun z => U.total z.val) p y :=
  proposition_3_1c_unique U.continuous_total (U.strictQuasiConcave_total hs) p y

end Kreps.ConsumerDemand
