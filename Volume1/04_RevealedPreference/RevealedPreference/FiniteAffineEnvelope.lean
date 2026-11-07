/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import RevealedPreference.FiniteMinimum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# The finite affine envelope in Afriat's theorem

Kreps I, equation (4.1) and the proof of Proposition 4.3, pp. 72-73. Given the
numbers produced by Lemma 4.5, take the minimum of their supporting affine terms.
The construction is defined on the entire commodity vector space, so its
restriction covers every nonnegative bundle, including boundary bundles.

The results here are independent of the finite observation data structure. The
Afriat inequalities are intermediate inputs; the chapter's main theorem must
construct them from GARP before applying these envelope results.
-/

namespace Kreps.RevealedPreference

open scoped BigOperators

variable {I : Type*} {k : ℕ}

/-- Expenditure as used in each affine supporting function. -/
def AffineExpenditure (p x : Fin k → ℝ) : ℝ := ∑ j, p j * x j

/-- Expenditure is continuous on the full commodity vector space. -/
theorem affineExpenditure_continuous (p : Fin k → ℝ) :
    Continuous (AffineExpenditure p) := by
  unfold AffineExpenditure
  fun_prop

/-- Strictly positive prices make expenditure strictly increasing in the product order. -/
theorem affineExpenditure_strictMono {p : Fin k → ℝ} (hp : ∀ j, 0 < p j) :
    StrictMono (AffineExpenditure p) := by
  intro x y hxy
  obtain ⟨hle, j, hj⟩ := Pi.lt_def.mp hxy
  exact Finset.sum_lt_sum
    (fun l _ => mul_le_mul_of_nonneg_left (hle l) (hp l).le)
    ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hp j)⟩

/-- Expenditure preserves arbitrary real linear combinations. -/
theorem affineExpenditure_mix (p x y : Fin k → ℝ) (c d : ℝ) :
    AffineExpenditure p (c • x + d • y) =
      c * AffineExpenditure p x + d * AffineExpenditure p y := by
  simp only [AffineExpenditure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- The supporting affine term based at observation `i`, with its value and multiplier. -/
def FiniteAffineTerm (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I)
    (x : Fin k → ℝ) : ℝ :=
  v i + lam i * (AffineExpenditure (p i) x - AffineExpenditure (p i) (a i))

/-- Each affine term is continuous, with no sign assumptions on its coefficients. -/
theorem finiteAffineTerm_continuous (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I) :
    Continuous (FiniteAffineTerm p a v lam i) :=
  continuous_const.add
    (continuous_const.mul ((affineExpenditure_continuous (p i)).sub continuous_const))

/-- Positive multipliers and prices make each supporting term strictly increasing. -/
theorem finiteAffineTerm_strictMono {p a : I → Fin k → ℝ} {v lam : I → ℝ} (i : I)
    (hlam : 0 < lam i) (hp : ∀ j, 0 < p i j) : StrictMono (FiniteAffineTerm p a v lam i) := by
  intro x y hxy
  simpa only [FiniteAffineTerm, add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left (sub_lt_sub_right (affineExpenditure_strictMono hp hxy)
      (AffineExpenditure (p i) (a i))) hlam) (v i)

/-- A supporting affine term preserves combinations whose coefficients sum to one. -/
theorem finiteAffineTerm_mix (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I)
    (x y : Fin k → ℝ) {c d : ℝ} (hcd : c + d = 1) :
    FiniteAffineTerm p a v lam i (c • x + d • y) =
      c * FiniteAffineTerm p a v lam i x + d * FiniteAffineTerm p a v lam i y := by
  unfold FiniteAffineTerm
  rw [affineExpenditure_mix]
  linear_combination -(v i - lam i * AffineExpenditure (p i) (a i)) * hcd

/-- Each supporting term is concave on the entire vector space. -/
theorem finiteAffineTerm_concaveOn (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I) :
    ConcaveOn ℝ Set.univ (FiniteAffineTerm p a v lam i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d _ _ hcd
  simpa only [smul_eq_mul] using (finiteAffineTerm_mix p a v lam i x y hcd).symm.le

variable [Fintype I] [Nonempty I]

/-- The full-domain utility constructed after the Afriat inequalities have been obtained. -/
noncomputable def FiniteAffineEnvelope (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    (Fin k → ℝ) → ℝ := FiniteMinimum (FiniteAffineTerm p a v lam)

/-- The envelope is bounded above by each of its supporting terms. -/
theorem finiteAffineEnvelope_le_term (p a : I → Fin k → ℝ) (v lam : I → ℝ)
    (x : Fin k → ℝ) (i : I) :
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineTerm p a v lam i x :=
  finiteMinimum_le _ x i

/-- Afriat's finite affine envelope is continuous on the full vector space. -/
theorem finiteAffineEnvelope_continuous (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    Continuous (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_continuous (finiteAffineTerm_continuous p a v lam)

/-- Afriat's envelope is concave on the full vector space, hence on the nonnegative orthant. -/
theorem finiteAffineEnvelope_concaveOn (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    ConcaveOn ℝ Set.univ (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_concaveOn (finiteAffineTerm_concaveOn p a v lam)

/-- Positive Afriat multipliers and prices make the envelope strictly increasing. -/
theorem finiteAffineEnvelope_strictMono {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hp : ∀ i j, 0 < p i j) :
    StrictMono (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_strictMono (fun i => finiteAffineTerm_strictMono i (hlam i) (hp i))

/-- Equation (4.1) makes the envelope interpolate the prescribed utility of every observation. -/
theorem finiteAffineEnvelope_at_anchor {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hineq : ∀ i j, v i ≤ v j + lam j *
      (AffineExpenditure (p j) (a i) - AffineExpenditure (p j) (a j))) (i : I) :
    FiniteAffineEnvelope p a v lam (a i) = v i := by
  apply le_antisymm
  · calc
      FiniteAffineEnvelope p a v lam (a i) ≤ FiniteAffineTerm p a v lam i (a i) :=
        finiteAffineEnvelope_le_term p a v lam (a i) i
      _ = v i := by simp [FiniteAffineTerm]
  · exact le_finiteMinimum _ _ (hineq i)

/-- Affordability at an observation bounds the envelope by that observation's assigned value. -/
theorem finiteAffineEnvelope_le_value {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (i : I) (hlam : 0 ≤ lam i) {x : Fin k → ℝ}
    (hx : AffineExpenditure (p i) x ≤ AffineExpenditure (p i) (a i)) :
    FiniteAffineEnvelope p a v lam x ≤ v i := by
  calc
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineTerm p a v lam i x :=
      finiteAffineEnvelope_le_term p a v lam x i
    _ ≤ v i := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hx))

/-- Each observed bundle maximizes the constructed envelope over its entire budget half-space. -/
theorem finiteAffineEnvelope_maximizes {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hineq : ∀ i j, v i ≤ v j + lam j *
      (AffineExpenditure (p j) (a i) - AffineExpenditure (p j) (a j)))
    (i : I) (hlam : 0 ≤ lam i) {x : Fin k → ℝ}
    (hx : AffineExpenditure (p i) x ≤ AffineExpenditure (p i) (a i)) :
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineEnvelope p a v lam (a i) := by
  rw [finiteAffineEnvelope_at_anchor hineq i]
  exact finiteAffineEnvelope_le_value i hlam hx

end Kreps.RevealedPreference
