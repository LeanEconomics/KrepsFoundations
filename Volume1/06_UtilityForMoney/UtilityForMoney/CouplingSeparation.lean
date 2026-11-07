/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.FiniteCouplings
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

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
