/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixSequences
import PreferenceProperties.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Appendix 2: coordinate spaces and equivalent norms

The orthants on p. 441, the three distances on p. 444, and the coordinate-bound
characterization of Definition A2.11. Strict positivity means positivity in
every coordinate, rather than strict inequality in the product partial order.
-/

namespace Kreps.PreferenceProperties

/-- The strictly positive orthant described on p. 441. -/
def StrictlyPositiveOrthant (k : ℕ) := {x : Fin k → ℝ // ∀ j, 0 < x j}

/-- Membership of the nonnegative orthant is exactly coordinatewise nonnegativity. -/
theorem appendix2_nonnegative_coordinates {k : ℕ} (x : Fin k → ℝ) :
    x ∈ Set.Ici 0 ↔ ∀ j, 0 ≤ x j := Iff.rfl

/-- The nonnegative orthant is a closed domain, including its boundary. -/
theorem appendix2_nonnegative_orthant_closed (k : ℕ) :
    IsClosed (Set.Ici (0 : Fin k → ℝ)) := isClosed_Ici

/-- Strict coordinatewise positivity defines an open domain. -/
theorem appendix2_positive_orthant_open (k : ℕ) :
    IsOpen {x : Fin k → ℝ | ∀ j, 0 < x j} := by
  have he : {x : Fin k → ℝ | ∀ j, 0 < x j} = ⋂ j, {x | 0 < x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)

/-- The sum norm dominates the Euclidean norm by the coordinate-vector triangle inequality. -/
theorem euclidean_norm_le_sum_abs {k : ℕ} (x : CommodityEuclidean k) :
    ‖x‖ ≤ ∑ j, |x j| := by
  have he : (∑ j : Fin k, PiLp.single 2 j (x j) : CommodityEuclidean k) = x := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ j : Fin k, (PiLp.single 2 j (x j) : CommodityEuclidean k)‖ :=
      congrArg norm he.symm
    _ ≤ ∑ j : Fin k, ‖(PiLp.single 2 j (x j) : CommodityEuclidean k)‖ := norm_sum_le _ _
    _ = ∑ j, |x j| := by simp only [PiLp.norm_single, Real.norm_eq_abs]

/-- The three norms have explicit dimension-dependent comparison constants. -/
theorem appendix2_norm_comparison {k : ℕ} (x : CommodityEuclidean k) :
    ‖(fun j => x j : Fin k → ℝ)‖ ≤ ‖x‖ ∧ ‖x‖ ≤ ∑ j, |x j| ∧
      (∑ j, |x j|) ≤ k * ‖(fun j => x j : Fin k → ℝ)‖ := by
  refine ⟨(pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (PiLp.norm_apply_le x),
    euclidean_norm_le_sum_abs x, ?_⟩
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    Pi.sum_norm_apply_le_norm (fun j => x j)

/-- The sum norm and Euclidean norm give the same topology. -/
noncomputable def sumEuclideanHomeomorph (k : ℕ) :
    PiLp 1 (fun _ : Fin k => ℝ) ≃ₜ CommodityEuclidean k :=
  (PiLp.homeomorph 1 (fun _ : Fin k => ℝ)).trans
    (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm

/-- This homeomorphism preserves every coordinate. -/
theorem sumEuclideanHomeomorph_apply {k : ℕ} (x : PiLp 1 (fun _ : Fin k => ℝ))
    (j : Fin k) : sumEuclideanHomeomorph k x j = x j := rfl

/-- **Definition A2.11:** Euclidean boundedness is equivalent to uniform coordinate bounds. -/
theorem appendix2_bounded_coordinates {k : ℕ} (S : Set (CommodityEuclidean k)) :
    Bornology.IsBounded S ↔ ∃ M > 0, ∀ x ∈ S, ∀ j, |x j| < M := by
  constructor
  · intro h
    obtain ⟨M, hM, hb⟩ := h.exists_pos_norm_le
    refine ⟨M + 1, by linarith, fun x hx j => ?_⟩
    have hj : |x j| ≤ M := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x j).trans (hb x hx)
    linarith
  · rintro ⟨M, _, hb⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨k * M, fun x hx => ?_⟩
    calc
      ‖x‖ ≤ ∑ j, |x j| := euclidean_norm_le_sum_abs x
      _ ≤ ∑ _j : Fin k, M := Finset.sum_le_sum fun j _ => (hb x hx j).le
      _ = k * M := by simp

/-- The first point in the book's three-distance example. -/
def AppendixDistancePointA : Fin 2 → ℝ := ![1, 3]

/-- The second point in the example. -/
def AppendixDistancePointB : Fin 2 → ℝ := ![5, 0]

/-- The ordinary Euclidean distance in the displayed example is five. -/
theorem appendix2_example_euclidean_distance :
    dist (WithLp.toLp 2 AppendixDistancePointA) (WithLp.toLp 2 AppendixDistancePointB) = 5 := by
  norm_num [definition_A2_1, AppendixDistancePointA, AppendixDistancePointB,
    Fin.sum_univ_two, PiLp.toLp_apply, Real.sqrt_eq_iff_eq_sq]

/-- The supremum distance in the same example is four. -/
theorem appendix2_example_supremum_distance :
    dist AppendixDistancePointA AppendixDistancePointB = 4 := by
  norm_num [dist_pi_def, Finset.univ_fin2, AppendixDistancePointA, AppendixDistancePointB,
    Real.nndist_eq, Real.dist_eq]

/-- The sum (Manhattan) distance in the same example is seven. -/
theorem appendix2_example_sum_distance :
    dist (WithLp.toLp 1 AppendixDistancePointA) (WithLp.toLp 1 AppendixDistancePointB) = 7 := by
  norm_num [PiLp.dist_eq_of_L1, AppendixDistancePointA, AppendixDistancePointB,
    Fin.sum_univ_two, PiLp.toLp_apply, Real.dist_eq]

end Kreps.PreferenceProperties
