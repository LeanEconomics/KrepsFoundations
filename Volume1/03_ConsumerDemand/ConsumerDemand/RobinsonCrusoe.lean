/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.CorrespondenceMaximum
import Mathlib.Basic.NNReal.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-!
# Robinson Crusoe's consumption and planting problem

Kreps I, Problem 3.14(a,d), pp. 65-66. The feasible planting interval is
`[0,e]`, including both endpoints and zero endowment, and the literal objective
is `U(e-x,f(x))`. The exercise invites sufficient assumptions: continuity of
the real-valued production and utility functions gives existence and Berge
continuity. Economic production monotonicity and `f(0)=0` are used in the
subsequent convexity module, not needed for these stronger topological facts.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal Topology
open Filter

/-- Planting cannot be negative or exceed the nonnegative initial endowment. -/
def CrusoeFeasible (e : ℝ≥0) : Set ℝ := Set.Icc 0 (e : ℝ)

/-- The exact two-period utility of current consumption and the crop produced by planting. -/
def CrusoeObjective (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) (e : ℝ≥0) (x : ℝ) : ℝ :=
  U ((e : ℝ) - x, f x)

/-- The entire set of optimal planting quantities. -/
def CrusoeDemand (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : ℝ≥0 → Set ℝ :=
  ParametricMaxima CrusoeFeasible (CrusoeObjective f U)

/-- The attained value, once continuity guarantees an optimum. -/
noncomputable def CrusoeValue (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : ℝ≥0 → ℝ :=
  ParametricValue CrusoeFeasible (CrusoeObjective f U)

/-- The zero planting choice is feasible for every endowment. -/
theorem crusoeFeasible_nonempty (e : ℝ≥0) : (CrusoeFeasible e).Nonempty :=
  ⟨0, le_rfl, e.property⟩

/-- Every planting menu is compact. -/
theorem crusoeFeasible_isCompact (e : ℝ≥0) : IsCompact (CrusoeFeasible e) := isCompact_Icc

/-- Joint continuity of the literal objective follows from continuity of production and utility. -/
theorem crusoeObjective_continuous {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) :
    Continuous (fun q : ℝ≥0 × ℝ => CrusoeObjective f U q.1 q.2) :=
  hU.comp (((continuous_subtype_val.comp continuous_fst).sub continuous_snd).prodMk
    (hf.comp continuous_snd))

/-- Truncating a reference planting quantity at the new endowment gives a feasible recovery. -/
theorem crusoeFeasible_continuous_selection (e : ℝ≥0) (x : ℝ) (hx : x ∈ CrusoeFeasible e) :
    ∃ s : ℝ≥0 → ℝ, Continuous s ∧ s e = x ∧ ∀ e', s e' ∈ CrusoeFeasible e' := by
  exact ⟨fun e' => min x (e' : ℝ), continuous_const.inf continuous_subtype_val,
    min_eq_left hx.2, fun e' => ⟨le_min hx.1 e'.property, min_le_right _ _⟩⟩

/-- Planting feasibility has the book's lower semicontinuity property, including at zero. -/
theorem crusoeFeasible_sequentialLower : SequentialLower CrusoeFeasible :=
  sequentialLower_of_continuous_selections crusoeFeasible_continuous_selection

/-- Limits of feasible planting quantities remain feasible at the limiting endowment. -/
theorem crusoeFeasible_sequentialUpper : SequentialUpper CrusoeFeasible := by
  intro e x e₀ x₀ he hx hm
  refine ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hx
    (Eventually.of_forall (fun n => (hm n).1)), ?_⟩
  exact le_of_tendsto_of_tendsto hx (continuous_subtype_val.continuousAt.tendsto.comp he)
    (Eventually.of_forall (fun n => (hm n).2))

/-- Nearby endowments share a common compact planting bound. -/
theorem crusoeFeasible_localCompactBound : LocalCompactBound CrusoeFeasible := by
  intro e
  refine ⟨Set.Icc 0 ((e : ℝ) + 1), isCompact_Icc, ?_⟩
  have he : ∀ᶠ e' : ℝ≥0 in 𝓝 e, (e' : ℝ) < (e : ℝ) + 1 :=
    (continuous_subtype_val.continuousAt (x := e)).eventually
      (isOpen_Iio.mem_nhds (show (e : ℝ) < (e : ℝ) + 1 by linarith))
  filter_upwards [he] with e' he'
  intro x hx
  exact ⟨hx.1, hx.2.trans he'.le⟩

/-- **Problem 3.14(a):** continuous production and utility guarantee an optimal planting choice. -/
theorem problem_3_14a {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (e : ℝ≥0) : (CrusoeDemand f U e).Nonempty := by
  exact parametricMaxima_nonempty (crusoeFeasible_isCompact e) (crusoeFeasible_nonempty e)
    ((crusoeObjective_continuous hf hU).comp (continuous_const.prodMk continuous_id))

/-- **Problem 3.14(d):** the value is continuous and optimal planting is upper semicontinuous. -/
theorem problem_3_14d {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) :
    SequentialUpper (CrusoeDemand f U) ∧ LocalCompactBound (CrusoeDemand f U) ∧
      Continuous (CrusoeValue f U) :=
  (maximum_theorem (crusoeObjective_continuous hf hU) crusoeFeasible_sequentialLower
    crusoeFeasible_sequentialUpper crusoeFeasible_localCompactBound crusoeFeasible_nonempty).2

/-- The value is the actual utility of any optimal planting quantity. -/
theorem crusoeValue_eq_of_optimum {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ} {e : ℝ≥0} {x : ℝ}
    (hx : x ∈ CrusoeDemand f U e) : CrusoeValue f U e = U ((e : ℝ) - x, f x) :=
  parametricValue_eq_of_maximum hx

/-- The full set of optimal planting quantities is compact. -/
theorem crusoeDemand_isCompact {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (e : ℝ≥0) : IsCompact (CrusoeDemand f U e) :=
  (problem_3_14d hf hU).1.isCompact (problem_3_14d hf hU).2.1 e

/-- At zero endowment the unique possible planting quantity is zero. -/
theorem crusoeDemand_zero (f : ℝ → ℝ) (U : ℝ × ℝ → ℝ) : CrusoeDemand f U 0 = {0} := by
  ext x
  simp only [CrusoeDemand, ParametricMaxima, CrusoeFeasible, NNReal.coe_zero, Set.Icc_self,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
  exact ⟨And.left, fun h => ⟨h, by rw [h]⟩⟩

/-- Uniqueness everywhere gives a continuous selection and lower semicontinuous optimal planting. -/
theorem crusoeDemand_continuous_of_unique {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hU : Continuous U) (hu : ∀ e, (CrusoeDemand f U e).Subsingleton) :
    ∃ s : ℝ≥0 → ℝ, Continuous s ∧ (∀ e, CrusoeDemand f U e = {s e}) ∧
      SequentialLower (CrusoeDemand f U) := by
  classical
  let s : ℝ≥0 → ℝ := fun e => Classical.choose (problem_3_14a hf hU e)
  have hs (e) : s e ∈ CrusoeDemand f U e := Classical.choose_spec (problem_3_14a hf hU e)
  have heq (e) : CrusoeDemand f U e = {s e} :=
    Set.Subset.antisymm (fun _ hx => (hu e hx (hs e))) (Set.singleton_subset_iff.mpr (hs e))
  have hfun : CrusoeDemand f U = fun e => {s e} := funext heq
  have hc : Continuous s := by
    apply continuous_of_singleton_correspondence
    · rw [← hfun]
      exact (problem_3_14d hf hU).1
    · rw [← hfun]
      exact (problem_3_14d hf hU).2.1
  refine ⟨s, hc, heq, sequentialLower_of_continuous_selections ?_⟩
  intro e x hx
  refine ⟨s, hc, ?_, hs⟩
  have hxeq : x = s e := by rwa [heq e, Set.mem_singleton_iff] at hx
  exact hxeq.symm

end Kreps.ConsumerDemand
