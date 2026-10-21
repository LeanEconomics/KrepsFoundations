/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixExtrema
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Appendix 2: limsup and liminf

Definition A2.22 and Proposition A2.23, pp. 450–451. Suprema, infima and
accumulation points are taken in the extended real line so that every sequence
is covered. The finite-limit theorem separately identifies ordinary real convergence.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The extended supremum of a sequence tail in Definition A2.22. -/
noncomputable def SequenceTailSup (u : ℕ → ℝ) (N : ℕ) : EReal :=
  ⨆ n ≥ N, (u n : EReal)

/-- The extended infimum of a sequence tail in Definition A2.22. -/
noncomputable def SequenceTailInf (u : ℕ → ℝ) (N : ℕ) : EReal :=
  ⨅ n ≥ N, (u n : EReal)

/-- Tail suprema are nonincreasing, including infinite values. -/
theorem sequenceTailSup_antitone (u : ℕ → ℝ) : Antitone (SequenceTailSup u) := by
  intro M N hMN
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact le_iSup_of_le n (le_iSup_of_le (hMN.trans hn) le_rfl)

/-- Tail infima are nondecreasing. -/
theorem sequenceTailInf_monotone (u : ℕ → ℝ) : Monotone (SequenceTailInf u) := by
  intro M N hMN
  apply le_iInf
  intro n
  apply le_iInf
  intro hn
  exact iInf_le_of_le n (iInf_le_of_le (hMN.trans hn) le_rfl)

/-- **Definition A2.22:** limsup is the infimum of the tail suprema. -/
theorem definition_A2_22_limsup (u : ℕ → ℝ) :
    Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⨅ N, SequenceTailSup u N :=
  Filter.limsup_eq_iInf_iSup_of_nat

/-- **Definition A2.22:** liminf is the supremum of the tail infima. -/
theorem definition_A2_22_liminf (u : ℕ → ℝ) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⨆ N, SequenceTailInf u N :=
  Filter.liminf_eq_iSup_iInf_of_nat

/-- The tail suprema actually converge to the limsup, as in the book's definition. -/
theorem sequenceTailSup_tendsto (u : ℕ → ℝ) :
    Filter.Tendsto (SequenceTailSup u) Filter.atTop
      (𝓝 (Filter.limsup (fun n => (u n : EReal)) Filter.atTop)) := by
  rw [definition_A2_22_limsup]
  exact tendsto_atTop_iInf (sequenceTailSup_antitone u)

/-- The tail infima converge to the liminf. -/
theorem sequenceTailInf_tendsto (u : ℕ → ℝ) :
    Filter.Tendsto (SequenceTailInf u) Filter.atTop
      (𝓝 (Filter.liminf (fun n => (u n : EReal)) Filter.atTop)) := by
  rw [definition_A2_22_liminf]
  exact tendsto_atTop_iSup (sequenceTailInf_monotone u)

/-- The limsup is the greatest extended-real accumulation point. -/
theorem appendix2_limsup_greatest_accumulation (u : ℕ → ℝ) :
    IsGreatest {x : EReal | MapClusterPt x Filter.atTop (fun n => (u n : EReal))}
      (Filter.limsup (fun n => (u n : EReal)) Filter.atTop) :=
  isGreatest_mapClusterPt_limsup

/-- The liminf is the least extended-real accumulation point. -/
theorem appendix2_liminf_least_accumulation (u : ℕ → ℝ) :
    IsLeast {x : EReal | MapClusterPt x Filter.atTop (fun n => (u n : EReal))}
      (Filter.liminf (fun n => (u n : EReal)) Filter.atTop) :=
  isLeast_mapClusterPt_liminf

/-- **Proposition A2.23:** equality of extended liminf and limsup characterizes convergence. -/
theorem proposition_A2_23 (u : ℕ → ℝ) :
    (∃ x : EReal, Filter.Tendsto (fun n => (u n : EReal)) Filter.atTop (𝓝 x)) ↔
      Filter.liminf (fun n => (u n : EReal)) Filter.atTop =
        Filter.limsup (fun n => (u n : EReal)) Filter.atTop := by
  constructor
  · rintro ⟨x, hx⟩
    exact hx.liminf_eq.trans hx.limsup_eq.symm
  · intro h
    exact ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm⟩

/-- Ordinary real convergence requires the common extended limit to be finite. -/
theorem appendix2_finite_limit (u : ℕ → ℝ) (x : ℝ) :
    Filter.Tendsto u Filter.atTop (𝓝 x) ↔
      Filter.liminf (fun n => (u n : EReal)) Filter.atTop = (x : EReal) ∧
        Filter.limsup (fun n => (u n : EReal)) Filter.atTop = (x : EReal) := by
  constructor
  · intro h
    have he := EReal.tendsto_coe.mpr h
    exact ⟨he.liminf_eq, he.limsup_eq⟩
  · rintro ⟨hi, hs⟩
    exact EReal.tendsto_coe.mp (tendsto_of_liminf_eq_limsup hi hs)

/-- Divergence to positive infinity gives infinite liminf and limsup. -/
theorem appendix2_positive_infinite_limit {u : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop Filter.atTop) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊤ ∧
      Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊤ := by
  have he := EReal.tendsto_coe_nhds_top_iff.mpr hu
  exact ⟨he.liminf_eq, he.limsup_eq⟩

/-- Divergence to negative infinity gives the negative-infinite caveat in the text. -/
theorem appendix2_negative_infinite_limit {u : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop Filter.atBot) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊥ ∧
      Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊥ := by
  have he := EReal.tendsto_coe_nhds_bot_iff.mpr hu
  exact ⟨he.liminf_eq, he.limsup_eq⟩

/-- Removing a finite prefix cannot bound an unbounded-above real sequence. -/
theorem sequenceTailSup_unbounded {u : ℕ → ℝ} (hu : ¬BddAbove (Set.range u)) (N : ℕ) :
    SequenceTailSup u N = ⊤ := by
  have ht : ¬BddAbove (u '' Set.Ici N) := by
    rintro ⟨M, hM⟩
    apply hu
    apply Filter.IsBoundedUnder.bddAbove_range
    exact Filter.isBoundedUnder_of_eventually_le (a := M)
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => hM ⟨n, hn, rfl⟩⟩)
  simpa only [Set.image_image, Function.comp_def, sSup_image, Set.mem_Ici,
    SequenceTailSup] using appendix2_extended_sup_unbounded ht

/-- An unbounded-above sequence has positive-infinite limsup even if it does not diverge. -/
theorem appendix2_limsup_unbounded {u : ℕ → ℝ} (hu : ¬BddAbove (Set.range u)) :
    Filter.limsup (fun n => (u n : EReal)) Filter.atTop = ⊤ := by
  rw [definition_A2_22_limsup]
  simp only [sequenceTailSup_unbounded hu, iInf_const]

/-- The lower-tail version of the same finite-prefix observation. -/
theorem sequenceTailInf_unbounded {u : ℕ → ℝ} (hu : ¬BddBelow (Set.range u)) (N : ℕ) :
    SequenceTailInf u N = ⊥ := by
  have ht : ¬BddBelow (u '' Set.Ici N) := by
    rintro ⟨M, hM⟩
    apply hu
    apply Filter.IsBoundedUnder.bddBelow_range
    exact Filter.isBoundedUnder_of_eventually_ge (a := M)
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => hM ⟨n, hn, rfl⟩⟩)
  simpa only [Set.image_image, Function.comp_def, sInf_image, Set.mem_Ici,
    SequenceTailInf] using appendix2_extended_inf_unbounded ht

/-- An unbounded-below sequence has negative-infinite liminf. -/
theorem appendix2_liminf_unbounded {u : ℕ → ℝ} (hu : ¬BddBelow (Set.range u)) :
    Filter.liminf (fun n => (u n : EReal)) Filter.atTop = ⊥ := by
  rw [definition_A2_22_liminf]
  simp only [sequenceTailInf_unbounded hu, iSup_const]

end Kreps.PreferenceProperties
