/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-!
# Upper semicontinuity of uniformly controlled series

Analytic support for Kreps I, Problem 2.10. Uniform limits preserve upper
semicontinuity, so a series of upper semicontinuous real functions with a
summable bound on the absolute values is upper semicontinuous.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- A uniform limit of upper semicontinuous real functions is upper semicontinuous. -/
theorem upperSemicontinuous_of_tendstoUniformly {I X : Type*} [TopologicalSpace X]
    {l : Filter I} [l.NeBot] {f : I → X → ℝ} {g : X → ℝ}
    (hlim : TendstoUniformly f g l) (hf : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous g := by
  intro x b hb
  let ε := (b - g x) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have he : 3 * ε = b - g x := by dsimp [ε]; ring
  obtain ⟨i, hi⟩ := ((Metric.tendstoUniformly_iff.mp hlim) ε hε).exists
  have hx := hi x
  rw [Real.dist_eq] at hx
  have hx' : f i x < g x + 2 * ε := by linarith [(abs_lt.mp hx).1]
  filter_upwards [hf i x (g x + 2 * ε) hx'] with y hy
  have hy' := hi y
  rw [Real.dist_eq] at hy'
  linarith [(abs_lt.mp hy').2]

/-- Summably bounded upper semicontinuous summands have an upper semicontinuous sum. -/
theorem upperSemicontinuous_tsum_of_norm_le {I X : Type*} [TopologicalSpace X]
    {f : I → X → ℝ} {w : I → ℝ} (hw : Summable w)
    (hf : ∀ i, UpperSemicontinuous (f i)) (hbound : ∀ i x, ‖f i x‖ ≤ w i) :
    UpperSemicontinuous (fun x => ∑' i, f i x) :=
  upperSemicontinuous_of_tendstoUniformly (tendstoUniformly_tsum hw hbound)
    (fun _ => upperSemicontinuous_sum (fun i _ => hf i))

end Kreps.PreferenceProperties
