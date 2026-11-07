/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.AppendixSequenceLimits
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Appendix 2: the two sequence examples

The sequences `{10,20,30,...}` and `{1.1,2.1,1.01,2.01,...}` on pp. 445–446.
Natural-number indexing begins at zero, so the first formula uses `n + 1`.
-/

namespace Kreps.PreferenceProperties

open scoped Topology

/-- The diverging sequence displayed on p. 445. -/
def TenSequence (n : ℕ) : ℝ := 10 * (n + 1)

/-- The multiples of ten diverge to positive infinity. -/
theorem tenSequence_tendsto : Filter.Tendsto TenSequence Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b / 10)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [TenSequence]
  nlinarith

/-- The diverging sequence has no real accumulation point, as asserted on p. 446. -/
theorem tenSequence_no_accumulation (x : ℝ) : ¬MapClusterPt x Filter.atTop TenSequence := by
  intro h
  obtain ⟨φ, hφ, hlim⟩ := h.tendsto_subseq
  exact not_tendsto_atTop_of_tendsto_nhds hlim (tenSequence_tendsto.comp hφ.tendsto_atTop)

/-- In particular the sequence has no finite limit. -/
theorem tenSequence_no_limit : ¬∃ x : ℝ, Filter.Tendsto TenSequence Filter.atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  exact tenSequence_no_accumulation x hx.mapClusterPt

/-- The alternating decimal sequence, with each decimal increment used twice. -/
noncomputable def AlternatingDecimalSequence (n : ℕ) : ℝ :=
  (if n % 2 = 0 then 1 else 2) + (1 / 10 : ℝ) ^ (n / 2 + 1)

/-- The even-indexed subsequence approaches one. -/
theorem alternatingDecimal_even (n : ℕ) :
    AlternatingDecimalSequence (2 * n) = 1 + (1 / 10 : ℝ) ^ (n + 1) := by
  have hm : (2 * n) % 2 = 0 := by omega
  have hd : (2 * n) / 2 = n := by omega
  simp only [AlternatingDecimalSequence, hm, hd, ite_true]

/-- The odd-indexed subsequence approaches two. -/
theorem alternatingDecimal_odd (n : ℕ) :
    AlternatingDecimalSequence (2 * n + 1) = 2 + (1 / 10 : ℝ) ^ (n + 1) := by
  have hm : (2 * n + 1) % 2 ≠ 0 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp only [AlternatingDecimalSequence, hm, hd, ite_false]

/-- The displayed decimal perturbations tend to zero. -/
theorem decimalPerturbation_tendsto :
    Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ (n / 2 + 1)) Filter.atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply hp.comp
  apply Filter.tendsto_atTop.mpr
  intro N
  exact Filter.eventually_atTop.mpr ⟨2 * N, fun n hn => by omega⟩

/-- Both printed subsequences converge to their stated, distinct limits. -/
theorem alternatingDecimal_subsequence_limits :
    Filter.Tendsto (fun n => AlternatingDecimalSequence (2 * n)) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (fun n => AlternatingDecimalSequence (2 * n + 1)) Filter.atTop (𝓝 2) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  constructor
  · simpa only [alternatingDecimal_even, pow_succ, zero_mul, add_zero] using
      (tendsto_const_nhds.add (hp.mul_const (1 / 10 : ℝ)) :
        Filter.Tendsto (fun n => 1 + (1 / 10 : ℝ) ^ n * (1 / 10)) Filter.atTop (𝓝 (1 + 0 * _)))
  · simpa only [alternatingDecimal_odd, pow_succ, zero_mul, add_zero] using
      (tendsto_const_nhds.add (hp.mul_const (1 / 10 : ℝ)) :
        Filter.Tendsto (fun n => 2 + (1 / 10 : ℝ) ^ n * (1 / 10)) Filter.atTop (𝓝 (2 + 0 * _)))

/-- The accumulation points are exactly one and two. -/
theorem appendix2_alternating_accumulation (x : ℝ) :
    MapClusterPt x Filter.atTop AlternatingDecimalSequence ↔ x = 1 ∨ x = 2 := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hlim⟩ := h.tendsto_subseq
    have hbase := hlim.sub (decimalPerturbation_tendsto.comp hφ.tendsto_atTop)
    have hin : ∀ n, AlternatingDecimalSequence (φ n) -
        (1 / 10 : ℝ) ^ (φ n / 2 + 1) ∈ ({1, 2} : Set ℝ) := by
      intro n
      by_cases hn : φ n % 2 = 0 <;> simp [AlternatingDecimalSequence, hn]
    have hc : IsClosed ({1, 2} : Set ℝ) := (by simp : Set.Finite ({1, 2} : Set ℝ)).isClosed
    have hx := hc.mem_of_tendsto hbase (Filter.Eventually.of_forall hin)
    simpa only [sub_zero, Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  · rintro (rfl | rfl)
    · have hm : StrictMono (fun n : ℕ => 2 * n) := by intro a b h; dsimp; omega
      exact MapClusterPt.of_comp hm.tendsto_atTop
        alternatingDecimal_subsequence_limits.1.mapClusterPt
    · have hm : StrictMono (fun n : ℕ => 2 * n + 1) := by intro a b h; dsimp; omega
      exact MapClusterPt.of_comp hm.tendsto_atTop
        alternatingDecimal_subsequence_limits.2.mapClusterPt

/-- The alternating sequence has no limit despite its two accumulation points. -/
theorem appendix2_alternating_no_limit :
    ¬∃ x : ℝ, Filter.Tendsto AlternatingDecimalSequence Filter.atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have he : StrictMono (fun n : ℕ => 2 * n) := by intro a b h; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro a b h; dsimp; omega
  have h1 := tendsto_nhds_unique (hx.comp he.tendsto_atTop)
    alternatingDecimal_subsequence_limits.1
  have h2 := tendsto_nhds_unique (hx.comp ho.tendsto_atTop)
    alternatingDecimal_subsequence_limits.2
  linarith

end Kreps.PreferenceProperties
