/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RankCutUtility

/-!
# The general continuous-representation theorem

Kreps I, Proposition 2.9, pp. 35-38. Countable dense ranks and their rational
completion give a continuous utility without any monotonicity assumption.
Open strict contours prove continuity at every bundle, including extreme ranks.
The proof works on any separable connected space and is specialized below to
every finite-dimensional nonnegative orthant, including dimension zero.
-/

namespace Kreps.PreferenceProperties

variable {X : Type*} [TopologicalSpace X] {r : X → X → Prop}

/-- A bounded representation attaining all interior rational values has no discontinuous gaps. -/
theorem continuous_of_dense_rational_range {u : X → ℝ} (hu : Represents u r)
    (hc : ContinuousPreference r) (hb : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hq : ∀ q : ℚ, 0 < q → q < 1 → ∃ x, u x = (q : ℝ)) : Continuous u := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have ho := continuousPreference_openStrictContours hc
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change a < u x at hx
    by_cases ha : a < 0
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => ha.trans_le (hb y).1)
    · obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hx
      have hq0 : (0 : ℝ) < q := (le_of_not_gt ha).trans_lt haq
      have hq1 : (q : ℝ) < 1 := hqx.trans_le (hb x).2
      obtain ⟨z, hz⟩ := hq q (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      have hxz : Strict r x z := (strict_iff_utility_lt hu x z).mpr (hz.symm ▸ hqx)
      apply Filter.mem_of_superset ((ho z).1.mem_nhds hxz)
      intro y hy
      change a < u y
      have hzy := (strict_iff_utility_lt hu y z).mp hy
      rw [hz] at hzy
      exact haq.trans hzy
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change u x < a at hx
    by_cases ha : 1 < a
    · exact Filter.mem_of_superset Filter.univ_mem (fun y _ => (hb y).2.trans_lt ha)
    · obtain ⟨q, hxq, hqa⟩ := exists_rat_btwn hx
      have hq0 : (0 : ℝ) < q := (hb x).1.trans_lt hxq
      have hq1 : (q : ℝ) < 1 := hqa.trans_le (le_of_not_gt ha)
      obtain ⟨z, hz⟩ := hq q (by exact_mod_cast hq0) (by exact_mod_cast hq1)
      have hzx : Strict r z x := (strict_iff_utility_lt hu z x).mpr (hz.symm ▸ hxq)
      apply Filter.mem_of_superset ((ho z).2.mem_nhds hzx)
      intro y hy
      change u y < a
      have hyz := (strict_iff_utility_lt hu z y).mp hy
      rw [hz] at hyz
      exact hyz.trans hqa

/-- The completed rational-rank representation is continuous, even at its possible endpoints. -/
theorem rankCutUtility_continuous {v : X → ℝ} {D : Set X}
    (e : InteriorRankSet v D ≃o RationalUnit) (hs : StrictRankSeparator v D)
    (hv : Represents v r) (hc : ContinuousPreference r) : Continuous (RankCutUtility e) := by
  apply continuous_of_dense_rational_range (rankCutUtility_represents e hs hv) hc
    (fun x => ⟨rankCutUtility_nonneg e x, rankCutUtility_le_one e x⟩)
  intro q hq0 hq1
  exact rankCutUtility_attains_rationals e ⟨q, hq0, hq1⟩

/-- General Debreu representation on a connected separable domain, with a bounded utility. -/
theorem continuous_represents_of_continuous_connected [PreconnectedSpace X]
    [TopologicalSpace.SeparableSpace X] (hr : Rational r) (hc : ContinuousPreference r) :
    ∃ u : X → ℝ, Represents u r ∧ Continuous u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ 1 := by
  obtain ⟨v, hv⟩ := represents_of_continuous_connected hr hc
  by_cases hn : ∃ x y, v x < v y
  · obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense X
    have hs := dense_strictRankSeparator hr hc hv hd
    obtain ⟨e⟩ := interiorRanks_orderIso hD hs hn
    exact ⟨RankCutUtility e, rankCutUtility_represents e hs hv,
      rankCutUtility_continuous e hs hv hc,
      fun x => ⟨rankCutUtility_nonneg e x, rankCutUtility_le_one e x⟩⟩
  · refine ⟨fun _ => 0, ?_, continuous_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
    intro x y
    exact iff_of_true ((hv x y).mpr (le_of_not_gt (fun h => hn ⟨x, y, h⟩))) le_rfl

/-- **Proposition 2.9:** the full equivalence, with no monotonicity hypothesis. -/
theorem proposition_2_9 (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    ContinuousPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u := by
  constructor
  · intro hc
    let : PreconnectedSpace (NonnegativeOrthant k) :=
      isPreconnected_iff_preconnectedSpace.mp
        (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)).isPreconnected
    obtain ⟨u, hu, hc', _⟩ := continuous_represents_of_continuous_connected hr hc
    exact ⟨u, hu, hc'⟩
  · rintro ⟨u, hu, hc⟩
    exact proposition_2_9_forward hu hc

/-- The same equivalence using the common-radius metric continuity convention. -/
theorem proposition_2_9_metric (k : ℕ)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop} (hr : Rational r) :
    MetricContinuousPreference r ↔
      ∃ u : NonnegativeOrthant k → ℝ, Represents u r ∧ Continuous u :=
  continuousPreference_iff_metric.symm.trans (proposition_2_9 k hr)

end Kreps.PreferenceProperties
