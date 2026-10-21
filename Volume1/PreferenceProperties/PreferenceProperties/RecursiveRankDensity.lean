/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.RecursiveRanks
import PreferenceProperties.DensePreferenceRanks
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Density of the recursively assigned values

Kreps I, Problem 2.14(e), p. 49. The first point inserted between two adjacent
assigned ranks receives their midpoint. If the original sampled order has a rank
strictly between any two distinct ranks, this midpoint rule rules out gaps in the
closure of the numerical range.
-/

namespace Kreps.PreferenceProperties

/-- An order-dense enumeration remains order-dense after the recursive reassignment. -/
theorem recursiveRank_has_between (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j)
    {i j : ℕ} (hij : RecursiveRank v i < RecursiveRank v j) :
    ∃ k, RecursiveRank v i < RecursiveRank v k ∧ RecursiveRank v k < RecursiveRank v j := by
  obtain ⟨k, hik, hkj⟩ := hd i j ((recursiveRank_lt_iff v i j).mp hij)
  exact ⟨k, (recursiveRank_lt_iff v i k).mpr hik, (recursiveRank_lt_iff v k j).mpr hkj⟩

/-- The first insertion into a gap of a finite prefix must be the gap's midpoint. -/
theorem recursiveRank_first_between (v : ℕ → ℝ) (i j N : ℕ) (hiN : i ≤ N) (hjN : j ≤ N)
    (hgap : ∀ k ≤ N, ¬ (RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j))
    (hne : ∃ k, RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j) :
    ∃ k, RecursiveRank v k = (RecursiveRank v i + RecursiveRank v j) / 2 := by
  classical
  let n := Nat.find hne
  have hn : RecursiveRank v i < RecursiveRank v n ∧ RecursiveRank v n < RecursiveRank v j :=
    Nat.find_spec hne
  have hprior : ∀ k < n, ¬ (RecursiveRank v i < RecursiveRank v k ∧
      RecursiveRank v k < RecursiveRank v j) := fun _ hk => Nat.find_min hne hk
  have hNn : N < n := by
    by_contra h
    exact hgap n (Nat.le_of_not_gt h) hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  let vp : Fin (m + 1) → ℝ := fun k => v k
  let up : Fin (m + 1) → ℝ := fun k => RecursiveRank v k
  let i' : Fin (m + 1) := ⟨i, by omega⟩
  let j' : Fin (m + 1) := ⟨j, by omega⟩
  have he : RecursiveRank v n = InsertedRank vp up (v n) := by
    simpa only [hm] using recursiveRank_succ v m
  have hil : vp i' < v n := (recursiveRank_lt_iff v i n).mp hn.1
  have hjh : v n < vp j' := (recursiveRank_lt_iff v n j).mp hn.2
  have hnt : ¬ ∃ k, vp k = v n := by
    rintro ⟨k, hk⟩
    have heq : RecursiveRank v k = RecursiveRank v n := (recursiveRank_eq_iff v k n).mpr hk
    exact hprior k (by have := k.isLt; omega) (by simpa only [heq] using hn)
  have hmax : sSup (PreviousLowerRanks vp up (v n)) = RecursiveRank v i := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨i', hil, rfl⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    by_contra h
    have hleft : RecursiveRank v i < RecursiveRank v k := lt_of_not_ge h
    have hright : RecursiveRank v k < RecursiveRank v n :=
      (recursiveRank_lt_iff v k n).mpr hk
    exact hprior k (by have := k.isLt; omega) ⟨hleft, hright.trans hn.2⟩
  have hmin : sInf (PreviousUpperRanks vp up (v n)) = RecursiveRank v j := by
    apply IsLeast.csInf_eq
    refine ⟨⟨j', hjh, rfl⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    by_contra h
    have hright : RecursiveRank v k < RecursiveRank v j := lt_of_not_ge h
    have hleft : RecursiveRank v n < RecursiveRank v k :=
      (recursiveRank_lt_iff v n k).mpr hk
    exact hprior k (by have := k.isLt; omega) ⟨hn.1.trans hleft, hright⟩
  refine ⟨n, ?_⟩
  rw [he, insertedRank_between hnt ⟨i', hil⟩ ⟨j', hjh⟩, hmax, hmin]

/-- No open interval between assigned values can be missing from their closure. -/
theorem recursiveRank_between_mem_closure (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j)
    {i j : ℕ} {r : ℝ} (hi : RecursiveRank v i < r) (hj : r < RecursiveRank v j) :
    r ∈ closure (Set.range (RecursiveRank v)) := by
  classical
  let u := RecursiveRank v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  by_contra hmissing
  have hdist : ∀ n, ε ≤ |u n - r| := by
    intro n
    have h := not_lt.mpr (le_of_not_gt (fun hn =>
      hmissing ⟨u n, Set.mem_range_self n, hn⟩))
    simpa only [Real.dist_eq, abs_sub_comm, not_lt] using h
  have hne : ∀ n, u n ≠ r := by
    intro n hn
    have h := hdist n
    rw [hn, sub_self, abs_zero] at h
    linarith
  let L : Set ℝ := Set.range u ∩ Set.Iio r
  let H : Set ℝ := Set.range u ∩ Set.Ioi r
  have hLn : L.Nonempty := ⟨u i, Set.mem_range_self i, hi⟩
  have hHn : H.Nonempty := ⟨u j, Set.mem_range_self j, hj⟩
  have hLb : BddAbove L := ⟨r, fun _ hz => hz.2.le⟩
  have hHb : BddBelow H := ⟨r, fun _ hz => hz.2.le⟩
  let l := sSup L
  let h := sInf H
  have hll : l ≤ r - ε := by
    apply csSup_le hLn
    rintro y ⟨⟨n, rfl⟩, hn⟩
    have h := hdist n
    rw [abs_of_neg (sub_neg.mpr hn)] at h
    linarith
  have hhh : r + ε ≤ h := by
    apply le_csInf hHn
    rintro y ⟨⟨n, rfl⟩, hn⟩
    have h := hdist n
    rw [abs_of_pos (sub_pos.mpr hn)] at h
    linarith
  have hlh : l < h := by linarith
  let δ := (h - l) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨a, haL, haNear⟩ := exists_lt_of_lt_csSup hLn (show l - δ < l by linarith)
  obtain ⟨b, hbH, hbNear⟩ := exists_lt_of_csInf_lt hHn (show h < h + δ by linarith)
  obtain ⟨ia, hia⟩ := haL.1
  obtain ⟨ib, hib⟩ := hbH.1
  let N := max ia ib
  let up : Fin (N + 1) → ℝ := fun k => u k
  let LP : Set ℝ := up '' {k | up k < r}
  let HP : Set ℝ := up '' {k | r < up k}
  let ia' : Fin (N + 1) := ⟨ia, Nat.lt_succ_of_le (le_max_left ia ib)⟩
  let ib' : Fin (N + 1) := ⟨ib, Nat.lt_succ_of_le (le_max_right ia ib)⟩
  have hialow : up ia' < r := by
    change u ia < r
    rw [hia]
    exact haL.2
  have hibhigh : r < up ib' := by
    change r < u ib
    rw [hib]
    exact hbH.2
  have hLPn : LP.Nonempty := ⟨a, ia', hialow, hia⟩
  have hHPn : HP.Nonempty := ⟨b, ib', hibhigh, hib⟩
  have hLPf : LP.Finite := (Set.toFinite _).image up
  have hHPf : HP.Finite := (Set.toFinite _).image up
  obtain ⟨ip, hip, heip⟩ := hLPn.csSup_mem hLPf
  obtain ⟨jp, hjp, hejp⟩ := hHPn.csInf_mem hHPf
  have hipNear : l - δ < up ip := by
    have haLe' : a ≤ sSup LP := le_csSup hLPf.bddAbove ⟨ia', hialow, hia⟩
    rw [← heip] at haLe'
    exact haNear.trans_le haLe'
  have hjpNear : up jp < h + δ := by
    have hbLe : sInf HP ≤ b := csInf_le hHPf.bddBelow ⟨ib', hibhigh, hib⟩
    rw [← hejp] at hbLe
    exact hbLe.trans_lt hbNear
  have hipBound : up ip ≤ l := le_csSup hLb ⟨Set.mem_range_self ip.val, hip⟩
  have hjpBound : h ≤ up jp := csInf_le hHb ⟨Set.mem_range_self jp.val, hjp⟩
  have hgap : ∀ k ≤ N, ¬ (u ip < u k ∧ u k < u jp) := by
    intro k hk hbetween
    let k' : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    rcases lt_or_gt_of_ne (hne k) with hkr | hrk
    · have hkLe : up k' ≤ sSup LP := le_csSup hLPf.bddAbove ⟨k', hkr, rfl⟩
      rw [← heip] at hkLe
      exact not_lt_of_ge hkLe hbetween.1
    · have hkLe : sInf HP ≤ up k' := csInf_le hHPf.bddBelow ⟨k', hrk, rfl⟩
      rw [← hejp] at hkLe
      exact not_lt_of_ge hkLe hbetween.2
  have hbetween := recursiveRank_has_between v hd (show u ip < u jp from hip.trans hjp)
  obtain ⟨k, hk⟩ := recursiveRank_first_between v ip jp N
    (Nat.le_of_lt_succ ip.isLt) (Nat.le_of_lt_succ jp.isLt) hgap hbetween
  have hmidlo : l < u k := by
    change u k = (up ip + up jp) / 2 at hk
    dsimp [δ] at hipNear hjpNear
    linarith
  have hmidhi : u k < h := by
    change u k = (up ip + up jp) / 2 at hk
    dsimp [δ] at hipNear hjpNear
    linarith
  rcases lt_or_gt_of_ne (hne k) with hkr | hrk
  · have hkLe : u k ≤ l := le_csSup hLb ⟨Set.mem_range_self k, hkr⟩
    exact not_lt_of_ge hkLe hmidlo
  · have hkLe : h ≤ u k := csInf_le hHb ⟨Set.mem_range_self k, hrk⟩
    exact not_lt_of_ge hkLe hmidhi

/-- The smallest interval containing all values of the recursive assignment. -/
def RecursiveRankInterval (v : ℕ → ℝ) : Set ℝ :=
  {t | ∃ i j, RecursiveRank v i ≤ t ∧ t ≤ RecursiveRank v j}

/-- Every assigned value belongs to the containing interval. -/
theorem recursiveRank_range_subset_interval (v : ℕ → ℝ) :
    Set.range (RecursiveRank v) ⊆ RecursiveRankInterval v := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, n, le_rfl, le_rfl⟩

/-- The containing set really is an interval. -/
theorem recursiveRankInterval_ordConnected (v : ℕ → ℝ) :
    Set.OrdConnected (RecursiveRankInterval v) := by
  constructor
  rintro x ⟨i, _, hix, _⟩ y ⟨_, j, _, hyj⟩ z ⟨hxz, hzy⟩
  exact ⟨i, j, hix.trans hxz, hzy.trans hyj⟩

/-- Every interval containing all assigned values contains this interval. -/
theorem recursiveRankInterval_minimal (v : ℕ → ℝ) {S : Set ℝ}
    (hS : Set.OrdConnected S) (hrange : Set.range (RecursiveRank v) ⊆ S) :
    RecursiveRankInterval v ⊆ S := by
  rintro t ⟨i, j, hit, htj⟩
  exact hS.out (hrange (Set.mem_range_self i)) (hrange (Set.mem_range_self j)) ⟨hit, htj⟩

/-- The closure of the assigned values contains every point of their smallest interval. -/
theorem recursiveRankInterval_subset_closure (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j) :
    RecursiveRankInterval v ⊆ closure (Set.range (RecursiveRank v)) := by
  rintro t ⟨i, j, hit, htj⟩
  rcases hit.eq_or_lt with he | hi
  · exact he ▸ subset_closure (Set.mem_range_self i)
  rcases htj.eq_or_lt with he | hj
  · exact he.symm ▸ subset_closure (Set.mem_range_self j)
  exact recursiveRank_between_mem_closure v hd hi hj

/-- Relative density of the recursively assigned values in their smallest containing interval. -/
theorem recursiveRank_dense_in_interval (v : ℕ → ℝ)
    (hd : ∀ i j, v i < v j → ∃ k, v i < v k ∧ v k < v j) :
    DenseRange (Set.inclusion (recursiveRank_range_subset_interval v)) :=
  (denseRange_inclusion_iff _).mpr (recursiveRankInterval_subset_closure v hd)

/-- **Problem 2.14(e):** the assigned values are dense in their smallest containing interval. -/
theorem problem_2_14e {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {r : X → X → Prop} {v : X → ℝ} (hr : Rational r) (hc : ContinuousPreference r)
    (hv : Represents v r) (q : ℕ → X) (hq : DenseRange q) :
    DenseRange (Set.inclusion (recursiveRank_range_subset_interval (v ∘ q))) := by
  apply recursiveRank_dense_in_interval
  intro i j hij
  obtain ⟨x, ⟨k, rfl⟩, hik, hkj⟩ := dense_strictRankSeparator hr hc hv hq (q i) (q j) hij
  exact ⟨k, hik, hkj⟩

end Kreps.PreferenceProperties
