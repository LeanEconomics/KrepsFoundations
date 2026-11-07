/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.StochasticDominance
import Mathlib.Analysis.Convex.Slope

/-!
# Capped-linear tests for second-order dominance

Kreps I, Proposition 6.14(b) and Problem 6.6. On the union of two finite supports
an increasing concave utility can be interpolated by nonnegative combinations of
capped-linear tests and a constant. The induction removes the last segment's
slope before interpolating the preceding points. It allows arbitrary real prizes.
-/

namespace Kreps.UtilityForMoney

/-- Expectations of a sum with a scaled component distribute over a finite lottery. -/
theorem expectedUtility_add_scaled {X : Type*} (p : SimpleLottery X) (f g : X → ℝ) (a : ℝ) :
    ExpectedUtility (fun x => f x + a * g x) p = ExpectedUtility f p + a * ExpectedUtility g p := by
  unfold ExpectedUtility Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- All earlier secants of a concave function dominate the last segment's slope. -/
theorem last_secant_le {U : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ U)
    {x y b r : ℝ} (hxy : x < y) (hyb : y ≤ b) (hbr : b < r) :
    (U r - U b) / (r - b) ≤ (U y - U x) / (y - x) := by
  rcases hyb.eq_or_lt with rfl | h
  · exact hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) hxy hbr
  · exact (hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) h hbr).trans
      (hc.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) hxy h)

/-- Interpolate the specified concave utility on a finite set while preserving the capped tests. -/
theorem exists_cap_interpolant (p q : SimpleLottery ℝ)
    (ht : ∀ r : ℝ, ExpectedUtility (fun x => min x r) q ≤ ExpectedUtility (fun x => min x r) p)
    (T : Finset ℝ) (U : ℝ → ℝ) (hc : ConcaveOn ℝ Set.univ U) (hm : MonotoneOn U T) :
    ∃ f : ℝ → ℝ, ExpectedUtility f q ≤ ExpectedUtility f p ∧ (∀ x ∈ T, f x = U x) ∧
      ∀ v w, (∀ t ∈ T, t ≤ v) → (∀ t ∈ T, t ≤ w) → f v = f w := by
  classical
  induction T using Finset.induction_on_max generalizing U with
  | empty =>
    exact ⟨fun _ => 0, by simp [expectedUtility_const], by simp, by simp⟩
  | insert r T htop ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · refine ⟨fun _ => U r, by simp [expectedUtility_const], ?_, by simp⟩
      simp
    let b := T.max' hT
    have hb : b ∈ T := T.max'_mem hT
    have hbr : b < r := htop b hb
    let m := (U r - U b) / (r - b)
    have hm₀ : 0 ≤ m := div_nonneg (sub_nonneg.mpr (hm
      (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hbr.le)) (sub_nonneg.mpr hbr.le)
    have hmr : m * (r - b) = U r - U b := div_mul_cancel₀ _ (sub_ne_zero.mpr hbr.ne')
    let V (z : ℝ) := U z - m * z
    have hcV : ConcaveOn ℝ Set.univ V := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a c ha hh hsum
      have h := hc.2 hx hy ha hh hsum
      simp only [smul_eq_mul, V] at *
      linarith only [h]
    have hmV : MonotoneOn V T := by
      intro x hx y hy hxy
      rcases hxy.eq_or_lt with rfl | h
      · exact le_rfl
      · have hs := last_secant_le hc h (T.le_max' _ hy) hbr
        have he := (le_div_iff₀ (sub_pos.mpr h)).mp hs
        change U x - m * x ≤ U y - m * y
        change m * (y - x) ≤ U y - U x at he
        linarith
    obtain ⟨f, hpass, hval, hflat⟩ := ih V hcV hmV
    let F (x : ℝ) := f x + m * min x r
    refine ⟨F, ?_, ?_, ?_⟩
    · change ExpectedUtility (fun x => f x + m * min x r) q ≤ _
      rw [expectedUtility_add_scaled, show ExpectedUtility F p =
        ExpectedUtility f p + m * ExpectedUtility (fun x => min x r) p from
        expectedUtility_add_scaled p f _ m]
      exact add_le_add hpass (mul_le_mul_of_nonneg_left (ht r) hm₀)
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have he := hflat z b (fun t ht => (htop t ht).le) (fun t ht => T.le_max' t ht)
        dsimp only [F]
        rw [min_self, he, hval b hb]
        dsimp only [V]
        linarith
      · dsimp only [F]
        rw [min_eq_left (htop z hz).le, hval z hz]
        dsimp only [V]
        ring
    · intro v w hv hw
      dsimp only [F]
      rw [min_eq_right (hv r (Finset.mem_insert_self _ _)),
        min_eq_right (hw r (Finset.mem_insert_self _ _)),
        hflat v w (fun t ht => hv t (Finset.mem_insert_of_mem ht))
          (fun t ht => hw t (Finset.mem_insert_of_mem ht))]

/-- Expected shortfalls at all thresholds characterize the increasing concave order. -/
theorem secondOrder_iff_shortfalls (p q : SimpleLottery ℝ) : SecondOrderDominates p q ↔
    ∀ r, ExpectedShortfall p r ≤ ExpectedShortfall q r := by
  refine ⟨fun h => expectedShortfall_le_of_secondOrder h, ?_⟩
  intro hs U hm hc
  have ht (r : ℝ) : ExpectedUtility (fun x => min x r) q ≤
      ExpectedUtility (fun x => min x r) p := by
    have he : (fun x : ℝ => min x r) = fun x => -1 * max (r - x) 0 + r := by
      funext x
      rcases le_total x r with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]; ring
      · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]; ring
    rw [he, expectedUtility_affine_payoff, expectedUtility_affine_payoff]
    have h := hs r
    unfold ExpectedShortfall at h
    linarith
  let T := p.weights.support ∪ q.weights.support
  obtain ⟨f, hp, hv, _⟩ := exists_cap_interpolant p q ht T U hc (fun _ _ _ _ h => hm h)
  have he (w : SimpleLottery ℝ) (hw : w.weights.support ⊆ T) :
      ExpectedUtility f w = ExpectedUtility U w :=
    Finset.sum_congr rfl fun x hx => congrArg (w.weights x * ·) (hv x (hw hx))
  rwa [he p Finset.subset_union_left, he q Finset.subset_union_right] at hp

end Kreps.UtilityForMoney
