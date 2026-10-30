/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RobinsonCrusoe
import Mathlib.Analysis.Convex.Function

/-!
# Convexity and two uniqueness routes for Robinson Crusoe

Kreps I, Problem 3.14(b-c), p. 66. Concave production, concave utility, and
monotonicity in future consumption make the planting objective concave. Strict
concavity of utility is one sufficient uniqueness condition. Alternatively,
strictly concave production and strictly increasing future utility suffice.
Production is only required to be nondecreasing on its nonnegative domain,
with zero output from zero planting, as in the source.
-/

namespace Kreps.ConsumerDemand

open scoped NNReal

/-- Future consumption weakly increases utility at a fixed nonnegative current consumption. -/
def MonotoneFutureUtility (U : ℝ × ℝ → ℝ) : Prop :=
  ∀ c, 0 ≤ c → MonotoneOn (fun z => U (c, z)) (Set.Ici 0)

/-- Future consumption strictly increases utility at every nonnegative current consumption. -/
def StrictlyMonotoneFutureUtility (U : ℝ × ℝ → ℝ) : Prop :=
  ∀ c, 0 ≤ c → StrictMonoOn (fun z => U (c, z)) (Set.Ici 0)

/-- The source's production assumptions guarantee nonnegative future consumption. -/
theorem crusoe_production_nonneg {f : ℝ → ℝ} (hm : MonotoneOn f (Set.Ici 0))
    (h0 : f 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  rwa [h0] at h

/-- A feasible planting quantity gives a nonnegative two-period consumption stream. -/
theorem crusoe_stream_nonneg {f : ℝ → ℝ} (hm : MonotoneOn f (Set.Ici 0))
    (h0 : f 0 = 0) (e : ℝ≥0) {x : ℝ} (hx : x ∈ CrusoeFeasible e) :
    ((e : ℝ) - x, f x) ∈ Set.Ici (0 : ℝ × ℝ) :=
  ⟨sub_nonneg.mpr hx.2, crusoe_production_nonneg hm h0 hx.1⟩

/-- Concavity of production and utility composes through nondecreasing future utility. -/
theorem crusoeObjective_concave {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : ConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    ConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hmix : s * x + t * z ∈ CrusoeFeasible e := (convex_Icc _ _) hx hz hs ht hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hs ht hst
  have hfconc := hf.2 hx.1 hz.1 hs ht hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs hxU.2) (mul_nonneg ht hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) ≤ _
  change _ ≤ U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans hmono

/-- Strict concavity of utility gives strict concavity of the planting objective. -/
theorem crusoeObjective_strictConcave_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : StrictConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz hne s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hpair : ((e : ℝ) - x, f x) ≠ ((e : ℝ) - z, f z) := by
    intro he
    have h := congrArg Prod.fst he
    exact hne (by dsimp at h; linarith)
  have hmix : s * x + t * z ∈ CrusoeFeasible e :=
    (convex_Icc _ _) hx hz hs.le ht.le hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hpair hs ht hst
  have hfconc := hf.2 hx.1 hz.1 hs.le ht.le hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs.le hxU.2) (mul_nonneg ht.le hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) < _
  change _ < U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans_le hmono

/-- Strict production concavity suffices when utility strictly values future consumption. -/
theorem crusoeObjective_strictConcave_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) (e : ℝ≥0) :
    StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz hne s t hs ht hst
  have hxU := crusoe_stream_nonneg hm h0 e hx
  have hzU := crusoe_stream_nonneg hm h0 e hz
  have hmix : s * x + t * z ∈ CrusoeFeasible e :=
    (convex_Icc _ _) hx hz hs.le ht.le hst
  have hfirst : (e : ℝ) - (s * x + t * z) = s * ((e : ℝ) - x) + t * ((e : ℝ) - z) := by
    nlinarith
  have hconc := hU.2 hxU hzU hs.le ht.le hst
  have hfconc := hf.2 hx.1 hz.1 hne hs ht hst
  have hfuture : 0 ≤ s * f x + t * f z :=
    add_nonneg (mul_nonneg hs.le hxU.2) (mul_nonneg ht.le hzU.2)
  have hmono := hUm ((e : ℝ) - (s * x + t * z)) (sub_nonneg.mpr hmix.2)
    hfuture (crusoe_production_nonneg hm h0 hmix.1) hfconc
  change s * U ((e : ℝ) - x, f x) + t * U ((e : ℝ) - z, f z) < _
  change _ ≤ U (s * ((e : ℝ) - x) + t * ((e : ℝ) - z), s * f x + t * f z) at hconc
  rw [← hfirst] at hconc
  exact hconc.trans_lt hmono

/-- **Problem 3.14(b):** these primitive concavity assumptions give a convex solution set. -/
theorem problem_3_14b {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hU : ConcaveOn ℝ (Set.Ici 0) U) (hUm : MonotoneFutureUtility U) (e : ℝ≥0) :
    Convex ℝ (CrusoeDemand f U e) := by
  have hc := crusoeObjective_concave hm h0 hf hU hUm e
  intro x hx z hz s t hs ht hst
  refine ⟨hc.1 hx.1 hz.1 hs ht hst, fun w hw => ?_⟩
  have hconc := hc.2 hx.1 hz.1 hs ht hst
  have hxw := mul_le_mul_of_nonneg_left (hx.2 w hw) hs
  have hzw := mul_le_mul_of_nonneg_left (hz.2 w hw) ht
  change s * CrusoeObjective f U e x + t * CrusoeObjective f U e z ≤ _ at hconc
  have hwid : s * CrusoeObjective f U e w + t * CrusoeObjective f U e w =
      CrusoeObjective f U e w := by rw [← add_mul, hst, one_mul]
  linarith

/-- A strictly concave planting objective has at most one maximizer. -/
theorem crusoeDemand_subsingleton_of_strictConcave {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    {e : ℝ≥0} (hc : StrictConcaveOn ℝ (CrusoeFeasible e) (CrusoeObjective f U e)) :
    (CrusoeDemand f U e).Subsingleton := by
  intro x hx z hz
  exact hc.eq_of_isMaxOn hx.2 hz.2 hx.1 hz.1

/-- **Problem 3.14(c), first route:** strict utility concavity plus continuity gives uniqueness. -/
theorem problem_3_14c_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hU : StrictConcaveOn ℝ (Set.Ici 0) U)
    (hUm : MonotoneFutureUtility U) (e : ℝ≥0) : ∃! x, x ∈ CrusoeDemand f U e := by
  obtain ⟨x, hx⟩ := problem_3_14a hfc hUc e
  have hs := crusoeDemand_subsingleton_of_strictConcave
    (crusoeObjective_strictConcave_utility hm h0 hf hU hUm e)
  exact ⟨x, hx, fun z hz => hs hz hx⟩

/-- **Problem 3.14(c), second route:** strict production concavity also gives uniqueness. -/
theorem problem_3_14c_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) (e : ℝ≥0) : ∃! x, x ∈ CrusoeDemand f U e := by
  obtain ⟨x, hx⟩ := problem_3_14a hfc hUc e
  have hs := crusoeDemand_subsingleton_of_strictConcave
    (crusoeObjective_strictConcave_production hm h0 hf hU hUm e)
  exact ⟨x, hx, fun z hz => hs hz hx⟩

/-- **Problem 3.14(d):** the strict-utility assumptions also ensure lower semicontinuous demand. -/
theorem problem_3_14d_lower_utility {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hU : StrictConcaveOn ℝ (Set.Ici 0) U)
    (hUm : MonotoneFutureUtility U) : SequentialLower (CrusoeDemand f U) := by
  obtain ⟨_, _, _, hl⟩ := crusoeDemand_continuous_of_unique hfc hUc (fun e =>
    crusoeDemand_subsingleton_of_strictConcave
      (crusoeObjective_strictConcave_utility hm h0 hf hU hUm e))
  exact hl

/-- **Problem 3.14(d):** the strict-production assumptions likewise give lower semicontinuity. -/
theorem problem_3_14d_lower_production {f : ℝ → ℝ} {U : ℝ × ℝ → ℝ}
    (hfc : Continuous f) (hUc : Continuous U) (hm : MonotoneOn f (Set.Ici 0)) (h0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hUm : StrictlyMonotoneFutureUtility U) : SequentialLower (CrusoeDemand f U) := by
  obtain ⟨_, _, _, hl⟩ := crusoeDemand_continuous_of_unique hfc hUc (fun e =>
    crusoeDemand_subsingleton_of_strictConcave
      (crusoeObjective_strictConcave_production hm h0 hf hU hUm e))
  exact hl

end Kreps.ConsumerDemand
