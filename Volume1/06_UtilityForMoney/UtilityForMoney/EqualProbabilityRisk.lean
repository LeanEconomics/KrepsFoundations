/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.IncomeChoice

/-!
# Equally likely consumption gambles and concavity

Kreps I, footnote 12, p. 137. Continuity lets equally likely binary gambles
test full concavity. Along a segment subtract the chord joining the endpoint
utilities. A negative minimum would be the midpoint of an endpoint with zero
gap and a second point with no smaller gap, contradicting midpoint concavity.
-/

namespace Kreps.UtilityForMoney

/-- A continuous midpoint-concave gap vanishing at both endpoints is nonnegative throughout. -/
theorem midpoint_gap_nonneg (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1))
    (hm : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (f x + f y) / 2 ≤ f ((x + y) / 2)) (h₀ : f 0 = 0) (h₁ : f 1 = 0) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f z := by
  have hz : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have ho : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨t, ht, hlo⟩ := isCompact_Icc.exists_isMinOn ⟨0, hz⟩ hc
  suffices he : 0 ≤ f t from fun z h => he.trans (hlo h)
  rcases le_or_gt t (1/2) with h | h
  · have hv : 2*t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
    have hh := hm 0 hz _ hv
    rw [h₀, show (0 + 2*t)/2 = t by ring] at hh
    have hl : f t ≤ f (2*t) := hlo hv
    linarith
  · have hv : 2*t-1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
    have hh := hm _ hv 1 ho
    rw [h₁, show (2*t-1+1)/2 = t by ring] at hh
    have hl : f t ≤ f (2*t-1) := hlo hv
    linarith

/-- Under continuity, a weak preference for the sure midpoint in every fair binary gamble
gives Jensen's inequality for every mixing weight, including the endpoints. -/
theorem concavity_of_equal_probability_gambles {k : ℕ}
    (U : Demand.NonnegativeOrthant k → ℝ) (hU : Continuous U)
    (hm : ∀ x y, (U x + U y) / 2 ≤ U (Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ))
      x y (1 / 2) (by constructor <;> norm_num))) :
    Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) U := by
  intro x y a ha
  let z (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) := Demand.Mix
    (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) x y t ht
  let f (t : ℝ) := if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    U (z t ht) - (t * U x + (1-t) * U y) else 0
  have he (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      f t = U (z t ht) - (t * U x + (1-t) * U y) := dite_eq_left ht
  have hz : Continuous (fun t : Set.Icc (0 : ℝ) 1 => z t.val t.property) := by
    apply Continuous.subtype_mk
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 => t.val • x.val + (1-t.val) • y.val)
    fun_prop
  have hc : ContinuousOn f (Set.Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 => f t.val)
    simp only [fun t : Set.Icc (0 : ℝ) 1 => he t.val t.property]
    exact (hU.comp hz).sub ((continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const))
  have hmid (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
      (f v + f w)/2 ≤ f ((v+w)/2) := by
    have hav : (v+w)/2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hv.1, hw.1], by linarith [hv.2, hw.2]⟩
    have h := hm (z v hv) (z w hw)
    have hpos : (1/2 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
    have heq : Demand.Mix (convex_Ici (𝕜 := ℝ) (0 : Fin k → ℝ)) (z v hv) (z w hw)
        (1/2) hpos = z ((v+w)/2) hav := by
      ext i
      change 1/2 * (v*x.val i + (1-v)*y.val i) + (1-1/2) * (w*x.val i + (1-w)*y.val i) =
        ((v+w)/2) * x.val i + (1-(v+w)/2) * y.val i
      ring
    have h' := h.trans_eq (congrArg U heq)
    rw [he v hv, he w hw, he _ hav]
    linarith only [h']
  have h₀ : f 0 = 0 := by
    rw [he 0 (by norm_num)]
    simp [z, Demand.Mix]
  have h₁ : f 1 = 0 := by
    rw [he 1 (by norm_num)]
    simp [z, Demand.Mix]
  have h := midpoint_gap_nonneg f hc hmid h₀ h₁ a ha
  rw [he a ha] at h
  exact sub_nonneg.mp h

end Kreps.UtilityForMoney
