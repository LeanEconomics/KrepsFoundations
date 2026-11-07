/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import UtilityForMoney.MonetaryLotteries

/-!
# Comparing risk aversion

Kreps I, Definition 6.6 and Proposition 6.7, pp. 127–129. The comparison
quantifies over every lottery and every sure prize. The inverse of the
second utility is used only on its attained range, which is convex by
continuity of that utility on the monetary interval.
-/

namespace Kreps.UtilityForMoney

/-- **Definition 6.6:** acceptance by the more risk-averse decision maker entails acceptance
by the other one, at every sure prize. -/
def MoreRiskAverse (S : Set ℝ) (W V : ℝ → ℝ) : Prop :=
  ∀ (p : SimpleLottery S) (x : S), W x ≤ ExpectedUtility (fun y : S => W y) p →
    V x ≤ ExpectedUtility (fun y : S => V y) p

/-- The transformation taking the utility scale of `V` to that of `W`. -/
noncomputable def UtilityTransform (S : Set ℝ) (W V : ℝ → ℝ) (t : ℝ) : ℝ :=
  W (Function.invFunOn V S t)

/-- At each attained utility value the transform returns the corresponding first utility. -/
theorem utilityTransform_apply {S : Set ℝ} {V : ℝ → ℝ} (W : ℝ → ℝ)
    (hV : StrictMonoOn V S) {x : ℝ} (hx : x ∈ S) :
    UtilityTransform S W V (V x) = W x :=
  congrArg W (hV.injOn.leftInvOn_invFunOn hx)

/-- The utility transform is strictly increasing on precisely the relevant range. -/
theorem utilityTransform_strictMonoOn {S : Set ℝ} {V W : ℝ → ℝ}
    (hV : StrictMonoOn V S) (hW : StrictMonoOn W S) :
    StrictMonoOn (UtilityTransform S W V) (V '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [utilityTransform_apply W hV hx, utilityTransform_apply W hV hy]
  exact hW hx hy ((hV.lt_iff_lt hx hy).mp hxy)

/-- **Proposition 6.7:** increased risk aversion is equivalent to a concave utility transform. -/
theorem proposition_6_7 {S : Set ℝ} (hS : Convex ℝ S) {W V : ℝ → ℝ}
    (hW : StrictMonoOn W S) (hV : StrictMonoOn V S)
    (hWc : ContinuousOn W S) (hVc : ContinuousOn V S) :
    MoreRiskAverse S W V ↔ ConcaveOn ℝ (V '' S) (UtilityTransform S W V) := by
  let T := UtilityTransform S W V
  have hT (x : S) : T (V x) = W x := utilityTransform_apply W hV x.property
  have hrange : Convex ℝ (V '' S) := (hS.isPreconnected.image V hVc).convex
  have hmem (x : S) : V x ∈ V '' S := Set.mem_image_of_mem V x.property
  have hinc := utilityTransform_strictMonoOn hV hW
  constructor
  · intro h
    refine ⟨hrange, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
    let x : S := ⟨v, hv⟩
    let y : S := ⟨w, hw⟩
    have hI : a ∈ Set.Icc 0 1 := ⟨ha, by linarith⟩
    let p := BinaryLottery x y a hI
    obtain ⟨c, hc⟩ := proposition_6_5_exists hS hWc p
    have hp := h p c hc.le
    have hmean := expectedUtility_mem_of_convex hrange (fun t : S => V t) hmem p
    have hbound := hinc.monotoneOn (hmem c) hmean hp
    change T (V c) ≤ T (ExpectedUtility (fun t : S => V t) p) at hbound
    change W c = ExpectedUtility (fun t : S => W t) p at hc
    rw [hT c, hc] at hbound
    dsimp only [p] at hbound
    rw [expectedUtility_binary, expectedUtility_binary] at hbound
    change a * T (V x) + b * T (V y) ≤ T (a * V x + b * V y)
    rw [hT x, hT y]
    simpa only [show 1 - a = b by linarith] using hbound
  · intro hc p x hx
    have hj := expectedUtility_jensen hc (fun t : S => V t) hmem p
    change ExpectedUtility (fun t : S => T (V t)) p ≤
      T (ExpectedUtility (fun t : S => V t) p) at hj
    simp only [hT] at hj
    have hm := expectedUtility_mem_of_convex hrange (fun t : S => V t) hmem p
    apply (hinc.le_iff_le (hmem x) hm).mp
    change T (V x) ≤ _
    rw [hT x]
    exact hx.trans hj

end Kreps.UtilityForMoney
