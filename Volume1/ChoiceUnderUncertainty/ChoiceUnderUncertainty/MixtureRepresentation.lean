/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.UnboundedCalibration
import ChoiceUnderUncertainty.LotteryEvaluation

/-!
# The mixture-space and expected-utility theorems

Kreps I, Propositions 5.3–5.4 and Problem 5.3, pp. 88–96, 118. Normalize two
strictly ranked anchors. For each pair of alternatives, one bounded preference
interval contains the pair, its mixtures, and the anchors. Its normalized local
utility agrees with each globally calibrated value, proving representation and
affinity even when preferences have no best or worst alternative.
-/

namespace Kreps.ChoiceUnderUncertainty

open Convexity Filter Topology

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- Problem 5.3: constructing affine utility without a best or a worst alternative. -/
theorem problem_5_3 (h : MixtureAxioms r) :
    ∃ u : Z → ℝ, Represents u r ∧ AffineInMix u := by
  classical
  by_cases hex : ∃ g b, Strict r g b
  · obtain ⟨g, b, hgb⟩ := hex
    choose u hu using exists_calibration h hgb
    have pair (x y : Z) : (r x y ↔ u y ≤ u x) ∧
        ∀ a : Weight, u (Mix a x y) = a.val * u x + (1 - a.val) * u y := by
      obtain ⟨H, L, hHL, hg, hb, hall⟩ := exists_preference_enclosure h.1 hgb [x, y]
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      obtain ⟨v, hvg, hvb, hv, ha⟩ := normalized_interval_utility h hHL hg hb hgb
      have he (z : Z) (hz : Between r H L z) : u z = v z :=
        calibration_eq_local h hg hb hz v hvg hvb hv ha (hu z)
      refine ⟨by rw [he x hx, he y hy]; exact hv x y hx hy, ?_⟩
      intro a
      rw [he _ (between_mix h hx hy a), he x hx, he y hy, ha a x y hx hy]
    exact ⟨u, fun x y => (pair x y).1, fun a x y => (pair x y).2 a⟩
  · refine ⟨fun _ => 0, fun x y => ?_, by intro a x y; simp⟩
    apply iff_of_true _ le_rfl
    by_contra hn
    exact hex ⟨y, x, (proposition_1_9a h.1.1 _ _).mpr hn⟩

/-- Any affine representation satisfies the exact primitive substitution and continuity axioms. -/
theorem mixtureAxioms_of_representation {u : Z → ℝ} (hu : Represents u r)
    (ha : AffineInMix u) : MixtureAxioms r := by
  have hs (x y : Z) : Strict r x y ↔ u y < u x := by
    rw [Strict, hu x y, hu y x, not_le]
    exact ⟨And.right, fun hh => ⟨hh.le, hh⟩⟩
  refine ⟨⟨fun x y => (le_total (u y) (u x)).imp (hu x y).mpr (hu y x).mpr,
    fun x y z hxy hyz => (hu x z).mpr (((hu y z).mp hyz).trans ((hu x y).mp hxy))⟩,
    ?_, ?_⟩
  · intro a x y z w
    simp only [hs, ha a y z, ha a x z, ha a y w, ha a x w, add_lt_add_iff_right]
  · intro x y hxy z
    have hg := (hs x y).mp hxy
    have hne : ∀ᶠ a : ℝ in 𝓝 1,
        u y < a * u x + (1 - a) * u z ∧ a * u y + (1 - a) * u z < u x := by
      apply Filter.Eventually.and
      · apply (isOpen_lt continuous_const (by fun_prop)).mem_nhds
        simpa using hg
      · apply (isOpen_lt (by fun_prop) continuous_const).mem_nhds
        simpa using hg
    obtain ⟨l, b, ⟨hl, hb⟩, hh⟩ := hne.exists_Ioo_subset
    let c := (max l 0 + 1) / 2
    have hm : max l 0 < 1 := max_lt hl zero_lt_one
    have hc₀ : 0 < c := by dsimp [c]; linarith [le_max_right l 0]
    have hc₁ : c < 1 := by dsimp [c]; linarith
    refine ⟨c, ⟨hc₀, hc₁⟩, fun a hca => ?_⟩
    have hla : l < a.val := by dsimp [c] at hca; linarith [le_max_left l 0]
    simp only [hs, ha a x z, ha a y z]
    exact hh (show a.val ∈ Set.Ioo l b from ⟨hla, a.property.2.trans_lt hb⟩)

/-- **Proposition 5.4:** complete primitive characterization on a general mixture space. -/
theorem proposition_5_4 : MixtureAxioms r ↔ ∃ u : Z → ℝ, Represents u r ∧ AffineInMix u :=
  ⟨problem_5_3, fun ⟨_, hu, ha⟩ => mixtureAxioms_of_representation hu ha⟩

/-- **Proposition 5.3:** expected utility on all simple lotteries over an arbitrary prize type. -/
theorem proposition_5_3 {X : Type*} {p : SimpleLottery X → SimpleLottery X → Prop} :
    MixtureAxioms p ↔ ∃ U : X → ℝ, Represents (ExpectedUtility U) p := by
  constructor
  · intro h
    obtain ⟨u, hu, ha⟩ := proposition_5_4.mp h
    refine ⟨fun x => u (PureLottery x), fun x y => ?_⟩
    rw [← affineInMix_eq_expectedUtility ha x, ← affineInMix_eq_expectedUtility ha y]
    exact hu x y
  · rintro ⟨U, hu⟩
    exact mixtureAxioms_of_representation hu (expectedUtility_affine U)

end Kreps.ChoiceUnderUncertainty
