/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.DiagonalUtilityMean
import PreferenceProperties.BisymmetricMeanScale
import PreferenceProperties.NormalizedThreeFactorUtility

/-!
# Local additive scales from independent utility factors

Preparation for Kreps I, Proposition 2.14. The diagonal-inverse mean and its
dyadic cardinal scale give an actual additive representation on a compact
pair domain. The surrounding partial medial identity is enough; its proof
from normalized independent utility factors is supplied separately.
-/

namespace Kreps.PreferenceProperties

/-- The partial medial identity yields a continuous additive scale for pair comparisons. -/
theorem exists_pair_additive_scale_of_partialMedial
    {A B : Type*} [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
    [CompactSpace A] [DenselyOrdered A] [PreconnectedSpace A]
    (G : B → B → ℝ) (f : B → ℝ) (k : A → B) {lo hi : A}
    (hlohi : lo < hi) (hlo : ∀ x, lo ≤ x) (hhi : ∀ x, x ≤ hi)
    (hl : ∀ y, StrictMono (fun x => G (k x) (k y)))
    (hr : ∀ x, StrictMono (fun y => G (k x) (k y)))
    (hc : Continuous (fun p : A × A => G (k p.1) (k p.2)))
    (hs : ∀ x y, G (k x) (k y) = G (k y) (k x))
    (hsmall : ∀ x y, ∃ p, G (k x) (k y) = f p)
    (hmed : PartialUtilityMedial G f) (hd : Function.Injective (fun p => G p p)) :
    ∃ φ : A → ℝ, Continuous φ ∧ StrictMono φ ∧ φ lo = 0 ∧ φ hi = 1 ∧
      ∀ a b c d, G (k a) (k b) ≤ G (k c) (k d) ↔ φ a + φ b ≤ φ c + φ d := by
  let F : A → A → ℝ := fun x y => G (k x) (k y)
  have he : ∀ x y, ∃ z, F z z = F x y :=
    utilityDiagonal_attains_pair hl hr (hc.comp (continuous_id.prodMk continuous_id))
  let M := OrderedUtilityMean G f k he hl hr hs (fun _ _ => rfl) hsmall hmed hd
  have hmc : Continuous (fun p : A × A => M.mean p.1 p.2) :=
    diagonalUtilityMean_continuous he hl hr hc
  obtain ⟨φ, hφc, hφm, hφlo, hφhi, hφmean⟩ :=
    exists_continuous_bisymmetricMean_scale M hlohi hlo hhi hmc
  refine ⟨φ, hφc, hφm, hφlo, hφhi, ?_⟩
  intro a b c d
  calc
    G (k a) (k b) ≤ G (k c) (k d) ↔ M.mean a b ≤ M.mean c d :=
      diagonalUtilityMean_comparison he hl hr a b c d
    _ ↔ φ (M.mean a b) ≤ φ (M.mean c d) := hφm.le_iff_le.symm
    _ ↔ φ a + φ b ≤ φ c + φ d := by
      rw [hφmean, hφmean]
      exact div_le_div_iff_of_pos_right (by norm_num)

/-- Normalized independent factors supply the partial medial premise used above. -/
theorem normalized_threeFactor_partialMedial {B : Type*} {v : B × B × B → ℝ}
    {f : B → ℝ} {e : B} (hi : ThreeFactorIndependent (UtilityPref v))
    (hn : NormalizedThreeAxes v f e) :
    PartialUtilityMedial (fun x y => v (x, y, e)) f := by
  intro a b c d p q s t hp hq hs ht
  exact normalized_threeFactor_pair_medial hi hn a b c d p q s t hp hq hs ht

end Kreps.PreferenceProperties
