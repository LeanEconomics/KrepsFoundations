/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MeasureMixtures
import ChoiceUnderUncertainty.MixtureRepresentation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite atomic and compact-density probability laws

Kreps I, pp. 97–98. The source's weighted components are a nonnegative finite
atom vector and a nonnegative compactly supported continuous density. The
formula on every measurable set describes an actual Borel probability measure.
Singleton masses recover the atom vector. Integrals over measurable sets recover
the continuous component. The resulting domain is convex under measure mixtures.
-/

namespace Kreps.ChoiceUnderUncertainty

open MeasureTheory Convexity
open scoped ENNReal

attribute [local instance] BorelConvexSpace

/-- Evaluate a finite vector of atomic masses against any real test function. -/
noncomputable def AtomicFunctional (u : ℝ → ℝ) : (ℝ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ u

/-- Evaluation of a singleton indicator gives its atom mass. -/
theorem atomicFunctional_singleton (w : ℝ →₀ ℝ) (x : ℝ) :
    AtomicFunctional (({x} : Set ℝ).indicator (fun _ => 1)) w = w x := by
  classical
  change w.sum (fun y t => t * ({x} : Set ℝ).indicator (fun _ => 1) y) = _
  rw [Finsupp.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Set.indicator, hy]
  · simp

/-- A law on all measurable events, using its weighted finite atoms and weighted density. -/
structure AtomicDensityPresentation (p : ProbabilityMeasure ℝ) (w : ℝ →₀ ℝ) (f : ℝ → ℝ) : Prop where
  /-- Each atom has nonnegative mass. -/
  atoms_nonneg : 0 ≤ w
  /-- The weighted density is continuous. -/
  continuous : Continuous f
  /-- Its support stays in some compact set depending on the law. -/
  compact : HasCompactSupport f
  /-- The density is nonnegative everywhere. -/
  density_nonneg : ∀ x, 0 ≤ f x
  /-- Every event has its finite atomic mass plus its continuous-density integral. -/
  event : ∀ T : Set ℝ, MeasurableSet T → (p : Measure ℝ).real T =
    AtomicFunctional (T.indicator (fun _ => 1)) w + ∫ x in T, f x

/-- Individual atoms are exactly the singleton probabilities of the underlying measure. -/
theorem atomicDensity_singleton {p : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p w f) (x : ℝ) : (p : Measure ℝ).real {x} = w x := by
  rw [h.event {x} (measurableSet_singleton x), atomicFunctional_singleton]
  simp

/-- Both weighted components of an actual law are uniquely determined, also at mixture endpoints. -/
theorem atomicDensity_unique {p : ProbabilityMeasure ℝ} {v w : ℝ →₀ ℝ} {f g : ℝ → ℝ}
    (h : AtomicDensityPresentation p v f) (k : AtomicDensityPresentation p w g) :
    v = w ∧ f = g := by
  have he : v = w := Finsupp.ext fun x =>
    (atomicDensity_singleton h x).symm.trans (atomicDensity_singleton k x)
  subst w
  refine ⟨rfl, (h.continuous.ae_eq_iff_eq (μ := volume) k.continuous).mp ?_⟩
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (h.continuous.integrable_of_hasCompactSupport h.compact)
    (k.continuous.integrable_of_hasCompactSupport k.compact)
  intro T hT _
  linarith [h.event T hT, k.event T hT]

/-- Finite atomic mass and density mass add to one. -/
theorem atomicDensity_normalized {p : ProbabilityMeasure ℝ} {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p w f) :
    AtomicFunctional (fun _ => 1) w + ∫ x, f x = 1 := by
  simpa using (h.event Set.univ MeasurableSet.univ).symm

/-- Both weighted components mix by the same convex coefficients as the underlying measures. -/
theorem atomicDensity_mix (a : Weight) {p q : ProbabilityMeasure ℝ}
    {v w : ℝ →₀ ℝ} {f g : ℝ → ℝ}
    (h : AtomicDensityPresentation p v f) (k : AtomicDensityPresentation q w g) :
    AtomicDensityPresentation (Mix a p q) (a.val • v + (1 - a.val) • w)
      (fun x => a.val * f x + (1 - a.val) * g x) := by
  have ha := a.property.1
  have hb := sub_nonneg.mpr a.property.2
  refine ⟨add_nonneg (smul_nonneg ha h.atoms_nonneg) (smul_nonneg hb k.atoms_nonneg),
    (continuous_const.mul h.continuous).add (continuous_const.mul k.continuous), ?_,
    fun x => add_nonneg (mul_nonneg ha (h.density_nonneg x)) (mul_nonneg hb (k.density_nonneg x)),
    ?_⟩
  · exact (h.compact.mul_left (f := fun _ => a.val)).add
      (k.compact.mul_left (f := fun _ => 1 - a.val))
  · intro T hT
    have hfi : Integrable f volume := h.continuous.integrable_of_hasCompactSupport h.compact
    have hgi : Integrable g volume := k.continuous.integrable_of_hasCompactSupport k.compact
    rw [borelMix_event, h.event T hT, k.event T hT,
      integral_add (hfi.integrableOn.const_mul _) (hgi.integrableOn.const_mul _),
      integral_const_mul, integral_const_mul, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring

/-- The exact domain of Borel probabilities admitting a finite atomic and compact-density split. -/
def AtomicDensityDomain : Set (ProbabilityMeasure ℝ) :=
  {p | ∃ (w : ℝ →₀ ℝ) (f : ℝ → ℝ), AtomicDensityPresentation p w f}

/-- The domain in the printed example is closed under mixtures of its actual measures. -/
theorem atomicDensityDomain_isConvex : IsConvexSet ℝ AtomicDensityDomain := by
  apply IsConvexSet.of_convexCombPair_mem
  rintro a b ha hb hab p ⟨v, f, hf⟩ q ⟨w, g, hg⟩
  have he : b = 1 - a := by linarith
  subst b
  let t : Weight := ⟨a, ha, by linarith⟩
  exact ⟨_, _, atomicDensity_mix t hf hg⟩

/-- The convex structure on the source domain is inherited from Borel probability measures. -/
noncomputable abbrev atomicDensityConvexSpace : ConvexSpace ℝ AtomicDensityDomain :=
  .subtype _ atomicDensityDomain_isConvex

/-- The source functional equals one plus the atomic expectation of `x - 1`. -/
noncomputable def AtomicDensityIndex (p : AtomicDensityDomain) : ℝ :=
  AtomicFunctional (fun x => x - 1) (Classical.choose p.property) + 1

/-- The value can use any presentation because singleton masses determine the weighted atoms. -/
theorem atomicDensityIndex_eq (p : AtomicDensityDomain) {w : ℝ →₀ ℝ} {f : ℝ → ℝ}
    (h : AtomicDensityPresentation p.val w f) :
    AtomicDensityIndex p = AtomicFunctional (fun x => x - 1) w + 1 := by
  obtain ⟨g, hg⟩ := Classical.choose_spec p.property
  rw [AtomicDensityIndex, (atomicDensity_unique hg h).1]

/-- The source formula at atomic fraction `a` and ordinary simple lottery `q`. -/
theorem atomicDensityIndex_scaled (p : AtomicDensityDomain) (q : SimpleLottery ℝ) (a : ℝ)
    {f : ℝ → ℝ} (h : AtomicDensityPresentation p.val (a • q.weights) f) :
    AtomicDensityIndex p = a * ExpectedUtility id q + (1 - a) := by
  have he : AtomicFunctional (fun x => x - 1) q.weights = ExpectedUtility id q - 1 := by
    change (∑ x ∈ q.weights.support, q.weights x * (x - 1)) =
      (∑ x ∈ q.weights.support, q.weights x * x) - 1
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [show ∑ x ∈ q.weights.support, q.weights x = 1 from q.total]
  rw [atomicDensityIndex_eq p h, map_smul, he, smul_eq_mul]
  ring

/-- Finite mixtures preserve the weighted discrete plus continuous index. -/
theorem atomicDensityIndex_affine : @AffineInMix _ atomicDensityConvexSpace AtomicDensityIndex := by
  let _ := atomicDensityConvexSpace
  intro a p q
  obtain ⟨v, f, hf⟩ := p.property
  obtain ⟨w, g, hg⟩ := q.property
  have he : (Mix a p q).val = Mix a p.val q.val := subtypeVal_convexCombPair _
    atomicDensityDomain_isConvex a.val (1 - a.val) a.property.1 (sub_nonneg.mpr a.property.2)
    (by ring) p q
  have hp := atomicDensity_mix a hf hg
  rw [← he] at hp
  rw [atomicDensityIndex_eq _ hp, atomicDensityIndex_eq _ hf, atomicDensityIndex_eq _ hg,
    map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The model with weighted atomic mean and constant continuous value meets all three axioms. -/
theorem atomicDensityIndex_mixtureAxioms :
    @MixtureAxioms _ atomicDensityConvexSpace (UtilityPref AtomicDensityIndex) :=
  @mixtureAxioms_of_representation _ atomicDensityConvexSpace _ _ (fun _ _ => Iff.rfl)
    atomicDensityIndex_affine

end Kreps.ChoiceUnderUncertainty
