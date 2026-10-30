/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Correspondences and parametric maxima

Kreps I, Appendix 4, pp. 471-477. The book's upper semicontinuity is the
sequential closed-graph condition. It must not be confused with open-set upper
hemicontinuity in the absence of a local compact bound. These general lemmas
provide the existence and limit steps used in the maximum theorem.
-/

namespace Kreps.ConsumerDemand

open Filter Set
open scoped Topology

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- Definition A4.2a: membership is preserved under simultaneous sequential limits. -/
def SequentialUpper (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (x : ℕ → X) (p₀ : P) (x₀ : X),
    Tendsto p atTop (𝓝 p₀) → Tendsto x atTop (𝓝 x₀) →
    (∀ n, x n ∈ A (p n)) → x₀ ∈ A p₀

/-- Definition A4.2b: every feasible limit point has a feasible companion sequence. -/
def SequentialLower (A : P → Set X) : Prop :=
  ∀ (p : ℕ → P) (p₀ : P), Tendsto p atTop (𝓝 p₀) →
    ∀ x₀ ∈ A p₀, ∃ x : ℕ → X, (∀ᶠ n in atTop, x n ∈ A (p n)) ∧
      Tendsto x atTop (𝓝 x₀)

/-- The maximizing correspondence for an objective depending on the parameter. -/
def ParametricMaxima (A : P → Set X) (F : P → X → ℝ) (p : P) : Set X :=
  {x | x ∈ A p ∧ ∀ y ∈ A p, F p y ≤ F p x}

omit [TopologicalSpace P] in
/-- Compact, nonempty feasible sets give nonempty maximizing sets. -/
theorem parametricMaxima_nonempty {A : P → Set X} {F : P → X → ℝ} {p : P}
    (hA : IsCompact (A p)) (hne : (A p).Nonempty) (hF : Continuous (F p)) :
    (ParametricMaxima A F p).Nonempty := by
  obtain ⟨x, hx, hm⟩ := hA.exists_isMaxOn hne hF.continuousOn
  exact ⟨x, hx, hm⟩

/-- The closed-graph step of Berge's theorem, using the book's sequential conventions. -/
theorem parametricMaxima_sequentialUpper {A : P → Set X} {F : P → X → ℝ}
    (hA : SequentialUpper A) (hL : SequentialLower A)
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    SequentialUpper (ParametricMaxima A F) := by
  intro p x p₀ x₀ hp hx hm
  refine ⟨hA p x p₀ x₀ hp hx (fun n => (hm n).1), ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hL p p₀ hp y hy
  exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
    (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
    (hz.mono fun n hn => (hm n).2 (z n) hn)

/-- A compact local bound converts the book's upper condition to Mathlib hemicontinuity. -/
theorem sequentialUpper_upperHemicontinuousAt {A : P → Set X} {p₀ : P}
    [(𝓝 p₀).IsCountablyGenerated] (hA : SequentialUpper A)
    {K : Set X} (hK : IsSeqCompact K) (hb : ∀ᶠ p in 𝓝 p₀, A p ⊆ K) :
    UpperHemicontinuousAt A p₀ := by
  apply UpperHemicontinuousAt.of_sequences hK hb
  intro p hp x hx x₀ hlim
  exact hA p x p₀ x₀ hp hlim hx

/-- Continuous feasible selections through each point imply the book's lower condition. -/
theorem sequentialLower_of_continuous_selections {A : P → Set X}
    (h : ∀ p x, x ∈ A p → ∃ s : P → X,
      Continuous s ∧ s p = x ∧ ∀ q, s q ∈ A q) : SequentialLower A := by
  intro p p₀ hp x₀ hx₀
  obtain ⟨s, hs, hsp, hmem⟩ := h p₀ x₀ hx₀
  refine ⟨s ∘ p, Eventually.of_forall (fun n => hmem (p n)), ?_⟩
  simpa only [hsp] using hs.continuousAt.tendsto.comp hp

/-- A local compact container for all nearby feasible sets (Appendix 4). -/
def LocalCompactBound (A : P → Set X) : Prop :=
  ∀ p, ∃ K : Set X, IsCompact K ∧ ∀ᶠ q in 𝓝 p, A q ⊆ K

/-- The supremum value of a parameterized optimization problem. -/
noncomputable def ParametricValue (A : P → Set X) (F : P → X → ℝ) (p : P) : ℝ :=
  sSup (F p '' A p)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- An attained maximum evaluates the supremum without any choice of maximizer. -/
theorem parametricValue_eq_of_maximum {A : P → Set X} {F : P → X → ℝ} {p : P} {x : X}
    (hx : x ∈ ParametricMaxima A F p) : ParametricValue A F p = F p x := by
  apply csSup_eq_of_is_forall_le_of_forall_le_imp_ge
  · exact ⟨F p x, x, hx.1, rfl⟩
  · rintro v ⟨y, hy, rfl⟩
    exact hx.2 y hy
  · intro b hb
    exact hb _ ⟨x, hx.1, rfl⟩

/-- The maximum-value continuity step, with existence separated from the limit argument. -/
theorem parametricValue_continuous [SequentialSpace P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hupper : SequentialUpper (ParametricMaxima A F))
    (hne : ∀ p, (ParametricMaxima A F p).Nonempty)
    (hbound : LocalCompactBound (ParametricMaxima A F))
    (hF : Continuous (fun q : P × X => F q.1 q.2)) :
    Continuous (ParametricValue A F) := by
  classical
  choose s hs using hne
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hpn := hp.comp hns
  obtain ⟨K, hK, hb⟩ := hbound p₀
  have hev : ∀ᶠ n in atTop, s (p (ns n)) ∈ K := by
    filter_upwards [hpn hb] with n hn
    exact hn (hs _)
  obtain ⟨x, _, ms, hms, hlim⟩ := hK.tendsto_subseq' hev.frequently
  have hpm := hpn.comp hms.tendsto_atTop
  have hx : x ∈ ParametricMaxima A F p₀ :=
    hupper (fun n => p (ns (ms n))) (fun n => s (p (ns (ms n))))
      p₀ x hpm hlim (fun n => hs _)
  refine ⟨ms, ?_⟩
  have ht := hF.continuousAt.tendsto.comp (hpm.prodMk_nhds hlim)
  have heq : (fun n => ParametricValue A F (p (ns (ms n)))) =
      (fun n => F (p (ns (ms n))) (s (p (ns (ms n))))) := by
    funext n
    exact parametricValue_eq_of_maximum (hs _)
  change Tendsto (fun n => ParametricValue A F (p (ns (ms n)))) atTop
    (𝓝 (ParametricValue A F p₀))
  rw [heq, parametricValue_eq_of_maximum hx]
  exact ht

/-- Local compact containment passes to every pointwise smaller correspondence. -/
theorem LocalCompactBound.mono {A B : P → Set X} (h : LocalCompactBound B)
    (hab : ∀ p, A p ⊆ B p) : LocalCompactBound A := by
  intro p
  obtain ⟨K, hK, hb⟩ := h p
  exact ⟨K, hK, hb.mono (fun q hq => (hab q).trans hq)⟩

/-- Closed-graph fibers are closed in first-countable spaces. -/
theorem SequentialUpper.isClosed [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (p : P) : IsClosed (A p) := by
  apply isSeqClosed_iff_isClosed.mp
  intro x x₀ hx ht
  exact h (fun _ => p) x p x₀ tendsto_const_nhds ht hx

/-- The book's closed-graph condition and a local compact bound imply compact values. -/
theorem SequentialUpper.isCompact [FirstCountableTopology X] {A : P → Set X}
    (h : SequentialUpper A) (hb : LocalCompactBound A) (p : P) : IsCompact (A p) := by
  obtain ⟨K, hK, hlocal⟩ := hb p
  exact hK.of_isClosed_subset (h.isClosed p) hlocal.self_of_nhds

/-- Corollary A4.8's singleton step, without needing a utility function. -/
theorem continuous_of_singleton_correspondence [FirstCountableTopology P]
    [FirstCountableTopology X] {s : P → X}
    (hu : SequentialUpper (fun p => {s p}))
    (hb : LocalCompactBound (fun p => {s p})) : Continuous s := by
  apply upperHemicontinuous_singleton_iff.mp
  intro p
  obtain ⟨K, hK, hk⟩ := hb p
  exact sequentialUpper_upperHemicontinuousAt hu hK.isSeqCompact hk

/-- Equality of objective suprema expressed by equality of all real upper bounds.
This avoids assigning a real value to the supremum of an unbounded set. -/
def SameObjectiveUpperBounds (A B : P → Set X) (F : P → X → ℝ) : Prop :=
  ∀ p r, (∀ x ∈ A p, F p x ≤ r) ↔ (∀ x ∈ B p, F p x ≤ r)

/-- Berge's auxiliary-correspondence form: the feasible set itself need not be compact.
The nonempty auxiliary fibers make the convention used in the source proof explicit. -/
theorem maximum_theorem_auxiliary [FirstCountableTopology P] [FirstCountableTopology X]
    {A B : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper B) (hb : LocalCompactBound B)
    (hne : ∀ p, (B p).Nonempty) (hba : ∀ p, B p ⊆ A p)
    (hzb : ∀ p, ParametricMaxima A F p ⊆ B p)
    (hsup : SameObjectiveUpperBounds A B F) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) := by
  have hn (p) : (ParametricMaxima A F p).Nonempty := by
    have hc : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
    obtain ⟨x, hx, hmax⟩ := parametricMaxima_nonempty (hu.isCompact hb p) (hne p) hc
    exact ⟨x, hba p hx, (hsup p (F p x)).mpr hmax⟩
  have hz : SequentialUpper (ParametricMaxima A F) := by
    intro p x p₀ x₀ hp hx hm
    have hxB : x₀ ∈ B p₀ := hu p x p₀ x₀ hp hx (fun n => hzb _ (hm n))
    refine ⟨hba _ hxB, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hl p p₀ hp y hy
    exact le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hzy))
      (hF.continuousAt.tendsto.comp (hp.prodMk_nhds hx))
      (hz.mono fun n hn => (hm n).2 (z n) hn)
  have hbound := hb.mono hzb
  exact ⟨hn, hz, hbound, parametricValue_continuous hz hn hbound hF⟩

/-- The compact-feasible-set version used for consumer budgets, including zero income. -/
theorem maximum_theorem [FirstCountableTopology P] [FirstCountableTopology X]
    {A : P → Set X} {F : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hl : SequentialLower A) (hu : SequentialUpper A) (hb : LocalCompactBound A)
    (hne : ∀ p, (A p).Nonempty) :
    (∀ p, (ParametricMaxima A F p).Nonempty) ∧
      SequentialUpper (ParametricMaxima A F) ∧
      LocalCompactBound (ParametricMaxima A F) ∧ Continuous (ParametricValue A F) :=
  maximum_theorem_auxiliary hF hl hu hb hne (fun _ => Subset.rfl)
    (fun _ _ hx => hx.1) (fun _ _ => Iff.rfl)

omit [TopologicalSpace P] [TopologicalSpace X] in
/-- For nonempty objectives with finite upper bounds, the auxiliary theorem's upper-bound
formulation is exactly equality of the printed real suprema. -/
theorem sameObjectiveUpperBounds_iff_value_eq {A B : P → Set X} {F : P → X → ℝ}
    (ha : ∀ p, (A p).Nonempty) (hb : ∀ p, (B p).Nonempty)
    (hba : ∀ p, BddAbove (F p '' A p)) (hbb : ∀ p, BddAbove (F p '' B p)) :
    SameObjectiveUpperBounds A B F ↔ ∀ p, ParametricValue A F p = ParametricValue B F p := by
  have hA (p : P) (r : ℝ) : ParametricValue A F p ≤ r ↔ ∀ x ∈ A p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hba p) ((ha p).image (F p))]
    simp
  have hB (p : P) (r : ℝ) : ParametricValue B F p ≤ r ↔ ∀ x ∈ B p, F p x ≤ r := by
    rw [ParametricValue, csSup_le_iff (hbb p) ((hb p).image (F p))]
    simp
  constructor
  · intro h p
    apply le_antisymm
    · exact (hA p _).mpr ((h p _).mpr ((hB p _).mp le_rfl))
    · exact (hB p _).mpr ((h p _).mp ((hA p _).mp le_rfl))
  · intro h p r
    rw [← hA, ← hB, h p]

end Kreps.ConsumerDemand
