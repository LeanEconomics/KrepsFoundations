/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite minima for Afriat's utility construction

Kreps I, p. 73 and Problem 4.2, p. 78. A nonempty finite minimum preserves
continuity, strict increase and concavity. The domain and its order or vector
structure are arbitrary; the next module applies these facts to affine functions
on commodity space. Nonemptiness prevents an artificial value for an empty minimum.
-/

namespace Kreps.RevealedPreference

variable {I X : Type*} [Fintype I] [Nonempty I]

/-- The pointwise minimum over a nonempty finite family of real-valued functions. -/
noncomputable def FiniteMinimum (f : I → X → ℝ) (x : X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => f i x)

/-- The finite minimum is no greater than any member of the family. -/
theorem finiteMinimum_le (f : I → X → ℝ) (x : X) (i : I) :
    FiniteMinimum f x ≤ f i x :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- A common lower bound bounds the finite minimum from below. -/
theorem le_finiteMinimum (f : I → X → ℝ) (x : X) {a : ℝ}
    (ha : ∀ i, a ≤ f i x) : a ≤ FiniteMinimum f x :=
  Finset.le_inf' _ _ (fun i _ => ha i)

/-- At each point some family member attains the finite minimum. -/
theorem finiteMinimum_attained (f : I → X → ℝ) (x : X) :
    ∃ i, FiniteMinimum f x = f i x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => f i x)
  exact ⟨i, hi⟩

/-- **Problem 4.2:** a finite minimum of continuous functions is continuous. -/
theorem finiteMinimum_continuous [TopologicalSpace X] {f : I → X → ℝ}
    (hf : ∀ i, Continuous (f i)) : Continuous (FiniteMinimum f) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => hf i)

/-- **Problem 4.2:** a finite minimum of strictly increasing functions is strictly increasing. -/
theorem finiteMinimum_strictMono [Preorder X] {f : I → X → ℝ}
    (hf : ∀ i, StrictMono (f i)) : StrictMono (FiniteMinimum f) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := finiteMinimum_attained f y
  rw [hi]
  exact (finiteMinimum_le f x i).trans_lt (hf i hxy)

/-- **Problem 4.2:** a finite minimum of concave functions is concave on their common domain. -/
theorem finiteMinimum_concaveOn [AddCommMonoid X] [Module ℝ X] {S : Set X}
    {f : I → X → ℝ} (hf : ∀ i, ConcaveOn ℝ S (f i)) :
    ConcaveOn ℝ S (FiniteMinimum f) := by
  refine ⟨(hf (Classical.arbitrary I)).1, ?_⟩
  intro x hx y hy a b ha hb hab
  apply le_finiteMinimum
  intro i
  calc
    a • FiniteMinimum f x + b • FiniteMinimum f y
        ≤ a • f i x + b • f i y :=
      add_le_add (smul_le_smul_of_nonneg_left (finiteMinimum_le f x i) ha)
        (smul_le_smul_of_nonneg_left (finiteMinimum_le f y i) hb)
    _ ≤ f i (a • x + b • y) := (hf i).2 hx hy ha hb hab

end Kreps.RevealedPreference
