import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Basic.NNReal.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Preference prerequisites for finite demand data

Selected prerequisite definitions and proofs from `PreferenceProperties.Basic`,
`StrictPreference`, `Rationalization` and `CountableUtility`, originating at commit
`7d496c5`. The namespace and imports are local to this independent chapter.
Kreps I, pp. 3-11, supplies the rationality and numerical-representation conventions
used throughout Chapter 4, pp. 67-78.
-/

namespace Kreps.RevealedPreference

variable {X : Type*} {r : X → X → Prop}

/-- Every pair of alternatives can be compared. -/
def Complete (r : X → X → Prop) : Prop := ∀ x y, r x y ∨ r y x

/-- Weak preference is transitive. -/
def TransitivePref (r : X → X → Prop) : Prop :=
  ∀ x y z, r x y → r y z → r x z

/-- The standing complete-and-transitive preference assumption. -/
def Rational (r : X → X → Prop) : Prop := Complete r ∧ TransitivePref r

/-- Strict preference is weak preference without its converse. -/
def Strict (r : X → X → Prop) (x y : X) : Prop := r x y ∧ ¬r y x

/-- Indifference is weak preference in both directions. -/
def Indifferent (r : X → X → Prop) (x y : X) : Prop := r x y ∧ r y x

/-- All feasible alternatives weakly preferred to every member of the menu. -/
def PrefChoice (r : X → X → Prop) (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∀ y ∈ A, r x y}

/-- Numerical utility induces the book's orientation of weak preference. -/
def UtilityPref (u : X → ℝ) (x y : X) : Prop := u y ≤ u x

/-- A numerical utility represents all and only the weak comparisons. -/
def Represents (u : X → ℝ) (r : X → X → Prop) : Prop :=
  ∀ x y, r x y ↔ u y ≤ u x

/-- Completeness includes reflexivity. -/
theorem complete_refl (hc : Complete r) (x : X) : r x x := (hc x x).elim id id

/-- A strict comparison followed by a weak comparison remains strict. -/
theorem strict_weak_trans (ht : TransitivePref r) {x y z : X}
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨ht x y z hxy.1 hyz, fun hzx => hxy.2 (ht y z x hyz hzx)⟩

/-- A weak comparison followed by a strict comparison remains strict. -/
theorem weak_strict_trans (ht : TransitivePref r) {x y z : X}
    (hxy : r x y) (hyz : Strict r y z) : Strict r x z :=
  ⟨ht x y z hxy hyz.1, fun hzx => hyz.2 (ht z x y hzx hxy)⟩

/-- Numerical preference is always complete and transitive. -/
theorem utilityPref_rational (u : X → ℝ) : Rational (UtilityPref u) := by
  constructor
  · exact fun x y => le_total (u y) (u x)
  · exact fun _ _ _ hxy hyz => le_trans hyz hxy

/-- A represented preference is rational. -/
theorem represents_rational {u : X → ℝ} (hu : Represents u r) : Rational r := by
  constructor
  · intro x y
    exact (le_total (u y) (u x)).imp ((hu x y).mpr) ((hu y x).mpr)
  · intro x y z hxy hyz
    exact (hu x z).mpr (((hu y z).mp hyz).trans ((hu x y).mp hxy))

/-- Strict preference corresponds exactly to strict inequality of represented utilities. -/
theorem strict_iff_utility_lt {u : X → ℝ} (hu : Represents u r) (x y : X) :
    Strict r x y ↔ u y < u x := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hle => h.2 ((hu y x).mpr hle))
  · intro h
    exact ⟨(hu x y).mpr h.le, fun hyx => (not_le_of_gt h) ((hu y x).mp hyx)⟩

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Revealed comparison chains and GARP

Kreps I, Definition 4.2, p. 70. A cost matrix entry is expenditure on one observed
bundle at another observation's prices minus that observation's income. Weak
edges have nonpositive cost; strict edges have negative cost. A strict revealed
chain has at least one strict edge and any finite number of weak edges on either
side. The empty weak chain is harmless on feasible data, whose diagonal is already
a direct weak comparison. No budget-exhaustion condition is built into GARP.
-/

namespace Kreps.RevealedPreference

variable {I : Type*}

/-- Direct weak revealed preference in a cost-minus-income matrix. -/
def DirectWeak (C : I → I → ℝ) (i j : I) : Prop := C i j ≤ 0

/-- Direct strict revealed preference uses a strict budget slack. -/
def DirectStrict (C : I → I → ℝ) (i j : I) : Prop := C i j < 0

/-- A finite chain of weak direct comparisons, including the reflexive chain. -/
def RevealedWeak (C : I → I → ℝ) : I → I → Prop :=
  Relation.ReflTransGen (DirectWeak C)

/-- A weak chain with at least one direct strict step. -/
def RevealedStrict (C : I → I → ℝ) (i j : I) : Prop :=
  ∃ a b, RevealedWeak C i a ∧ DirectStrict C a b ∧ RevealedWeak C b j

/-- **Definition 4.2c:** no revealed strict cycle occurs. -/
def MatrixGARP (C : I → I → ℝ) : Prop := ∀ i, ¬RevealedStrict C i i

/-- A direct weak comparison is a one-step revealed weak chain. -/
theorem directWeak_revealedWeak {C : I → I → ℝ} {i j : I}
    (h : DirectWeak C i j) : RevealedWeak C i j := Relation.ReflTransGen.single h

/-- A direct strict comparison is a revealed strict chain with no intervening edges. -/
theorem directStrict_revealedStrict {C : I → I → ℝ} {i j : I}
    (h : DirectStrict C i j) : RevealedStrict C i j :=
  ⟨i, j, .refl, h, .refl⟩

/-- Every strict revealed chain is also a weak revealed chain. -/
theorem revealedStrict_weak {C : I → I → ℝ} {i j : I}
    (h : RevealedStrict C i j) : RevealedWeak C i j := by
  obtain ⟨a, b, hia, hab, hbj⟩ := h
  exact hia.trans ((directWeak_revealedWeak hab.le).trans hbj)

/-- Prefixing a weak chain preserves the strict edge later in the chain. -/
theorem revealedWeak_strict_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedWeak C i j) (hjl : RevealedStrict C j l) : RevealedStrict C i l := by
  obtain ⟨a, b, hja, hab, hbl⟩ := hjl
  exact ⟨a, b, hij.trans hja, hab, hbl⟩

/-- Appending a weak chain preserves an earlier strict edge. -/
theorem revealedStrict_weak_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedStrict C i j) (hjl : RevealedWeak C j l) : RevealedStrict C i l := by
  obtain ⟨a, b, hia, hab, hbj⟩ := hij
  exact ⟨a, b, hia, hab, hbj.trans hjl⟩

/-- Two strict revealed chains concatenate to a strict chain. -/
theorem revealedStrict_trans {C : I → I → ℝ} {i j l : I}
    (hij : RevealedStrict C i j) (hjl : RevealedStrict C j l) : RevealedStrict C i l :=
  revealedStrict_weak_trans hij (revealedStrict_weak hjl)

/-- GARP forbids a weak chain returning against a strict revealed chain. -/
theorem matrixGARP_no_reverse {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedWeak C i j) : ¬RevealedStrict C j i :=
  fun hji => hG i (revealedWeak_strict_trans hij hji)

/-- The usual GARP criterion compares a weak chain with the cost of its closing edge. -/
theorem matrixGARP_iff_return_cost (C : I → I → ℝ) :
    MatrixGARP C ↔ ∀ i j, RevealedWeak C i j → 0 ≤ C j i := by
  constructor
  · intro hG i j hij
    exact le_of_not_gt (fun hji => matrixGARP_no_reverse hG hij
      (directStrict_revealedStrict hji))
  · intro h i hi
    obtain ⟨a, b, hia, hab, hbi⟩ := hi
    exact (not_lt_of_ge (h b a (hbi.trans hia))) hab

/-- GARP and feasibility force budget exhaustion, rather than assuming it. -/
theorem matrixGARP_diagonal_zero {C : I → I → ℝ} (hG : MatrixGARP C)
    (hf : ∀ i, C i i ≤ 0) (i : I) : C i i = 0 := by
  exact le_antisymm (hf i) ((matrixGARP_iff_return_cost C).mp hG i i .refl)

/-- A choice with positive budget slack violates GARP by a one-edge self-cycle. -/
theorem negative_diagonal_not_matrixGARP {C : I → I → ℝ} {i : I} (hi : C i i < 0) :
    ¬MatrixGARP C := fun hG => hG i (directStrict_revealedStrict hi)

/-- A numeric certificate increasing weakly along revealed comparisons excludes all cycles. -/
theorem matrixGARP_of_scores {C : I → I → ℝ} (v : I → ℝ)
    (hw : ∀ i j, DirectWeak C i j → v j ≤ v i)
    (hs : ∀ i j, DirectStrict C i j → v j < v i) : MatrixGARP C := by
  have hchain {i j : I} (h : RevealedWeak C i j) : v j ≤ v i := by
    induction h with
    | refl => exact le_rfl
    | @tail j l _ hjl ih => exact (hw j l hjl).trans ih
  intro i hi
  obtain ⟨a, b, hia, hab, hbi⟩ := hi
  have hlt : v i < v i := (hchain hbi).trans_lt ((hs a b hab).trans_le (hchain hia))
  exact lt_irrefl _ hlt

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The finite rank used in Varian's proof

Kreps I, Lemma 4.4, p. 72. The rank counts observations strictly below an
observation by a revealed chain. Weak revealed comparisons include all successors
of the lower observation; strict comparisons include at least one more. A
minimum-rank observation therefore has no strict successors.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} [Fintype I]

/-- The indices of observations strictly revealed below a given observation. -/
noncomputable def StrictSuccessors (C : I → I → ℝ) (i : I) : Finset I := by
  classical
  exact Finset.univ.filter (RevealedStrict C i)

/-- The cardinal rank `n(i)` from Lemma 4.4. -/
noncomputable def RevealedRank (C : I → I → ℝ) (i : I) : ℕ :=
  (StrictSuccessors C i).card

/-- Membership in the finite successor set is exactly strict revealed preference. -/
theorem mem_strictSuccessors {C : I → I → ℝ} {i j : I} :
    j ∈ StrictSuccessors C i ↔ RevealedStrict C i j := by
  classical
  simp [StrictSuccessors]

/-- A weak chain preserves the inclusion of strict successor sets. -/
theorem strictSuccessors_subset {C : I → I → ℝ} {i j : I}
    (hij : RevealedWeak C i j) : StrictSuccessors C j ⊆ StrictSuccessors C i := by
  intro l hl
  exact mem_strictSuccessors.mpr (revealedWeak_strict_trans hij (mem_strictSuccessors.mp hl))

/-- A weak revealed comparison can only decrease the finite rank. -/
theorem revealedRank_le {C : I → I → ℝ} {i j : I} (hij : RevealedWeak C i j) :
    RevealedRank C j ≤ RevealedRank C i :=
  Finset.card_le_card (strictSuccessors_subset hij)

/-- A strict revealed comparison strictly decreases rank when GARP holds. -/
theorem revealedRank_lt {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedStrict C i j) : RevealedRank C j < RevealedRank C i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨strictSuccessors_subset (revealedStrict_weak hij), ?_⟩
  intro he
  have hj : j ∈ StrictSuccessors C i := mem_strictSuccessors.mpr hij
  rw [← he] at hj
  exact hG j (mem_strictSuccessors.mp hj)

/-- **Lemma 4.4a:** a higher-rank observation is strictly unaffordable at a lower rank. -/
theorem lemma_4_4a {C : I → I → ℝ} {i j : I}
    (hij : RevealedRank C i < RevealedRank C j) : 0 < C i j := by
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt hij) (revealedRank_le (directWeak_revealedWeak h))

/-- **Lemma 4.4b:** equal-rank observations cannot be strictly affordable under GARP. -/
theorem lemma_4_4b {C : I → I → ℝ} (hG : MatrixGARP C) {i j : I}
    (hij : RevealedRank C i = RevealedRank C j) : 0 ≤ C i j := by
  apply le_of_not_gt
  intro h
  have hr := revealedRank_lt hG (directStrict_revealedStrict h)
  rw [hij] at hr
  exact lt_irrefl _ hr

/-- **Lemma 4.4c:** a nonempty finite dataset satisfying GARP has a rank-zero observation. -/
theorem lemma_4_4c [Nonempty I] {C : I → I → ℝ} (hG : MatrixGARP C) :
    ∃ i, RevealedRank C i = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image (RevealedRank C) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  by_contra hn
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  have hji := revealedRank_lt hG (mem_strictSuccessors.mp hj)
  exact (not_le_of_gt hji) (hi j (Finset.mem_univ j))

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Varian's rank-class induction for the Afriat inequalities

Kreps I, Lemma 4.5, pp. 72-73, and Problem 4.2, p. 78. Remove the lowest
rank class, retain the inductively constructed coefficients on its complement,
and assign the removed class the minimum of the finitely many cross-class affine
values. Strictly positive cross-class costs permit positive new multipliers.
The all-minimal case is treated separately, including empty datasets.
-/

namespace Kreps.RevealedPreference

variable {I : Type*}

/-- A finite collection of inequalities with positive slopes has a positive common bound. -/
theorem exists_positive_finite_multiplier (s : Finset I) (a b : I → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ l : ℝ, 0 < l ∧ ∀ i ∈ s, b i ≤ l * a i := by
  classical
  by_cases hn : s.Nonempty
  · obtain ⟨m, _, hm⟩ := s.exists_max_image (fun i => b i / a i) hn
    refine ⟨max 1 (b m / a m), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi
    exact (div_le_iff₀ (ha i hi)).mp ((hm i hi).trans (le_max_right _ _))
  · exact ⟨1, zero_lt_one, fun i hi => (hn ⟨i, hi⟩).elim⟩

/-- **Problem 4.2, all-minimal case:** nonnegative costs admit zero values and unit weights. -/
theorem afriat_all_minimal (C : I → I → ℝ) (s : Finset I)
    (hC : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ C j i) :
    ∃ v l : I → ℝ, (∀ i ∈ s, 0 < l i) ∧
      ∀ i ∈ s, ∀ j ∈ s, v i ≤ v j + l j * C j i := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ _ => zero_lt_one, ?_⟩
  simpa using hC

/-- The finite rank-class construction solves the inequalities on every finite subdataset. -/
theorem afriat_of_rank_on_finset (C : I → I → ℝ) (rank : I → ℕ)
    (hstrict : ∀ i j, rank i < rank j → 0 < C i j)
    (hequal : ∀ i j, rank i = rank j → 0 ≤ C i j) (s : Finset I) :
    ∃ v l : I → ℝ, (∀ i ∈ s, 0 < l i) ∧
      ∀ i ∈ s, ∀ j ∈ s, v i ≤ v j + l j * C j i := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hn : s.Nonempty
  · obtain ⟨m, hm, hmin⟩ := s.exists_min_image rank hn
    let H := s.filter (fun i => rank m < rank i)
    have hHs : H ⊆ s := Finset.filter_subset _ _
    have hmH : m ∉ H := by simp [H]
    have hsmall : H ⊂ s := by
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨hHs, fun he => hmH (he.symm ▸ hm)⟩
    have hbase (i : I) (hi : i ∈ s) (hiH : i ∉ H) : rank i = rank m := by
      have hnot : ¬rank m < rank i := fun hh => hiH (Finset.mem_filter.mpr ⟨hi, hh⟩)
      exact le_antisymm (le_of_not_gt hnot) (hmin i hi)
    by_cases hH : H.Nonempty
    · obtain ⟨v, l, hl, hv⟩ := ih H hsmall
      let Z := s \ H
      have hZ : Z.Nonempty := ⟨m, Finset.mem_sdiff.mpr ⟨hm, hmH⟩⟩
      obtain ⟨p, _, hp⟩ := (Z.product H).exists_min_image
        (fun q : I × I => v q.2 + l q.2 * C q.2 q.1) (hZ.product hH)
      let v0 := v p.2 + l p.2 * C p.2 p.1
      have hfloor (i : I) (hi : i ∈ Z) (j : I) (hj : j ∈ H) :
          v0 ≤ v j + l j * C j i := hp (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
      have hnew : ∀ j, ∃ t : ℝ, 0 < t ∧
          (j ∈ Z → ∀ i ∈ H, v i - v0 ≤ t * C j i) := by
        intro j
        by_cases hj : j ∈ Z
        · obtain ⟨t, ht, hti⟩ := exists_positive_finite_multiplier H (C j)
            (fun i => v i - v0) (by
              intro i hi
              apply hstrict
              rw [hbase j (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2]
              exact (Finset.mem_filter.mp hi).2)
          exact ⟨t, ht, fun _ => hti⟩
        · exact ⟨1, zero_lt_one, fun h => (hj h).elim⟩
      choose t ht hti using hnew
      refine ⟨fun i => if i ∈ H then v i else v0,
        fun i => if i ∈ H then l i else t i, ?_, ?_⟩
      · intro i hi
        change 0 < if i ∈ H then l i else t i
        split_ifs with hiH
        · exact hl i hiH
        · exact ht i
      · intro i hi j hj
        by_cases hiH : i ∈ H <;> by_cases hjH : j ∈ H
        · simpa only [ite_eq_left hiH, ite_eq_left hjH] using hv i hiH j hjH
        · simp only [ite_eq_left hiH, ite_eq_right hjH]
          have hh := hti j (Finset.mem_sdiff.mpr ⟨hj, hjH⟩) i hiH
          linarith
        · simpa only [ite_eq_right hiH, ite_eq_left hjH] using
            hfloor i (Finset.mem_sdiff.mpr ⟨hi, hiH⟩) j hjH
        · simp only [ite_eq_right hiH, ite_eq_right hjH, le_add_iff_nonneg_right]
          exact mul_nonneg (ht j).le
            (hequal j i ((hbase j hj hjH).trans (hbase i hi hiH).symm))
    · apply afriat_all_minimal C s
      intro i hi j hj
      exact hequal j i ((hbase j hj (fun h => hH ⟨j, h⟩)).trans
        (hbase i hi (fun h => hH ⟨i, h⟩)).symm)
  · exact afriat_all_minimal C s (fun i hi => (hn ⟨i, hi⟩).elim)

/-- **Lemma 4.5:** GARP yields positive Afriat multipliers on arbitrary finite data. -/
theorem lemma_4_5 [Finite I] {C : I → I → ℝ} (hG : MatrixGARP C) :
    ∃ v l : I → ℝ, (∀ i, 0 < l i) ∧ ∀ i j, v i ≤ v j + l j * C j i := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨v, l, hl, hv⟩ := afriat_of_rank_on_finset C (RevealedRank C)
    (fun _ _ => lemma_4_4a) (fun _ _ => lemma_4_4b hG) Finset.univ
  exact ⟨v, l, fun i => hl i (Finset.mem_univ i),
    fun i j => hv i (Finset.mem_univ i) j (Finset.mem_univ j)⟩

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The finite affine envelope in Afriat's theorem

Kreps I, equation (4.1) and the proof of Proposition 4.3, pp. 72-73. Given the
numbers produced by Lemma 4.5, take the minimum of their supporting affine terms.
The construction is defined on the entire commodity vector space, so its
restriction covers every nonnegative bundle, including boundary bundles.

The results here are independent of the finite observation data structure. The
Afriat inequalities are intermediate inputs; the chapter's main theorem must
construct them from GARP before applying these envelope results.
-/

namespace Kreps.RevealedPreference

open scoped BigOperators

variable {I : Type*} {k : ℕ}

/-- Expenditure as used in each affine supporting function. -/
def AffineExpenditure (p x : Fin k → ℝ) : ℝ := ∑ j, p j * x j

/-- Expenditure is continuous on the full commodity vector space. -/
theorem affineExpenditure_continuous (p : Fin k → ℝ) :
    Continuous (AffineExpenditure p) := by
  unfold AffineExpenditure
  fun_prop

/-- Strictly positive prices make expenditure strictly increasing in the product order. -/
theorem affineExpenditure_strictMono {p : Fin k → ℝ} (hp : ∀ j, 0 < p j) :
    StrictMono (AffineExpenditure p) := by
  intro x y hxy
  obtain ⟨hle, j, hj⟩ := Pi.lt_def.mp hxy
  exact Finset.sum_lt_sum
    (fun l _ => mul_le_mul_of_nonneg_left (hle l) (hp l).le)
    ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hp j)⟩

/-- Expenditure preserves arbitrary real linear combinations. -/
theorem affineExpenditure_mix (p x y : Fin k → ℝ) (c d : ℝ) :
    AffineExpenditure p (c • x + d • y) =
      c * AffineExpenditure p x + d * AffineExpenditure p y := by
  simp only [AffineExpenditure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- The supporting affine term based at observation `i`, with its value and multiplier. -/
def FiniteAffineTerm (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I)
    (x : Fin k → ℝ) : ℝ :=
  v i + lam i * (AffineExpenditure (p i) x - AffineExpenditure (p i) (a i))

/-- Each affine term is continuous, with no sign assumptions on its coefficients. -/
theorem finiteAffineTerm_continuous (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I) :
    Continuous (FiniteAffineTerm p a v lam i) :=
  continuous_const.add
    (continuous_const.mul ((affineExpenditure_continuous (p i)).sub continuous_const))

/-- Positive multipliers and prices make each supporting term strictly increasing. -/
theorem finiteAffineTerm_strictMono {p a : I → Fin k → ℝ} {v lam : I → ℝ} (i : I)
    (hlam : 0 < lam i) (hp : ∀ j, 0 < p i j) : StrictMono (FiniteAffineTerm p a v lam i) := by
  intro x y hxy
  simpa only [FiniteAffineTerm, add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left (sub_lt_sub_right (affineExpenditure_strictMono hp hxy)
      (AffineExpenditure (p i) (a i))) hlam) (v i)

/-- A supporting affine term preserves combinations whose coefficients sum to one. -/
theorem finiteAffineTerm_mix (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I)
    (x y : Fin k → ℝ) {c d : ℝ} (hcd : c + d = 1) :
    FiniteAffineTerm p a v lam i (c • x + d • y) =
      c * FiniteAffineTerm p a v lam i x + d * FiniteAffineTerm p a v lam i y := by
  unfold FiniteAffineTerm
  rw [affineExpenditure_mix]
  linear_combination -(v i - lam i * AffineExpenditure (p i) (a i)) * hcd

/-- Each supporting term is concave on the entire vector space. -/
theorem finiteAffineTerm_concaveOn (p a : I → Fin k → ℝ) (v lam : I → ℝ) (i : I) :
    ConcaveOn ℝ Set.univ (FiniteAffineTerm p a v lam i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d _ _ hcd
  simpa only [smul_eq_mul] using (finiteAffineTerm_mix p a v lam i x y hcd).symm.le

variable [Fintype I] [Nonempty I]

/-- The full-domain utility constructed after the Afriat inequalities have been obtained. -/
noncomputable def FiniteAffineEnvelope (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    (Fin k → ℝ) → ℝ := FiniteMinimum (FiniteAffineTerm p a v lam)

/-- The envelope is bounded above by each of its supporting terms. -/
theorem finiteAffineEnvelope_le_term (p a : I → Fin k → ℝ) (v lam : I → ℝ)
    (x : Fin k → ℝ) (i : I) :
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineTerm p a v lam i x :=
  finiteMinimum_le _ x i

/-- Afriat's finite affine envelope is continuous on the full vector space. -/
theorem finiteAffineEnvelope_continuous (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    Continuous (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_continuous (finiteAffineTerm_continuous p a v lam)

/-- Afriat's envelope is concave on the full vector space, hence on the nonnegative orthant. -/
theorem finiteAffineEnvelope_concaveOn (p a : I → Fin k → ℝ) (v lam : I → ℝ) :
    ConcaveOn ℝ Set.univ (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_concaveOn (finiteAffineTerm_concaveOn p a v lam)

/-- Positive Afriat multipliers and prices make the envelope strictly increasing. -/
theorem finiteAffineEnvelope_strictMono {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hp : ∀ i j, 0 < p i j) :
    StrictMono (FiniteAffineEnvelope p a v lam) :=
  finiteMinimum_strictMono (fun i => finiteAffineTerm_strictMono i (hlam i) (hp i))

/-- Equation (4.1) makes the envelope interpolate the prescribed utility of every observation. -/
theorem finiteAffineEnvelope_at_anchor {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hineq : ∀ i j, v i ≤ v j + lam j *
      (AffineExpenditure (p j) (a i) - AffineExpenditure (p j) (a j))) (i : I) :
    FiniteAffineEnvelope p a v lam (a i) = v i := by
  apply le_antisymm
  · calc
      FiniteAffineEnvelope p a v lam (a i) ≤ FiniteAffineTerm p a v lam i (a i) :=
        finiteAffineEnvelope_le_term p a v lam (a i) i
      _ = v i := by simp [FiniteAffineTerm]
  · exact le_finiteMinimum _ _ (hineq i)

/-- Affordability at an observation bounds the envelope by that observation's assigned value. -/
theorem finiteAffineEnvelope_le_value {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (i : I) (hlam : 0 ≤ lam i) {x : Fin k → ℝ}
    (hx : AffineExpenditure (p i) x ≤ AffineExpenditure (p i) (a i)) :
    FiniteAffineEnvelope p a v lam x ≤ v i := by
  calc
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineTerm p a v lam i x :=
      finiteAffineEnvelope_le_term p a v lam x i
    _ ≤ v i := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hx))

/-- Each observed bundle maximizes the constructed envelope over its entire budget half-space. -/
theorem finiteAffineEnvelope_maximizes {p a : I → Fin k → ℝ} {v lam : I → ℝ}
    (hineq : ∀ i j, v i ≤ v j + lam j *
      (AffineExpenditure (p j) (a i) - AffineExpenditure (p j) (a j)))
    (i : I) (hlam : 0 ≤ lam i) {x : Fin k → ℝ}
    (hx : AffineExpenditure (p i) x ≤ AffineExpenditure (p i) (a i)) :
    FiniteAffineEnvelope p a v lam x ≤ FiniteAffineEnvelope p a v lam (a i) := by
  rw [finiteAffineEnvelope_at_anchor hineq i]
  exact finiteAffineEnvelope_le_value i hlam hx

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Structural preference properties used by Afriat's theorem

Selected local prerequisite copies from Chapter 2's `OrthantRepresentation`,
`Monotonicity`, `ContinuousPreference` and `ConvexPreference`, commit `7d496c5`.
Definitions preserve the nonnegative orthant, the closed-radius local-insatiability
condition and the distinction between strict coordinate increase and strict
preference. The final concavity bridge specializes standard Jensen inequalities.
-/

namespace Kreps.RevealedPreference

variable {X : Type*} {r : X → X → Prop}

/-- The nonnegative commodity orthant, including boundary bundles. -/
abbrev NonnegativeOrthant (k : ℕ) := {x : Fin k → ℝ // 0 ≤ x}

/-- A distinct weakly larger bundle is strictly preferred. -/
def StrictlyMonotonePreference [PartialOrder X] (r : X → X → Prop) : Prop :=
  ∀ x y, y ≤ x → x ≠ y → Strict r x y

/-- A strict improvement exists within every positive distance. -/
def LocallyInsatiable [PseudoMetricSpace X] (r : X → X → Prop) : Prop :=
  ∀ x, ∀ ε > 0, ∃ y, dist y x ≤ ε ∧ Strict r y x

/-- Continuity of preference is openness of its strict-comparison graph. -/
def ContinuousPreference [TopologicalSpace X] (r : X → X → Prop) : Prop :=
  IsOpen {p : X × X | Strict r p.1 p.2}

/-- A convex combination belongs to the same convex consumption domain. -/
def Mix {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (x y : S) (a : ℝ) (ha : a ∈ Set.Icc 0 1) : S :=
  ⟨a • x.val + (1 - a) • y.val,
    hS x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)⟩

/-- A mixture is weakly preferred to the worse endpoint. -/
def ConvexPreference {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, r x y → ∀ a, ∀ ha : a ∈ Set.Icc 0 1, r (Mix hS x y a ha) y

/-- Continuous utility gives continuous preference. -/
theorem continuousPreference_of_continuous_utility [TopologicalSpace X]
    {u : X → ℝ} (hu : Continuous u) : ContinuousPreference (UtilityPref u) := by
  have heq : {p : X × X | Strict (UtilityPref u) p.1 p.2} =
      {p : X × X | u p.2 < u p.1} := by
    ext p
    exact lt_iff_le_not_ge.symm
  change IsOpen {p : X × X | Strict (UtilityPref u) p.1 p.2}
  rw [heq]
  exact isOpen_lt (hu.comp continuous_snd) (hu.comp continuous_fst)

/-- A strictly increasing numerical utility gives strictly monotone preference. -/
theorem strictlyMonotonePreference_of_strictMono [PartialOrder X] {u : X → ℝ}
    (hu : StrictMono u) : StrictlyMonotonePreference (UtilityPref u) := by
  intro x y hyx hne
  have h := hu (lt_of_le_of_ne hyx hne.symm)
  exact ⟨h.le, not_le_of_gt h⟩

/-- The closed-radius formulation is equivalent to an open-ball improvement. -/
theorem locallyInsatiable_iff_open [PseudoMetricSpace X] :
    LocallyInsatiable r ↔ ∀ x, ∀ ε > 0, ∃ y, dist y x < ε ∧ Strict r y x := by
  constructor
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x (ε / 2) (by positivity)
    exact ⟨y, lt_of_le_of_lt hy (by linarith), hr⟩
  · intro h x ε hε
    obtain ⟨y, hy, hr⟩ := h x ε hε
    exact ⟨y, hy.le, hr⟩

/-- Raise every coordinate by the same nonnegative amount. -/
def RaisedBundle {k : ℕ} (x : NonnegativeOrthant k) (δ : ℝ) (hδ : 0 ≤ δ) :
    NonnegativeOrthant k := ⟨fun j => x.val j + δ, fun j => add_nonneg (x.property j) hδ⟩

/-- The finite-product distance is bounded by the common coordinate increase. -/
theorem raisedBundle_dist_le {k : ℕ} (x : NonnegativeOrthant k) {δ : ℝ} (hδ : 0 ≤ δ) :
    dist (RaisedBundle x δ hδ) x ≤ δ := by
  change dist (fun j => x.val j + δ) x.val ≤ δ
  apply (dist_pi_le_iff hδ).mpr
  intro j
  simp [abs_of_nonneg hδ]

/-- Strict monotonicity gives local insatiability in a positive number of commodities. -/
theorem strictlyMonotone_locallyInsatiable {k : ℕ} (hk : 0 < k)
    {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}
    (hm : StrictlyMonotonePreference r) : LocallyInsatiable r := by
  intro x ε hε
  refine ⟨RaisedBundle x ε hε.le, raisedBundle_dist_le x hε.le, hm _ x ?_ ?_⟩
  · intro j
    exact le_add_of_nonneg_right hε.le
  · intro he
    have hj := congrArg (fun z : NonnegativeOrthant k => z.val ⟨0, hk⟩) he
    change x.val ⟨0, hk⟩ + ε = x.val ⟨0, hk⟩ at hj
    linarith

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Finite market observations and rationalization

Kreps I, pp. 67-70. Observed bundles are nonnegative, prices are strictly positive,
incomes are nonnegative, and observations are feasible. Budget exhaustion is a
conclusion of GARP or locally insatiable maximization, never an input to the data.
The index type need not be finite until the sufficiency proof invokes it.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- Expenditure at a price vector, on any real commodity vector. -/
def Expenditure (p x : Fin k → ℝ) : ℝ := ∑ j, p j * x j

/-- The full nonnegative budget set includes its boundary and all unobserved bundles. -/
def Budget (p : Fin k → ℝ) (y : ℝ) : Set (NonnegativeOrthant k) :=
  {x | Expenditure p x.val ≤ y}

/-- Primitive market observations; feasibility does not presume budget exhaustion. -/
structure MarketData (I : Type*) (k : ℕ) where
  price : I → Fin k → ℝ
  income : I → ℝ
  bundle : I → NonnegativeOrthant k
  price_pos : ∀ i j, 0 < price i j
  income_nonneg : ∀ i, 0 ≤ income i
  feasible : ∀ i, Expenditure (price i) (bundle i).val ≤ income i

/-- The matrix records cross-expenditure minus the original observation's income. -/
def MarketData.cost (D : MarketData I k) (i j : I) : ℝ :=
  Expenditure (D.price i) (D.bundle j).val - D.income i

/-- **Definition 4.2:** the original-income data have no revealed strict cycle. -/
def GARP (D : MarketData I k) : Prop := MatrixGARP D.cost

/-- A preference rationalizes each choice on its entire observed budget set. -/
def Rationalizes (D : MarketData I k)
    (r : NonnegativeOrthant k → NonnegativeOrthant k → Prop) : Prop :=
  ∀ i, D.bundle i ∈ PrefChoice r (Budget (D.price i) (D.income i))

/-- Expenditure is continuous on real commodity space. -/
theorem expenditure_continuous (p : Fin k → ℝ) : Continuous (Expenditure p) := by
  unfold Expenditure
  fun_prop

/-- Expenditure remains continuous when restricted to nonnegative bundles. -/
theorem expenditure_orthant_continuous (p : Fin k → ℝ) :
    Continuous (fun x : NonnegativeOrthant k => Expenditure p x.val) :=
  (expenditure_continuous p).comp continuous_subtype_val

/-- The strict interior of a budget is an open set in the consumption domain. -/
theorem strictBudget_isOpen (p : Fin k → ℝ) (y : ℝ) :
    IsOpen {x : NonnegativeOrthant k | Expenditure p x.val < y} :=
  isOpen_lt (expenditure_orthant_continuous p) continuous_const

/-- Feasibility makes every diagonal entry nonpositive. -/
theorem MarketData.cost_self_nonpos (D : MarketData I k) (i : I) : D.cost i i ≤ 0 :=
  sub_nonpos.mpr (D.feasible i)

/-- GARP forces every observation to exhaust its original income. -/
theorem garp_budget_exhaustion {D : MarketData I k} (hG : GARP D) (i : I) :
    Expenditure (D.price i) (D.bundle i).val = D.income i :=
  sub_eq_zero.mp (matrixGARP_diagonal_zero hG D.cost_self_nonpos i)

/-- With exhausted budgets, costs are the expenditure differences in the Afriat formula. -/
theorem garp_cost_eq_difference {D : MarketData I k} (hG : GARP D) (i j : I) :
    D.cost i j = Expenditure (D.price i) (D.bundle j).val -
      Expenditure (D.price i) (D.bundle i).val := by
  rw [garp_budget_exhaustion hG]
  rfl

/-- Without local insatiability, complete indifference rationalizes every feasible dataset. -/
theorem constant_utility_rationalizes (D : MarketData I k) :
    Rationalizes D (UtilityPref (fun _ => 0)) := by
  intro i
  exact ⟨D.feasible i, fun _ _ => le_rfl⟩

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Local insatiability implies GARP

Kreps I, Lemma 4.1, p. 68, and the necessity direction of Proposition 4.3,
pp. 70-71. Local improvements inside a strict budget establish strict preference
over every strictly cheaper alternative. Rationality propagates these comparisons
along all finite revealed chains. No numerical representation is assumed.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- **Lemma 4.1:** an optimal bundle strictly dominates every strictly affordable bundle. -/
theorem lemma_4_1 (hr : Rational r) (hl : LocallyInsatiable r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : Expenditure p z.val < y) : Strict r x z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (strictBudget_isOpen p y) z hz
  obtain ⟨w, hw, hwp⟩ := locallyInsatiable_iff_open.mp hl z ε hε
  have hwstrict : Expenditure p w.val < y := hball (Metric.mem_ball.mpr hw)
  have hwb : w ∈ Budget p y := hwstrict.le
  exact weak_strict_trans hr.2 (hx.2 w hwb) hwp

/-- A locally insatiable maximum exhausts its budget. -/
theorem optimal_budget_exhaustion (hr : Rational r) (hl : LocallyInsatiable r)
    {p : Fin k → ℝ} {y : ℝ} {x : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) : Expenditure p x.val = y := by
  apply le_antisymm hx.1
  apply le_of_not_gt
  intro hs
  have h := lemma_4_1 hr hl hx hs
  exact h.2 h.1

/-- Rationalization transports every weak revealed chain to a weak preference comparison. -/
theorem rationalizes_revealedWeak {D : MarketData I k} (hr : Rational r)
    (hR : Rationalizes D r) {i j : I} (hij : RevealedWeak D.cost i j) :
    r (D.bundle i) (D.bundle j) := by
  induction hij with
  | refl => exact complete_refl hr.1 _
  | @tail j l _ hjl ih =>
    exact hr.2 _ _ _ ih ((hR j).2 _ (sub_nonpos.mp hjl))

/-- A strict edge in a revealed chain yields strict preference under local insatiability. -/
theorem rationalizes_revealedStrict {D : MarketData I k} (hr : Rational r)
    (hl : LocallyInsatiable r) (hR : Rationalizes D r) {i j : I}
    (hij : RevealedStrict D.cost i j) : Strict r (D.bundle i) (D.bundle j) := by
  obtain ⟨a, b, hia, hab, hbj⟩ := hij
  exact strict_weak_trans hr.2
    (weak_strict_trans hr.2 (rationalizes_revealedWeak hr hR hia)
      (lemma_4_1 hr hl (hR a) (sub_lt_zero.mp hab)))
    (rationalizes_revealedWeak hr hR hbj)

/-- **Proposition 4.3, necessity:** rational, locally insatiable rationalization implies GARP. -/
theorem rationalizes_garp {D : MarketData I k} (hr : Rational r)
    (hl : LocallyInsatiable r) (hR : Rationalizes D r) : GARP D := by
  intro i hi
  have h := rationalizes_revealedStrict hr hl hR hi
  exact h.2 h.1

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Afriat's theorem on the full consumption domain

Kreps I, Proposition 4.3, pp. 70-73. Primitive feasible market data satisfy GARP
exactly when rational, locally insatiable preferences rationalize them. The
sufficiency construction supplies a continuous, strictly increasing, concave
utility on all real commodity vectors, then restricts it to the entire nonnegative
orthant. Empty observation families are included. The preference equivalence
requires a positive number of commodities, as local insatiability is impossible
on the singleton zero-dimensional orthant.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- Positive multipliers in the Afriat inequalities rule out every revealed strict cycle. -/
theorem matrixGARP_of_afriat {C : I → I → ℝ} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hineq : ∀ i j, v i ≤ v j + lam j * C j i) :
    MatrixGARP C := by
  apply matrixGARP_of_scores v
  · intro i j hij
    exact (hineq j i).trans (add_le_of_nonpos_right
      (mul_nonpos_of_nonneg_of_nonpos (hlam i).le hij))
  · intro i j hij
    exact (hineq j i).trans_lt (add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (hlam i) hij))

/-- GARP is equivalent to solvability of the finite Afriat inequalities. -/
theorem matrixGARP_iff_afriat [Finite I] (C : I → I → ℝ) :
    MatrixGARP C ↔ ∃ v lam : I → ℝ, (∀ i, 0 < lam i) ∧
      ∀ i j, v i ≤ v j + lam j * C j i :=
  ⟨lemma_4_5, fun ⟨_, _, hl, hv⟩ => matrixGARP_of_afriat hl hv⟩

/-- Concavity of a full-domain utility gives convex preference on the nonnegative orthant. -/
theorem convexPreference_of_concaveOn {u : (Fin k → ℝ) → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) :
    ConvexPreference (convex_Ici (0 : Fin k → ℝ))
      (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) := by
  intro x y hxy a ha
  have h := hu.2 (Set.mem_univ x.val) (Set.mem_univ y.val)
    ha.1 (sub_nonneg.mpr ha.2) (by ring : a + (1 - a) = 1)
  change u y.val ≤ u x.val at hxy
  change u y.val ≤ u (a • x.val + (1 - a) • y.val)
  simp only [smul_eq_mul] at h
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hxy)]

/-- The constructive direction supplies a regular utility over the entire commodity space. -/
theorem garp_exists_concave_utility [Finite I] {D : MarketData I k} (hG : GARP D) :
    ∃ u : (Fin k → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧
      ConcaveOn ℝ Set.univ u ∧
      Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) := by
  classical
  let := Fintype.ofFinite I
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let u := FiniteAffineTerm (fun _ : Unit => fun _ : Fin k => (1 : ℝ))
      (fun _ : Unit => (0 : Fin k → ℝ)) (fun _ => 0) (fun _ => 1) ()
    refine ⟨u, finiteAffineTerm_continuous _ _ _ _ _,
      finiteAffineTerm_strictMono _ zero_lt_one (fun _ => zero_lt_one),
      finiteAffineTerm_concaveOn _ _ _ _ _, ?_⟩
    exact fun i => isEmptyElim i
  | inr hI =>
    obtain ⟨v, lam, hlam, hineq⟩ := lemma_4_5 hG
    have hv : ∀ i j, v i ≤ v j + lam j *
        (AffineExpenditure (D.price j) (D.bundle i).val -
          AffineExpenditure (D.price j) (D.bundle j).val) := by
      intro i j
      simpa only [garp_cost_eq_difference hG, Expenditure, AffineExpenditure] using hineq i j
    let u := FiniteAffineEnvelope D.price (fun i => (D.bundle i).val) v lam
    refine ⟨u, finiteAffineEnvelope_continuous _ _ _ _,
      finiteAffineEnvelope_strictMono hlam D.price_pos,
      finiteAffineEnvelope_concaveOn _ _ _ _, ?_⟩
    intro i
    refine ⟨D.feasible i, fun x hx => ?_⟩
    apply finiteAffineEnvelope_maximizes hv i (hlam i).le
    change Expenditure (D.price i) x.val ≤ Expenditure (D.price i) (D.bundle i).val
    rw [garp_budget_exhaustion hG]
    exact hx

/-- **Proposition 4.3:** GARP is equivalent to primitive rational, insatiable rationalization. -/
theorem proposition_4_3 [Finite I] (hk : 0 < k) (D : MarketData I k) :
    GARP D ↔ ∃ r, Rational r ∧ LocallyInsatiable r ∧ Rationalizes D r := by
  constructor
  · intro hG
    obtain ⟨u, _, hm, _, hR⟩ := garp_exists_concave_utility hG
    refine ⟨UtilityPref (fun x : NonnegativeOrthant k => u x.val),
      utilityPref_rational _, ?_, hR⟩
    exact strictlyMonotone_locallyInsatiable hk
      (strictlyMonotonePreference_of_strictMono (fun _ _ h => hm h))
  · rintro ⟨r, hr, hl, hR⟩
    exact rationalizes_garp hr hl hR

/-- Afriat's stronger regularity conclusion imposes no further restriction on finite data. -/
theorem garp_iff_regular_rationalizable [Finite I] (hk : 0 < k) (D : MarketData I k) :
    GARP D ↔ ∃ r, Rational r ∧ ContinuousPreference r ∧
      StrictlyMonotonePreference r ∧
      ConvexPreference (convex_Ici (0 : Fin k → ℝ)) r ∧ Rationalizes D r := by
  constructor
  · intro hG
    obtain ⟨u, hc, hm, hconc, hR⟩ := garp_exists_concave_utility hG
    exact ⟨UtilityPref (fun x : NonnegativeOrthant k => u x.val),
      utilityPref_rational _,
      continuousPreference_of_continuous_utility (hc.comp continuous_subtype_val),
      strictlyMonotonePreference_of_strictMono (fun _ _ h => hm h),
      convexPreference_of_concaveOn hconc, hR⟩
  · rintro ⟨r, hr, _, hm, _, hR⟩
    exact rationalizes_garp hr (strictlyMonotone_locallyInsatiable hk hm) hR

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Slutsky compensation and the Giffen implication

Kreps I, Propositions 4.6-4.8, pp. 76-77, and Problem 4.4, p. 78. The proofs
use primitive rational, locally insatiable preferences and actual maximizers.
They require neither differentiability nor uniqueness. Proposition 4.7 takes the
lower-income maximizer conditionally, as the source explicitly permits when
continuity is not maintained.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A price increase changes exactly one coordinate. -/
def OwnPriceIncrease (p q : Fin k → ℝ) (i : Fin k) : Prop :=
  p i < q i ∧ ∀ j, j ≠ i → q j = p j

/-- Expenditure changes by the own-price increment times the purchased quantity. -/
theorem expenditure_own_price {p q : Fin k → ℝ} {i : Fin k}
    (h : ∀ j, j ≠ i → q j = p j) (x : Fin k → ℝ) :
    Expenditure q x = Expenditure p x + (q i - p i) * x i := by
  classical
  have he : ∀ j, q j * x j = p j * x j +
      if j = i then (q i - p i) * x i else 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [ite_eq_left]
      ring
    · simp [hj, h j hj]
  simp only [Expenditure, he, Finset.sum_add_distrib]
  simp

/-- Slutsky compensation makes the new choice no cheaper at the old prices. -/
theorem compensated_old_expenditure (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) :
    Expenditure p x.val ≤ Expenditure p z.val := by
  rw [optimal_budget_exhaustion hr hl hx]
  apply le_of_not_gt
  intro hs
  exact (lemma_4_1 hr hl hx hs).2 (hz.2 x (by simp [Budget]))

/-- **Proposition 4.6:** the compensated own-price effect is nonpositive. -/
theorem proposition_4_6 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) : z.val i ≤ x.val i := by
  have hcost := compensated_old_expenditure hr hl hx hz
  have hnew := optimal_budget_exhaustion hr hl hz
  rw [expenditure_own_price hp.2 z.val, expenditure_own_price hp.2 x.val] at hnew
  have hmul : (q i - p i) * z.val i ≤ (q i - p i) * x.val i := by linarith
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hp.1)).mp hmul

/-- The price-change dot product expands into the difference of the two cost changes. -/
theorem expenditure_price_quantity_difference (p q x z : Fin k → ℝ) :
    Expenditure (q - p) (z - x) =
      (Expenditure q z - Expenditure q x) -
        (Expenditure p z - Expenditure p x) := by
  unfold Expenditure
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Proposition 4.8 / Problem 4.4:** the compensated price-quantity dot product is nonpositive. -/
theorem proposition_4_8 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q (Expenditure q x.val))) :
    Expenditure (q - p) (z.val - x.val) ≤ 0 := by
  rw [expenditure_price_quantity_difference, optimal_budget_exhaustion hr hl hz]
  have h := compensated_old_expenditure hr hl hx hz
  linarith

/-- A Giffen response is strictly cheaper at the original prices and hence lowers income. -/
theorem giffen_lower_income (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hz : z ∈ PrefChoice r (Budget q y))
    (hg : x.val i < z.val i) : Expenditure p z.val < y := by
  have hnew := optimal_budget_exhaustion hr hl hz
  rw [expenditure_own_price hp.2 z.val] at hnew
  have hzpos : 0 < z.val i := (x.property i).trans_lt hg
  have hprod := mul_pos (sub_pos.mpr hp.1) hzpos
  linarith

/-- A lower-income choice in the Giffen argument consumes at least the new own quantity. -/
theorem giffen_lower_income_quantity (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {z w : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hz : z ∈ PrefChoice r (Budget q y))
    (hw : w ∈ PrefChoice r (Budget p (Expenditure p z.val))) : z.val i ≤ w.val i := by
  apply le_of_not_gt
  intro hlt
  have hwcost := optimal_budget_exhaustion hr hl hw
  have hzq := optimal_budget_exhaustion hr hl hz
  have hprod := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hp.1)
  have hwq : Expenditure q w.val < y := by
    rw [expenditure_own_price hp.2 w.val, hwcost]
    rw [expenditure_own_price hp.2 z.val] at hzq
    linarith
  exact (lemma_4_1 hr hl hz hwq).2 (hw.2 z (by simp [Budget]))

/-- **Proposition 4.7:** Giffen behavior implies a strict inferior-good comparison. -/
theorem proposition_4_7 (hr : Rational r) (hl : LocallyInsatiable r)
    {p q : Fin k → ℝ} {i : Fin k} {y : ℝ} {x z w : NonnegativeOrthant k}
    (hp : OwnPriceIncrease p q i) (hx : x ∈ PrefChoice r (Budget p y))
    (hz : z ∈ PrefChoice r (Budget q y))
    (hg : x.val i < z.val i)
    (hw : w ∈ PrefChoice r (Budget p (Expenditure p z.val))) :
    Expenditure p z.val < y ∧ x.val i < w.val i := by
  have hy := optimal_budget_exhaustion hr hl hx
  have hlow : Expenditure p z.val < Expenditure p x.val := by
    rw [hy]
    exact giffen_lower_income hr hl hp hz hg
  exact ⟨hy ▸ hlow, hg.trans_le (giffen_lower_income_quantity hr hl hp hz hw)⟩

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Direct rankings, unique choices, and income effects

Kreps I, pp. 71 and 73-75. Afriat's regularity conclusion concerns finite market
data; directly elicited rankings can contradict convexity or monotonicity.
The stronger boundary comparison called WARP in the source requires unique
maximizers. Strict convexity suffices for uniqueness. Zero income forces zero
consumption, so globally nonincreasing nonnegative demand must vanish.

`StrictlyConvexPreference` is an attributed local copy from Chapter 2,
`ConvexPreference.lean`, originating at commit `7d496c5`.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}
variable {r : NonnegativeOrthant k → NonnegativeOrthant k → Prop}

/-- A nontrivial mixture of distinct bundles is strictly above the worse endpoint. -/
def StrictlyConvexPreference {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (r : S → S → Prop) : Prop :=
  ∀ x y, x ≠ y → r x y → ∀ a, ∀ ha : a ∈ Set.Ioo 0 1,
    Strict r (Mix hS x y a ⟨ha.1.le, ha.2.le⟩) y

/-- A strict preference for a coordinatewise dominated bundle rejects monotonicity. -/
theorem dominated_strict_ranking_not_monotone {x y : NonnegativeOrthant k}
    (hxy : x ≤ y) (hp : Strict r x y) : ¬(∀ a b, b ≤ a → r a b) :=
  fun hm => hp.2 (hm y x hxy)

/-- Strictly preferring both endpoints to their midpoint rejects convex preference. -/
theorem midpoint_strict_rankings_not_convex (hr : Rational r)
    (x y : NonnegativeOrthant k)
    (hx : Strict r x (Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num)))
    (hy : Strict r y (Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num))) :
    ¬ConvexPreference (convex_Ici (0 : Fin k → ℝ)) r := by
  intro hc
  rcases hr.1 x y with hxy | hyx
  · exact hy.2 (hc x y hxy (1 / 2) (by norm_num))
  · have he : Mix (convex_Ici (0 : Fin k → ℝ)) y x (1 / 2) (by norm_num) =
        Mix (convex_Ici (0 : Fin k → ℝ)) x y (1 / 2) (by norm_num) := by
      apply Subtype.ext
      ext j
      simp only [Mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact hx.2 (he ▸ hc y x hyx (1 / 2) (by norm_num))

/-- Convex mixtures of affordable nonnegative bundles remain affordable. -/
theorem budget_mix {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ Budget p y) (hz : z ∈ Budget p y) {a : ℝ} (ha : a ∈ Set.Icc 0 1) :
    Mix (convex_Ici (0 : Fin k → ℝ)) x z a ha ∈ Budget p y := by
  change Expenditure p (a • x.val + (1 - a) • z.val) ≤ y
  have he := affineExpenditure_mix p x.val z.val a (1 - a)
  change Expenditure p (a • x.val + (1 - a) • z.val) =
    a * Expenditure p x.val + (1 - a) * Expenditure p z.val at he
  rw [he]
  change Expenditure p x.val ≤ y at hx
  change Expenditure p z.val ≤ y at hz
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx),
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hz)]

/-- Strict convexity makes the budget maximizer unique whenever it exists. -/
theorem strictlyConvex_budget_choice_unique
    (hc : StrictlyConvexPreference (convex_Ici (0 : Fin k → ℝ)) r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : z ∈ PrefChoice r (Budget p y)) : x = z := by
  by_contra hne
  have hs := hc x z hne (hx.2 z hz.1) (1 / 2) (by norm_num)
  exact hs.2 (hz.2 _ (budget_mix hx.1 hz.1 (by norm_num)))

/-- The source's WARP boundary comparison follows from uniqueness, not insatiability alone. -/
theorem unique_choice_strict (hr : Rational r) {A : Set (NonnegativeOrthant k)}
    {x z : NonnegativeOrthant k} (hx : x ∈ PrefChoice r A)
    (hu : ∀ w ∈ PrefChoice r A, w = x) (hz : z ∈ A) (hne : z ≠ x) : Strict r x z := by
  refine ⟨hx.2 z hz, ?_⟩
  intro hzx
  exact hne (hu z ⟨hz, fun w hw => hr.2 _ _ _ hzx (hx.2 w hw)⟩)

/-- Strictly convex preferences give the strict boundary comparison for every other bundle. -/
theorem strictlyConvex_choice_strict (hr : Rational r)
    (hc : StrictlyConvexPreference (convex_Ici (0 : Fin k → ℝ)) r)
    {p : Fin k → ℝ} {y : ℝ} {x z : NonnegativeOrthant k}
    (hx : x ∈ PrefChoice r (Budget p y)) (hz : z ∈ Budget p y) (hne : z ≠ x) :
    Strict r x z :=
  unique_choice_strict hr hx (fun _ hw => strictlyConvex_budget_choice_unique hc hw hx) hz hne

/-- Positive prices and zero income leave only the zero commodity vector affordable. -/
theorem zero_income_bundle_zero {p : Fin k → ℝ} (hp : ∀ i, 0 < p i)
    {x : NonnegativeOrthant k} (hx : x ∈ Budget p 0) : x.val = 0 := by
  ext i
  have hterm : p i * x.val i ≤ Expenditure p x.val :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hp j).le (x.property j)) (Finset.mem_univ i)
  have hnonpos : x.val i ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge (hterm.trans hx)) (mul_pos (hp i) hpos)
  exact le_antisymm hnonpos (x.property i)

/-- A nonnegative demand coordinate falling at every income must never be consumed. -/
theorem globally_inferior_demand_zero {p : Fin k → ℝ} (hp : ∀ i, 0 < p i)
    (d : NNReal → NonnegativeOrthant k) (hd : ∀ y : NNReal, d y ∈ Budget p (y : ℝ))
    (i : Fin k)
    (hfall : Antitone (fun y => (d y).val i)) : ∀ y, (d y).val i = 0 := by
  intro y
  have hz : (d 0).val i = 0 := congrFun (zero_income_bundle_zero hp (hd 0)) i
  have hle : (d y).val i ≤ (d 0).val i := hfall (show (0 : NNReal) ≤ y from zero_le)
  rw [hz] at hle
  exact le_antisymm hle ((d y).property i)

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A two-good Giffen example with unique choices

Kreps I, Problem 4.3, p. 78, asks for an indifference-curve diagram showing a
Giffen good. The formula and numbers below are a constructed witness, not an
example specified by Kreps. Utility is the minimum of two increasing affine
functions on the full nonnegative orthant. At income ten, raising only the first
price from one to two changes unique demand from `(1,9)` to `(2,6)`.

The reproducible diagram `docs/assets/giffen-example.svg` plots these exact budget
lines and utility levels; `scripts/plot_giffen_example.py` generates it. All
feasibility, global optimality and uniqueness claims are proved here independently
of plotting or numerical optimization.
-/

namespace Kreps.RevealedPreference

/-- A constructed concave utility, defined on all real two-good vectors. -/
def GiffenUtility (x : Fin 2 → ℝ) : ℝ :=
  min (x 0 + 2 * x 1) (13 * x 0 + 6 * x 1 - 48)

/-- The preference used by the example, on the entire nonnegative consumption domain. -/
def GiffenPreference : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop :=
  UtilityPref (fun x => GiffenUtility x.val)

/-- Both goods initially have unit prices. -/
def GiffenOldPrices : Fin 2 → ℝ := ![1, 1]

/-- Only the price of the first good rises, from one to two. -/
def GiffenNewPrices : Fin 2 → ℝ := ![2, 1]

/-- The unique original consumption bundle in the constructed example. -/
def GiffenOldBundle : NonnegativeOrthant 2 :=
  ⟨![1, 9], by intro j; fin_cases j <;> norm_num⟩

/-- The unique new bundle buys more of the now more expensive first good. -/
def GiffenNewBundle : NonnegativeOrthant 2 :=
  ⟨![2, 6], by intro j; fin_cases j <;> norm_num⟩

/-- The constructed utility is continuous everywhere, including on the orthant boundary. -/
theorem giffenUtility_continuous : Continuous GiffenUtility := by
  unfold GiffenUtility
  fun_prop

/-- Both affine pieces are concave, so their minimum is concave on the full vector space. -/
theorem giffenUtility_concaveOn : ConcaveOn ℝ Set.univ GiffenUtility := by
  have hfirst : ConcaveOn ℝ Set.univ (fun x : Fin 2 → ℝ => x 0 + 2 * x 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hsecond : ConcaveOn ℝ Set.univ
      (fun x : Fin 2 → ℝ => 13 * x 0 + 6 * x 1 - 48) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  exact hfirst.inf hsecond

/-- Increasing some coordinate and decreasing none strictly increases the constructed utility. -/
theorem giffenUtility_strictMono : StrictMono GiffenUtility := by
  intro x y hxy
  have hfirst := affineExpenditure_strictMono
    (p := (![1, 2] : Fin 2 → ℝ)) (by intro j; fin_cases j <;> norm_num) hxy
  have hsecond := affineExpenditure_strictMono
    (p := (![13, 6] : Fin 2 → ℝ)) (by intro j; fin_cases j <;> norm_num) hxy
  simp only [AffineExpenditure, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Fin.sum_univ_zero, add_zero, one_mul] at hfirst hsecond
  exact lt_min ((min_le_left _ _).trans_lt hfirst)
    ((min_le_right _ _).trans_lt (sub_lt_sub_right hsecond 48))

/-- The full-domain constructed preference has all the regularity properties in Afriat's theorem. -/
theorem giffenPreference_regular :
    Rational GiffenPreference ∧ ContinuousPreference GiffenPreference ∧
      StrictlyMonotonePreference GiffenPreference ∧ LocallyInsatiable GiffenPreference ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) GiffenPreference := by
  have hm : StrictlyMonotonePreference GiffenPreference :=
    strictlyMonotonePreference_of_strictMono (fun _ _ h => giffenUtility_strictMono h)
  exact ⟨utilityPref_rational _,
    continuousPreference_of_continuous_utility
      (giffenUtility_continuous.comp continuous_subtype_val), hm,
    strictlyMonotone_locallyInsatiable (by norm_num) hm,
    convexPreference_of_concaveOn giffenUtility_concaveOn⟩

/-- Every price is strictly positive in each of the two observations. -/
theorem giffenPrices_positive (j : Fin 2) :
    0 < GiffenOldPrices j ∧ 0 < GiffenNewPrices j := by
  fin_cases j <;> norm_num [GiffenOldPrices, GiffenNewPrices]

/-- The price change is exactly an increase of the first commodity's price. -/
theorem giffenPrices_ownPriceIncrease : OwnPriceIncrease GiffenOldPrices GiffenNewPrices 0 := by
  constructor
  · norm_num [GiffenOldPrices, GiffenNewPrices]
  · intro j hj
    fin_cases j <;> simp_all [GiffenOldPrices, GiffenNewPrices]

/-- The original bundle is affordable at income ten. -/
theorem giffen_old_feasible : GiffenOldBundle ∈ Budget GiffenOldPrices 10 := by
  norm_num [Budget, Expenditure, GiffenOldPrices, GiffenOldBundle, Fin.sum_univ_succ]

/-- The new bundle is affordable at income ten after the first price increases. -/
theorem giffen_new_feasible : GiffenNewBundle ∈ Budget GiffenNewPrices 10 := by
  norm_num [Budget, Expenditure, GiffenNewPrices, GiffenNewBundle, Fin.sum_univ_succ]

/-- Each selected bundle uses exactly the same income, ten, at its corresponding prices. -/
theorem giffen_budget_exhaustion :
    Expenditure GiffenOldPrices GiffenOldBundle.val = 10 ∧
      Expenditure GiffenNewPrices GiffenNewBundle.val = 10 := by
  norm_num [Expenditure, GiffenOldPrices, GiffenNewPrices, GiffenOldBundle,
    GiffenNewBundle, Fin.sum_univ_succ]

/-- The original optimum lies on the indifference curve of utility nineteen. -/
theorem giffen_old_value : GiffenUtility GiffenOldBundle.val = 19 := by
  norm_num [GiffenUtility, GiffenOldBundle]

/-- The new optimum lies on the indifference curve of utility fourteen. -/
theorem giffen_new_value : GiffenUtility GiffenNewBundle.val = 14 := by
  norm_num [GiffenUtility, GiffenNewBundle]

/-- Every originally affordable bundle gives utility at most nineteen. -/
theorem giffen_old_maximum {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenOldPrices 10) : GiffenUtility x.val ≤ 19 := by
  have hb : x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenOldPrices, Fin.sum_univ_succ] using hx
  by_cases hfirst : x.val 0 ≤ 1
  · exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-- Equality in the old budget bound forces exactly the original bundle. -/
theorem giffen_old_unique {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenOldPrices 10) (hu : 19 ≤ GiffenUtility x.val) :
    x = GiffenOldBundle := by
  have hb : x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenOldPrices, Fin.sum_univ_succ] using hx
  obtain ⟨hfirst, hsecond⟩ := le_min_iff.mp hu
  have hzero : x.val 0 = 1 := by linarith
  have hone : x.val 1 = 9 := by linarith
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hzero
  · exact hone

/-- Every bundle affordable after the price rise gives utility at most fourteen. -/
theorem giffen_new_maximum {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenNewPrices 10) : GiffenUtility x.val ≤ 14 := by
  have hb : 2 * x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenNewPrices, Fin.sum_univ_succ] using hx
  by_cases hfirst : x.val 0 ≤ 2
  · exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-- Equality in the new budget bound forces exactly the new bundle. -/
theorem giffen_new_unique {x : NonnegativeOrthant 2}
    (hx : x ∈ Budget GiffenNewPrices 10) (hu : 14 ≤ GiffenUtility x.val) :
    x = GiffenNewBundle := by
  have hb : 2 * x.val 0 + x.val 1 ≤ 10 := by
    simpa [Budget, Expenditure, GiffenNewPrices, Fin.sum_univ_succ] using hx
  obtain ⟨hfirst, hsecond⟩ := le_min_iff.mp hu
  have hzero : x.val 0 = 2 := by linarith
  have hone : x.val 1 = 6 := by linarith
  apply Subtype.ext
  funext j
  fin_cases j
  · exact hzero
  · exact hone

/-- The entire original choice set consists of the single bundle `(1,9)`. -/
theorem giffen_old_choice :
    PrefChoice GiffenPreference (Budget GiffenOldPrices 10) = {GiffenOldBundle} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply giffen_old_unique hx.1
    have h := hx.2 GiffenOldBundle giffen_old_feasible
    change GiffenUtility GiffenOldBundle.val ≤ GiffenUtility x.val at h
    rwa [giffen_old_value] at h
  · rintro rfl
    refine ⟨giffen_old_feasible, ?_⟩
    intro z hz
    change GiffenUtility z.val ≤ GiffenUtility GiffenOldBundle.val
    rw [giffen_old_value]
    exact giffen_old_maximum hz

/-- The entire new choice set consists of the single bundle `(2,6)`. -/
theorem giffen_new_choice :
    PrefChoice GiffenPreference (Budget GiffenNewPrices 10) = {GiffenNewBundle} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply giffen_new_unique hx.1
    have h := hx.2 GiffenNewBundle giffen_new_feasible
    change GiffenUtility GiffenNewBundle.val ≤ GiffenUtility x.val at h
    rwa [giffen_new_value] at h
  · rintro rfl
    refine ⟨giffen_new_feasible, ?_⟩
    intro z hz
    change GiffenUtility z.val ≤ GiffenUtility GiffenNewBundle.val
    rw [giffen_new_value]
    exact giffen_new_maximum hz

/-- **Problem 4.3:** the same regular preference has unique demand rising with its own price. -/
theorem problem_4_3 :
    Rational GiffenPreference ∧ ContinuousPreference GiffenPreference ∧
      StrictlyMonotonePreference GiffenPreference ∧ LocallyInsatiable GiffenPreference ∧
      ConvexPreference (convex_Ici (0 : Fin 2 → ℝ)) GiffenPreference ∧
      OwnPriceIncrease GiffenOldPrices GiffenNewPrices 0 ∧
      PrefChoice GiffenPreference (Budget GiffenOldPrices 10) = {GiffenOldBundle} ∧
      PrefChoice GiffenPreference (Budget GiffenNewPrices 10) = {GiffenNewBundle} ∧
      GiffenOldBundle.val 0 < GiffenNewBundle.val 0 := by
  obtain ⟨hr, hc, hm, hl, hv⟩ := giffenPreference_regular
  exact ⟨hr, hc, hm, hl, hv, giffenPrices_ownPriceIncrease, giffen_old_choice,
    giffen_new_choice, by norm_num [GiffenOldBundle, GiffenNewBundle]⟩

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The literal market datasets

Kreps I, Table 4.1 and the modified third observation, pp. 67-70, and Table 4.2,
Problem 4.1, p. 78. All prices, incomes, bundles and cross-expenditure entries
are exact rational numbers. GARP certificates control arbitrary revealed chains;
the positive conclusions rationalize complete budget sets on the full orthant.
-/

namespace Kreps.RevealedPreference

/-- The three chosen bundles in Table 4.1, retained in the modified example. -/
noncomputable def InitialBundles (i : Fin 3) : NonnegativeOrthant 3 :=
  ⟨![![10, 10, 10], ![9, 25, 15 / 2], ![15, 5, 9]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩

/-- The original three observations from pp. 67-68. -/
noncomputable def InitialData : MarketData (Fin 3) 3 where
  price := ![![10, 10, 10], ![10, 1, 2], ![1, 1, 10]]
  income := ![300, 130, 110]
  bundle := InitialBundles
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, InitialBundles, Fin.sum_univ_succ]

/-- Every literal entry of Table 4.1, with its printed rows of bundles and columns of prices. -/
theorem table_4_1_costs (i j : Fin 3) :
    Expenditure (InitialData.price j) (InitialData.bundle i).val =
      ![![300, 130, 120], ![415, 130, 109], ![290, 173, 110]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [InitialData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- All original observations use their entire stated income. -/
theorem initialData_exhausts (i : Fin 3) :
    Expenditure (InitialData.price i) (InitialData.bundle i).val = InitialData.income i := by
  fin_cases i <;>
    norm_num [InitialData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The original three observations contain the source's strict revealed cycle. -/
theorem initialData_not_garp : ¬GARP InitialData := by
  intro hG
  apply hG 0
  apply revealedStrict_weak_trans (directStrict_revealedStrict (j := 2) ?_)
    ((directWeak_revealedWeak (j := 1) ?_).trans (directWeak_revealedWeak ?_))
  all_goals norm_num [DirectStrict, DirectWeak, MarketData.cost, InitialData,
    InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The original example cannot be rationalized by primitive rational insatiable preferences. -/
theorem initialData_not_rationalizable :
    ¬∃ r, Rational r ∧ LocallyInsatiable r ∧ Rationalizes InitialData r :=
  fun ⟨_, hr, hl, hR⟩ => initialData_not_garp (rationalizes_garp hr hl hR)

/-- The modified third price vector and income from p. 69. -/
noncomputable def ModifiedData : MarketData (Fin 3) 3 where
  price := ![![10, 10, 10], ![10, 1, 2], ![1, 2, 10]]
  income := ![300, 130, 115]
  bundle := InitialBundles
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, InitialBundles, Fin.sum_univ_succ]

/-- At the modified third prices, the other bundles cost 130 and 134, both above 115. -/
theorem modifiedData_third_costs (i : Fin 3) :
    Expenditure (ModifiedData.price 2) (ModifiedData.bundle i).val = ![130, 134, 115] i := by
  fin_cases i <;>
    norm_num [ModifiedData, InitialBundles, Expenditure, Fin.sum_univ_succ]

/-- The modified observations have no strict revealed cycle. -/
theorem modifiedData_garp : GARP ModifiedData := by
  apply matrixGARP_of_scores ![1, 2, 0]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectWeak, MarketData.cost, ModifiedData, InitialBundles,
        Expenditure, Fin.sum_univ_succ] at *
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectStrict, MarketData.cost, ModifiedData, InitialBundles,
        Expenditure, Fin.sum_univ_succ] at *

/-- The modified example has a regular utility rationalizer on the entire commodity space. -/
theorem modifiedData_rationalizable :
    ∃ u : (Fin 3 → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧ ConcaveOn ℝ Set.univ u ∧
      Rationalizes ModifiedData (UtilityPref (fun x : NonnegativeOrthant 3 => u x.val)) :=
  garp_exists_concave_utility modifiedData_garp

/-- The four observations stated in Table 4.2, Problem 4.1. -/
noncomputable def Problem41Data : MarketData (Fin 4) 3 where
  price := ![![1, 1, 1], ![3, 1, 1], ![1, 2, 2], ![1, 1, 2]]
  income := ![20, 20, 25, 20]
  bundle := fun i => ⟨![![10, 5, 5], ![3, 5, 6], ![13, 3, 3], ![15, 3, 1]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; fin_cases i <;> norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, Fin.sum_univ_succ]

/-- Exact cross-expenditures for Table 4.2, with rows of prices and columns of bundles. -/
theorem table_4_2_costs (i j : Fin 4) :
    Expenditure (Problem41Data.price i) (Problem41Data.bundle j).val =
      ![![20, 14, 19, 19], ![40, 20, 45, 49], ![30, 25, 25, 23], ![25, 20, 22, 20]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Problem41Data, Expenditure, Fin.sum_univ_succ]

/-- **Problem 4.1:** the order of revealed comparisons is first, third, fourth, second. -/
theorem problem_4_1_garp : GARP Problem41Data := by
  apply matrixGARP_of_scores ![3, 0, 2, 1]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectWeak, MarketData.cost, Problem41Data, Expenditure, Fin.sum_univ_succ] at *
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [DirectStrict, MarketData.cost, Problem41Data, Expenditure, Fin.sum_univ_succ] at *

/-- **Problem 4.1:** the literal four observations admit the full regular consumer model. -/
theorem problem_4_1 :
    ∃ u : (Fin 3 → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧ ConcaveOn ℝ Set.univ u ∧
      Rationalizes Problem41Data (UtilityPref (fun x : NonnegativeOrthant 3 => u x.val)) :=
  garp_exists_concave_utility problem_4_1_garp

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Why the maintained restrictions matter

Kreps I, p. 68, permits indifference throughout the region where every good is
below 1000, without requiring indifference everywhere. A nonconstant utility
with exactly this plateau rationalizes the otherwise inconsistent original data.
The p. 73 distinction between strict interior and boundary comparisons is also
witnessed by a strictly increasing linear utility with tied budget maximizers.
-/

namespace Kreps.RevealedPreference

variable {k : ℕ}

/-- A nonconstant utility flat on the box below the source's threshold 1000. -/
noncomputable def ThousandPlateauUtility (x : Fin k → ℝ) : ℝ :=
  ∑ i, max 0 (x i - 1000)

/-- Every bundle whose coordinates are at most 1000 has zero plateau utility. -/
theorem thousandPlateauUtility_zero {x : Fin k → ℝ} (hx : ∀ i, x i ≤ 1000) :
    ThousandPlateauUtility x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact max_eq_left (sub_nonpos.mpr (hx i))

/-- All bundles in the book's open box are indifferent to one another. -/
theorem thousandPlateauUtility_indifferent {x z : NonnegativeOrthant k}
    (hx : ∀ i, x.val i < 1000) (hz : ∀ i, z.val i < 1000) :
    Indifferent (UtilityPref
      (fun w : NonnegativeOrthant k => ThousandPlateauUtility w.val)) x z := by
  change ThousandPlateauUtility z.val ≤ ThousandPlateauUtility x.val ∧
    ThousandPlateauUtility x.val ≤ ThousandPlateauUtility z.val
  rw [thousandPlateauUtility_zero (fun i => (hx i).le),
    thousandPlateauUtility_zero (fun i => (hz i).le)]
  exact ⟨le_rfl, le_rfl⟩

/-- Prices of at least one bound each affordable quantity by income. -/
theorem affordable_coordinate_le_income {p : Fin k → ℝ} (hp : ∀ i, 1 ≤ p i)
    {y : ℝ} {x : NonnegativeOrthant k} (hx : x ∈ Budget p y) (i : Fin k) : x.val i ≤ y := by
  calc
    x.val i ≤ p i * x.val i := le_mul_of_one_le_left (x.property i) (hp i)
    _ ≤ Expenditure p x.val := Finset.single_le_sum
      (fun j _ => mul_nonneg (zero_le_one.trans (hp j)) (x.property j)) (Finset.mem_univ i)
    _ ≤ y := hx

/-- The nonconstant plateau utility rationalizes every budget in the original inconsistent data. -/
theorem thousandPlateauUtility_rationalizes :
    Rationalizes InitialData
      (UtilityPref (fun x : NonnegativeOrthant 3 => ThousandPlateauUtility x.val)) := by
  intro i
  have hp : ∀ j, 1 ≤ InitialData.price i j := by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [InitialData]
  have hy : InitialData.income i ≤ 1000 := by fin_cases i <;> norm_num [InitialData]
  have hz (x : NonnegativeOrthant 3) (hx : x ∈ Budget (InitialData.price i)
      (InitialData.income i)) : ThousandPlateauUtility x.val = 0 :=
    thousandPlateauUtility_zero (fun j => (affordable_coordinate_le_income hp hx j).trans hy)
  refine ⟨InitialData.feasible i, fun x hx => ?_⟩
  change ThousandPlateauUtility x.val ≤ ThousandPlateauUtility (InitialData.bundle i).val
  rw [hz x hx, hz _ (InitialData.feasible i)]

/-- The plateau utility is not the constant indifference representation. -/
theorem thousandPlateauUtility_nonconstant :
    ThousandPlateauUtility (![0, 0, 0] : Fin 3 → ℝ) = 0 ∧
      ThousandPlateauUtility (![1001, 0, 0] : Fin 3 → ℝ) = 1 := by
  norm_num [ThousandPlateauUtility, Fin.sum_univ_succ]

/-- Linear utility leaves distinct bundles on the same budget boundary indifferent. -/
theorem linear_boundary_tie :
    ∃ r : NonnegativeOrthant 2 → NonnegativeOrthant 2 → Prop,
      Rational r ∧ LocallyInsatiable r ∧
      ∃ x z : NonnegativeOrthant 2,
        x ≠ z ∧ x ∈ PrefChoice r (Budget ![1, 1] 1) ∧
        z ∈ PrefChoice r (Budget ![1, 1] 1) ∧ ¬Strict r x z := by
  let u : NonnegativeOrthant 2 → ℝ := fun x => Expenditure ![1, 1] x.val
  let x : NonnegativeOrthant 2 := ⟨![1, 0], by intro i; fin_cases i <;> norm_num⟩
  let z : NonnegativeOrthant 2 := ⟨![0, 1], by intro i; fin_cases i <;> norm_num⟩
  have hu : StrictMono u := by
    intro a b hab
    exact affineExpenditure_strictMono (by intro i; fin_cases i <;> norm_num) hab
  have hxu : u x = 1 := by norm_num [u, x, Expenditure, Fin.sum_univ_two]
  have hzu : u z = 1 := by norm_num [u, z, Expenditure, Fin.sum_univ_two]
  refine ⟨UtilityPref u, utilityPref_rational u,
    strictlyMonotone_locallyInsatiable (by norm_num)
      (strictlyMonotonePreference_of_strictMono hu), x, z, ?_, ?_, ?_, ?_⟩
  · intro he
    have h := congrArg (fun w : NonnegativeOrthant 2 => w.val 0) he
    norm_num [x, z] at h
  · refine ⟨hxu.le, fun w hw => ?_⟩
    change u w ≤ u x
    rw [hxu]
    exact hw
  · refine ⟨hzu.le, fun w hw => ?_⟩
    change u w ≤ u z
    rw [hzu]
    exact hw
  · intro hs
    apply hs.2
    change u x ≤ u z
    rw [hxu, hzu]

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Own-price observations and a boundary correction

Kreps I, p. 75. The two-observation argument assumes positive consumption of the
changing-price commodity in the original observation. The later finite-sequence
claim omits this condition and is false at the boundary. We prove the corrected
finite-data assertion and an exact two-observation counterexample to the printed
unrestricted claim. See `docs/corrections.md`.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} {k : ℕ}

/-- At common income with other prices fixed, cross-cost is the own-price difference. -/
theorem ownPriceData_cost {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l) (i j : I) :
    D.cost i j = (D.price i g - D.price j g) * (D.bundle j).val g := by
  unfold MarketData.cost
  rw [expenditure_own_price (fun l hl => hp i j l hl), he j, hy j i]
  ring

/-- Positive own-good quantities validate the finite own-price consistency claim. -/
theorem garp_of_own_price_data {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l)
    (hx : ∀ i, 0 < (D.bundle i).val g) : GARP D := by
  apply matrixGARP_of_scores (fun i => -D.price i g)
  · intro i j hij
    change D.cost i j ≤ 0 at hij
    rw [ownPriceData_cost he hy hp i j] at hij
    have h : D.price i g - D.price j g ≤ 0 :=
      le_of_not_gt (fun hh => (not_lt_of_ge hij) (mul_pos hh (hx j)))
    linarith
  · intro i j hij
    change D.cost i j < 0 at hij
    rw [ownPriceData_cost he hy hp i j] at hij
    have h : D.price i g - D.price j g < 0 :=
      lt_of_not_ge (fun hh => (not_le_of_gt hij) (mul_nonneg hh (hx j).le))
    linarith

/-- The corrected finite own-price assertion supplies a full-domain regular rationalizer. -/
theorem own_price_data_rationalizable [Finite I] {D : MarketData I k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : ∀ i j, D.income i = D.income j)
    (hp : ∀ i j l, l ≠ g → D.price i l = D.price j l)
    (hx : ∀ i, 0 < (D.bundle i).val g) :
    ∃ u : (Fin k → ℝ) → ℝ, Continuous u ∧ StrictMono u ∧
      ConcaveOn ℝ Set.univ u ∧
      Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => u x.val)) :=
  garp_exists_concave_utility (garp_of_own_price_data he hy hp hx)

/-- The source's two-observation claim needs positive own consumption only in the old bundle. -/
theorem garp_two_own_price_observations {D : MarketData (Fin 2) k} {g : Fin k}
    (he : ∀ i, Expenditure (D.price i) (D.bundle i).val = D.income i)
    (hy : D.income 0 = D.income 1) (hp : OwnPriceIncrease (D.price 0) (D.price 1) g)
    (hx : 0 < (D.bundle 0).val g) : GARP D := by
  have hdiag (i : Fin 2) : D.cost i i = 0 := by simp [MarketData.cost, he]
  have h10 : 0 < D.cost 1 0 := by
    unfold MarketData.cost
    rw [expenditure_own_price hp.2, he 0, hy]
    simpa using mul_pos (sub_pos.mpr hp.1) hx
  apply matrixGARP_of_scores ![1, 0]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [DirectWeak, hdiag] at *
    exact (not_le_of_gt h10 hij).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [DirectStrict, hdiag] at *
    exact (not_lt_of_ge h10.le hij).elim

/-- Two feasible exhausted observations at increasing own prices, with zero old own demand. -/
noncomputable def BoundaryOwnPriceData : MarketData (Fin 2) 2 where
  price := ![![1, 1], ![2, 1]]
  income := fun _ => 1
  bundle := fun i => ⟨![![0, 1], ![1 / 4, 1 / 2]] i, by
    intro j
    fin_cases i <;> fin_cases j <;> norm_num⟩
  price_pos := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  income_nonneg := by intro i; norm_num
  feasible := by
    intro i
    fin_cases i <;> norm_num [Expenditure, Fin.sum_univ_two]

/-- Both counterexample observations exhaust the same income. -/
theorem boundaryOwnPriceData_exhausts (i : Fin 2) :
    Expenditure (BoundaryOwnPriceData.price i) (BoundaryOwnPriceData.bundle i).val = 1 := by
  fin_cases i <;> norm_num [BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]

/-- The second observation raises only the first price, from one to two. -/
theorem boundaryOwnPriceData_price_increase :
    OwnPriceIncrease (BoundaryOwnPriceData.price 0) (BoundaryOwnPriceData.price 1) 0 := by
  constructor
  · norm_num [BoundaryOwnPriceData]
  · intro j hj
    fin_cases j <;> norm_num [BoundaryOwnPriceData] at *

/-- The omitted positive-consumption condition permits a strict two-observation cycle. -/
theorem boundaryOwnPriceData_not_garp : ¬GARP BoundaryOwnPriceData := by
  intro hG
  apply hG 0
  apply revealedStrict_weak_trans
    (directStrict_revealedStrict (j := 1) ?_) (directWeak_revealedWeak ?_)
  · norm_num [DirectStrict, MarketData.cost, BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]
  · norm_num [DirectWeak, MarketData.cost, BoundaryOwnPriceData, Expenditure, Fin.sum_univ_two]

end Kreps.RevealedPreference

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The two possible rankings in the modified example

Kreps I, p. 69, allows either a strict ranking of the second bundle above the
first or indifference between them; both dominate the third. We construct
full-domain regular utility rationalizers realizing both possibilities, with
explicit Afriat coefficients. The reusable interpolation results preserve
prescribed utility levels on every observation.
-/

namespace Kreps.RevealedPreference

variable {I : Type*} [Fintype I] [Nonempty I] {k : ℕ}

/-- The affine envelope attached to market data and prescribed Afriat coefficients. -/
noncomputable def DataEnvelope (D : MarketData I k) (v lam : I → ℝ) :
    (Fin k → ℝ) → ℝ := FiniteAffineEnvelope D.price (fun i => (D.bundle i).val) v lam

/-- Positive original-income Afriat inequalities imply exact interpolation at observations. -/
theorem dataEnvelope_at {D : MarketData I k} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hv : ∀ i j, v i ≤ v j + lam j * D.cost j i) (i : I) :
    DataEnvelope D v lam (D.bundle i).val = v i := by
  have hG : GARP D := matrixGARP_of_afriat hlam hv
  apply finiteAffineEnvelope_at_anchor
  intro a b
  simpa only [garp_cost_eq_difference hG, AffineExpenditure, Expenditure] using hv a b

/-- The prescribed envelope rationalizes entire budgets, not just the finite observations. -/
theorem dataEnvelope_rationalizes {D : MarketData I k} {v lam : I → ℝ}
    (hlam : ∀ i, 0 < lam i) (hv : ∀ i j, v i ≤ v j + lam j * D.cost j i) :
    Rationalizes D (UtilityPref (fun x : NonnegativeOrthant k => DataEnvelope D v lam x.val)) := by
  have hG : GARP D := matrixGARP_of_afriat hlam hv
  intro i
  refine ⟨D.feasible i, fun x hx => ?_⟩
  change DataEnvelope D v lam x.val ≤ DataEnvelope D v lam (D.bundle i).val
  rw [dataEnvelope_at hlam hv]
  apply finiteAffineEnvelope_le_value i (hlam i).le
  change Expenditure (D.price i) x.val ≤ Expenditure (D.price i) (D.bundle i).val
  rw [garp_budget_exhaustion hG]
  exact hx

/-- A family realizing both printed rankings, with intermediate utility levels allowed. -/
noncomputable def ModifiedUtility (b : ℝ) : (Fin 3 → ℝ) → ℝ :=
  DataEnvelope ModifiedData ![1, b, 0] ![1 / 20, 1, 1]

/-- All the multipliers used for the modified example are strictly positive. -/
theorem modified_multipliers_pos (i : Fin 3) : 0 < (![1 / 20, 1, 1] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num

/-- The exact Afriat inequalities hold for every prescribed second utility between one and two. -/
theorem modified_afriat {b : ℝ} (hb : b ∈ Set.Icc 1 2) (i j : Fin 3) :
    (![1, b, 0] : Fin 3 → ℝ) i ≤ ![1, b, 0] j +
      ![1 / 20, 1, 1] j * ModifiedData.cost j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [MarketData.cost, ModifiedData, InitialBundles, Expenditure,
      Fin.sum_univ_succ] <;> linarith [hb.1, hb.2]

/-- Each member of the explicit family is continuous, increasing and concave on all vectors. -/
theorem modifiedUtility_regular (b : ℝ) :
    Continuous (ModifiedUtility b) ∧ StrictMono (ModifiedUtility b) ∧
      ConcaveOn ℝ Set.univ (ModifiedUtility b) := by
  unfold ModifiedUtility DataEnvelope
  exact ⟨finiteAffineEnvelope_continuous _ _ _ _,
    finiteAffineEnvelope_strictMono modified_multipliers_pos ModifiedData.price_pos,
    finiteAffineEnvelope_concaveOn _ _ _ _⟩

/-- The explicit utilities rationalize the modified data on the full orthant. -/
theorem modifiedUtility_rationalizes {b : ℝ} (hb : b ∈ Set.Icc 1 2) :
    Rationalizes ModifiedData
      (UtilityPref (fun x : NonnegativeOrthant 3 => ModifiedUtility b x.val)) :=
  dataEnvelope_rationalizes modified_multipliers_pos (modified_afriat hb)

/-- The constructed family has exactly the prescribed three observed utility levels. -/
theorem modifiedUtility_values {b : ℝ} (hb : b ∈ Set.Icc 1 2) (i : Fin 3) :
    ModifiedUtility b (InitialBundles i).val = ![1, b, 0] i :=
  dataEnvelope_at modified_multipliers_pos (modified_afriat hb) i

/-- The source's strict ordering is realized by a full-domain rationalizer. -/
theorem modifiedUtility_strict_rankings :
    ModifiedUtility 2 (InitialBundles 2).val < ModifiedUtility 2 (InitialBundles 0).val ∧
      ModifiedUtility 2 (InitialBundles 0).val < ModifiedUtility 2 (InitialBundles 1).val := by
  simp [modifiedUtility_values (by norm_num : (2 : ℝ) ∈ Set.Icc 1 2)]

/-- The source's alternative indifference is also realized by a full-domain rationalizer. -/
theorem modifiedUtility_tied_rankings :
    ModifiedUtility 1 (InitialBundles 2).val < ModifiedUtility 1 (InitialBundles 0).val ∧
      ModifiedUtility 1 (InitialBundles 0).val = ModifiedUtility 1 (InitialBundles 1).val := by
  simp [modifiedUtility_values (by norm_num : (1 : ℝ) ∈ Set.Icc 1 2)]

end Kreps.RevealedPreference

set_option linter.style.longLine false
#print axioms Kreps.RevealedPreference.Complete
#print axioms Kreps.RevealedPreference.TransitivePref
#print axioms Kreps.RevealedPreference.Rational
#print axioms Kreps.RevealedPreference.Strict
#print axioms Kreps.RevealedPreference.Indifferent
#print axioms Kreps.RevealedPreference.PrefChoice
#print axioms Kreps.RevealedPreference.UtilityPref
#print axioms Kreps.RevealedPreference.Represents
#print axioms Kreps.RevealedPreference.complete_refl
#print axioms Kreps.RevealedPreference.strict_weak_trans
#print axioms Kreps.RevealedPreference.weak_strict_trans
#print axioms Kreps.RevealedPreference.utilityPref_rational
#print axioms Kreps.RevealedPreference.represents_rational
#print axioms Kreps.RevealedPreference.strict_iff_utility_lt
#print axioms Kreps.RevealedPreference.DirectWeak
#print axioms Kreps.RevealedPreference.DirectStrict
#print axioms Kreps.RevealedPreference.RevealedWeak
#print axioms Kreps.RevealedPreference.RevealedStrict
#print axioms Kreps.RevealedPreference.MatrixGARP
#print axioms Kreps.RevealedPreference.directWeak_revealedWeak
#print axioms Kreps.RevealedPreference.directStrict_revealedStrict
#print axioms Kreps.RevealedPreference.revealedStrict_weak
#print axioms Kreps.RevealedPreference.revealedWeak_strict_trans
#print axioms Kreps.RevealedPreference.revealedStrict_weak_trans
#print axioms Kreps.RevealedPreference.revealedStrict_trans
#print axioms Kreps.RevealedPreference.matrixGARP_no_reverse
#print axioms Kreps.RevealedPreference.matrixGARP_iff_return_cost
#print axioms Kreps.RevealedPreference.matrixGARP_diagonal_zero
#print axioms Kreps.RevealedPreference.negative_diagonal_not_matrixGARP
#print axioms Kreps.RevealedPreference.matrixGARP_of_scores
#print axioms Kreps.RevealedPreference.StrictSuccessors
#print axioms Kreps.RevealedPreference.RevealedRank
#print axioms Kreps.RevealedPreference.mem_strictSuccessors
#print axioms Kreps.RevealedPreference.strictSuccessors_subset
#print axioms Kreps.RevealedPreference.revealedRank_le
#print axioms Kreps.RevealedPreference.revealedRank_lt
#print axioms Kreps.RevealedPreference.lemma_4_4a
#print axioms Kreps.RevealedPreference.lemma_4_4b
#print axioms Kreps.RevealedPreference.lemma_4_4c
#print axioms Kreps.RevealedPreference.exists_positive_finite_multiplier
#print axioms Kreps.RevealedPreference.afriat_all_minimal
#print axioms Kreps.RevealedPreference.afriat_of_rank_on_finset
#print axioms Kreps.RevealedPreference.lemma_4_5
#print axioms Kreps.RevealedPreference.FiniteMinimum
#print axioms Kreps.RevealedPreference.finiteMinimum_le
#print axioms Kreps.RevealedPreference.le_finiteMinimum
#print axioms Kreps.RevealedPreference.finiteMinimum_attained
#print axioms Kreps.RevealedPreference.finiteMinimum_continuous
#print axioms Kreps.RevealedPreference.finiteMinimum_strictMono
#print axioms Kreps.RevealedPreference.finiteMinimum_concaveOn
#print axioms Kreps.RevealedPreference.AffineExpenditure
#print axioms Kreps.RevealedPreference.affineExpenditure_continuous
#print axioms Kreps.RevealedPreference.affineExpenditure_strictMono
#print axioms Kreps.RevealedPreference.affineExpenditure_mix
#print axioms Kreps.RevealedPreference.FiniteAffineTerm
#print axioms Kreps.RevealedPreference.finiteAffineTerm_continuous
#print axioms Kreps.RevealedPreference.finiteAffineTerm_strictMono
#print axioms Kreps.RevealedPreference.finiteAffineTerm_mix
#print axioms Kreps.RevealedPreference.finiteAffineTerm_concaveOn
#print axioms Kreps.RevealedPreference.FiniteAffineEnvelope
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_le_term
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_continuous
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_concaveOn
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_strictMono
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_at_anchor
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_le_value
#print axioms Kreps.RevealedPreference.finiteAffineEnvelope_maximizes
#print axioms Kreps.RevealedPreference.NonnegativeOrthant
#print axioms Kreps.RevealedPreference.StrictlyMonotonePreference
#print axioms Kreps.RevealedPreference.LocallyInsatiable
#print axioms Kreps.RevealedPreference.ContinuousPreference
#print axioms Kreps.RevealedPreference.Mix
#print axioms Kreps.RevealedPreference.ConvexPreference
#print axioms Kreps.RevealedPreference.continuousPreference_of_continuous_utility
#print axioms Kreps.RevealedPreference.strictlyMonotonePreference_of_strictMono
#print axioms Kreps.RevealedPreference.locallyInsatiable_iff_open
#print axioms Kreps.RevealedPreference.RaisedBundle
#print axioms Kreps.RevealedPreference.raisedBundle_dist_le
#print axioms Kreps.RevealedPreference.strictlyMonotone_locallyInsatiable
#print axioms Kreps.RevealedPreference.Expenditure
#print axioms Kreps.RevealedPreference.Budget
#print axioms Kreps.RevealedPreference.MarketData
#print axioms Kreps.RevealedPreference.MarketData.mk
#print axioms Kreps.RevealedPreference.MarketData.price
#print axioms Kreps.RevealedPreference.MarketData.income
#print axioms Kreps.RevealedPreference.MarketData.bundle
#print axioms Kreps.RevealedPreference.MarketData.price_pos
#print axioms Kreps.RevealedPreference.MarketData.income_nonneg
#print axioms Kreps.RevealedPreference.MarketData.feasible
#print axioms Kreps.RevealedPreference.MarketData.cost
#print axioms Kreps.RevealedPreference.GARP
#print axioms Kreps.RevealedPreference.Rationalizes
#print axioms Kreps.RevealedPreference.expenditure_continuous
#print axioms Kreps.RevealedPreference.expenditure_orthant_continuous
#print axioms Kreps.RevealedPreference.strictBudget_isOpen
#print axioms Kreps.RevealedPreference.MarketData.cost_self_nonpos
#print axioms Kreps.RevealedPreference.garp_budget_exhaustion
#print axioms Kreps.RevealedPreference.garp_cost_eq_difference
#print axioms Kreps.RevealedPreference.constant_utility_rationalizes
#print axioms Kreps.RevealedPreference.lemma_4_1
#print axioms Kreps.RevealedPreference.optimal_budget_exhaustion
#print axioms Kreps.RevealedPreference.rationalizes_revealedWeak
#print axioms Kreps.RevealedPreference.rationalizes_revealedStrict
#print axioms Kreps.RevealedPreference.rationalizes_garp
#print axioms Kreps.RevealedPreference.matrixGARP_of_afriat
#print axioms Kreps.RevealedPreference.matrixGARP_iff_afriat
#print axioms Kreps.RevealedPreference.convexPreference_of_concaveOn
#print axioms Kreps.RevealedPreference.garp_exists_concave_utility
#print axioms Kreps.RevealedPreference.proposition_4_3
#print axioms Kreps.RevealedPreference.garp_iff_regular_rationalizable
#print axioms Kreps.RevealedPreference.OwnPriceIncrease
#print axioms Kreps.RevealedPreference.expenditure_own_price
#print axioms Kreps.RevealedPreference.compensated_old_expenditure
#print axioms Kreps.RevealedPreference.proposition_4_6
#print axioms Kreps.RevealedPreference.expenditure_price_quantity_difference
#print axioms Kreps.RevealedPreference.proposition_4_8
#print axioms Kreps.RevealedPreference.giffen_lower_income
#print axioms Kreps.RevealedPreference.giffen_lower_income_quantity
#print axioms Kreps.RevealedPreference.proposition_4_7
#print axioms Kreps.RevealedPreference.StrictlyConvexPreference
#print axioms Kreps.RevealedPreference.dominated_strict_ranking_not_monotone
#print axioms Kreps.RevealedPreference.midpoint_strict_rankings_not_convex
#print axioms Kreps.RevealedPreference.budget_mix
#print axioms Kreps.RevealedPreference.strictlyConvex_budget_choice_unique
#print axioms Kreps.RevealedPreference.unique_choice_strict
#print axioms Kreps.RevealedPreference.strictlyConvex_choice_strict
#print axioms Kreps.RevealedPreference.zero_income_bundle_zero
#print axioms Kreps.RevealedPreference.globally_inferior_demand_zero
#print axioms Kreps.RevealedPreference.GiffenUtility
#print axioms Kreps.RevealedPreference.GiffenPreference
#print axioms Kreps.RevealedPreference.GiffenOldPrices
#print axioms Kreps.RevealedPreference.GiffenNewPrices
#print axioms Kreps.RevealedPreference.GiffenOldBundle
#print axioms Kreps.RevealedPreference.GiffenNewBundle
#print axioms Kreps.RevealedPreference.giffenUtility_continuous
#print axioms Kreps.RevealedPreference.giffenUtility_concaveOn
#print axioms Kreps.RevealedPreference.giffenUtility_strictMono
#print axioms Kreps.RevealedPreference.giffenPreference_regular
#print axioms Kreps.RevealedPreference.giffenPrices_positive
#print axioms Kreps.RevealedPreference.giffenPrices_ownPriceIncrease
#print axioms Kreps.RevealedPreference.giffen_old_feasible
#print axioms Kreps.RevealedPreference.giffen_new_feasible
#print axioms Kreps.RevealedPreference.giffen_budget_exhaustion
#print axioms Kreps.RevealedPreference.giffen_old_value
#print axioms Kreps.RevealedPreference.giffen_new_value
#print axioms Kreps.RevealedPreference.giffen_old_maximum
#print axioms Kreps.RevealedPreference.giffen_old_unique
#print axioms Kreps.RevealedPreference.giffen_new_maximum
#print axioms Kreps.RevealedPreference.giffen_new_unique
#print axioms Kreps.RevealedPreference.giffen_old_choice
#print axioms Kreps.RevealedPreference.giffen_new_choice
#print axioms Kreps.RevealedPreference.problem_4_3
#print axioms Kreps.RevealedPreference.InitialBundles
#print axioms Kreps.RevealedPreference.InitialData
#print axioms Kreps.RevealedPreference.table_4_1_costs
#print axioms Kreps.RevealedPreference.initialData_exhausts
#print axioms Kreps.RevealedPreference.initialData_not_garp
#print axioms Kreps.RevealedPreference.initialData_not_rationalizable
#print axioms Kreps.RevealedPreference.ModifiedData
#print axioms Kreps.RevealedPreference.modifiedData_third_costs
#print axioms Kreps.RevealedPreference.modifiedData_garp
#print axioms Kreps.RevealedPreference.modifiedData_rationalizable
#print axioms Kreps.RevealedPreference.Problem41Data
#print axioms Kreps.RevealedPreference.table_4_2_costs
#print axioms Kreps.RevealedPreference.problem_4_1_garp
#print axioms Kreps.RevealedPreference.problem_4_1
#print axioms Kreps.RevealedPreference.ThousandPlateauUtility
#print axioms Kreps.RevealedPreference.thousandPlateauUtility_zero
#print axioms Kreps.RevealedPreference.thousandPlateauUtility_indifferent
#print axioms Kreps.RevealedPreference.affordable_coordinate_le_income
#print axioms Kreps.RevealedPreference.thousandPlateauUtility_rationalizes
#print axioms Kreps.RevealedPreference.thousandPlateauUtility_nonconstant
#print axioms Kreps.RevealedPreference.linear_boundary_tie
#print axioms Kreps.RevealedPreference.ownPriceData_cost
#print axioms Kreps.RevealedPreference.garp_of_own_price_data
#print axioms Kreps.RevealedPreference.own_price_data_rationalizable
#print axioms Kreps.RevealedPreference.garp_two_own_price_observations
#print axioms Kreps.RevealedPreference.BoundaryOwnPriceData
#print axioms Kreps.RevealedPreference.boundaryOwnPriceData_exhausts
#print axioms Kreps.RevealedPreference.boundaryOwnPriceData_price_increase
#print axioms Kreps.RevealedPreference.boundaryOwnPriceData_not_garp
#print axioms Kreps.RevealedPreference.DataEnvelope
#print axioms Kreps.RevealedPreference.dataEnvelope_at
#print axioms Kreps.RevealedPreference.dataEnvelope_rationalizes
#print axioms Kreps.RevealedPreference.ModifiedUtility
#print axioms Kreps.RevealedPreference.modified_multipliers_pos
#print axioms Kreps.RevealedPreference.modified_afriat
#print axioms Kreps.RevealedPreference.modifiedUtility_regular
#print axioms Kreps.RevealedPreference.modifiedUtility_rationalizes
#print axioms Kreps.RevealedPreference.modifiedUtility_values
#print axioms Kreps.RevealedPreference.modifiedUtility_strict_rankings
#print axioms Kreps.RevealedPreference.modifiedUtility_tied_rankings
