/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommonActiveScoreInterval

/-!
# One local cardinal scale for every active pair

At each specified interior reference value, one compact common score interval
has one continuous strict cardinal scale. Every pair of active coordinates
uses that scale, and independence extends its comparisons to every context.
-/

namespace Kreps.PreferenceProperties

variable {I : Type*} [DecidableEq I] {S : I → Set ℝ}

/-- A common normalized local scale represents all active pairs in all contexts. -/
def HasAllPairsLocalScale (V : (∀ i, S i) → ℝ) (z : ∀ i, S i) (T : Set I) (c : ℝ) : Prop :=
  ∃ (a b : ℝ) (hab : a < b) (hsub : ∀ i ∈ T, Set.Icc a b ⊆ S i)
    (φ : Set.Icc a b → ℝ), a < c ∧ c < b ∧ Continuous φ ∧ StrictMono φ ∧
      φ ⟨a, le_rfl, hab.le⟩ = 0 ∧ φ ⟨b, hab.le, le_rfl⟩ = 1 ∧
      ∀ (t : ∀ i, S i) (i : I), i ∈ T → ∀ j, j ∈ T → i ≠ j →
        ∀ x y x' y' : Set.Icc a b,
          CoordinatePairUtility V t (CommonActiveScoreEmbedding z T hsub) i j x y ≤
            CoordinatePairUtility V t (CommonActiveScoreEmbedding z T hsub) i j x' y' ↔
            φ x + φ y ≤ φ x' + φ y'

/-- Every specified interior reference admits one cardinal chart for all active coordinate pairs. -/
theorem exists_all_pairs_local_scale [Finite I] {V : (∀ i, S i) → ℝ}
    (hs : StronglySeparable (UtilityPref V)) (hm : StrictMono V) (hc : Continuous V)
    (z : ∀ i, S i) (hv : ∀ i (q : S i), V (Function.update z i q) = q.val)
    {T : Set I} {c : ℝ} (hz : ∀ i, (z i).val = c)
    (hint : ∀ i ∈ T, c ∈ interior (S i))
    (ht : ∃ p ∈ T, ∃ q ∈ T, ∃ l ∈ T, p ≠ q ∧ p ≠ l ∧ q ≠ l) :
    HasAllPairsLocalScale V z T c := by
  obtain ⟨p, hp, q, hq, l, hl, hpq, hpl, hql⟩ := ht
  obtain ⟨L, R, hcLR, hJ⟩ := exists_all_active_score_interval hint
  let e : Set.Ioo L R := ⟨c, hcLR⟩
  let v := CommonThreeScoreUtility V z p q l (hJ p hp) (hJ q hq) (hJ l hl)
  have hvc : Continuous v := commonThreeScoreUtility_continuous hc z p q l _ _ _
  have hvi : ThreeFactorIndependent (UtilityPref v) :=
    commonThreeScoreUtility_independent hs z hpq hpl hql _ _ _
  have hvn : NormalizedThreeAxes v Subtype.val e :=
    commonThreeScoreUtility_axes z hv hpq hpl hql _ _ _ e hz
  have hvl : ∀ y, StrictMono (fun x => v (x, y, e)) :=
    fun y => commonThreeScoreUtility_first_strictMono hm z hpq hpl _ _ _ y e
  have hvr : ∀ x, StrictMono (fun y => v (x, y, e)) :=
    fun x => commonThreeScoreUtility_second_strictMono hm z hql _ _ _ x e
  obtain ⟨a, b, hab, habJ, φ, hae, heb, hφc, hφm, hφa, hφb, hφpair⟩ :=
    normalizedThreeAxes_local_pair_scale isOpen_Ioo hvc hvi hvn hvl hvr
  have hsub : ∀ i ∈ T, Set.Icc a b ⊆ S i := fun i hi => (habJ.trans (hJ i hi))
  let k := CommonActiveScoreEmbedding z T hsub
  have hpair (x y : Set.Icc a b) : CoordinatePairUtility V z k p q x y =
      v (Set.inclusion habJ x, Set.inclusion habJ y, e) := by
    have hkp : k p x = Set.inclusion (hJ p hp) (Set.inclusion habJ x) := by
      exact commonActiveScoreEmbedding_active z T hsub hp x
    have hkq : k q y = Set.inclusion (hJ q hq) (Set.inclusion habJ y) := by
      exact commonActiveScoreEmbedding_active z T hsub hq y
    have hel : Set.inclusion (hJ l hl) e = z l := Subtype.ext (hz l).symm
    change V (Function.update (Function.update z p (k p x)) q (k q y)) =
      V (ThreeCoordinateBundle z p q l _ _ _)
    rw [hkp, hkq]
    unfold ThreeCoordinateBundle
    rw [hel]
    have heval :
        Function.update (Function.update z p (Set.inclusion (hJ p hp) (Set.inclusion habJ x)))
          q (Set.inclusion (hJ q hq) (Set.inclusion habJ y)) l = z l := by
      simp only [Function.update_of_ne hql.symm, Function.update_of_ne hpl.symm]
    rw [← heval, Function.update_eq_self]
  have hanchor : ∀ x y x' y', CoordinatePairUtility V z k p q x y ≤
      CoordinatePairUtility V z k p q x' y' ↔ φ x + φ y ≤ φ x' + φ y' := by
    intro x y x' y'
    rw [hpair, hpair]
    exact hφpair x y x' y'
  refine ⟨a, b, hab, hsub, φ, hae, heb, hφc, hφm, hφa, hφb, ?_⟩
  intro t i hi j hj hij x y x' y'
  exact coordinatePairUtility_all_comparisons hs z k
    (commonActiveScoreEmbedding_axes z hv T hsub)
    ⟨p, hp, q, hq, l, hl, hpq, hpl, hql⟩ hp hq hpq hanchor t hi hj hij x y x' y'

end Kreps.PreferenceProperties
