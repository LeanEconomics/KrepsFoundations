/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.RepresentationDensePreferenceRanks

/-!
Local prerequisite copy from Chapter 2, commit `7d496c5`.
Only project imports and namespace are changed; proofs are preserved.

# A bounded utility from dense rational ranks

The construction supporting the general Proposition 2.9 assigns each bundle
the supremum of its lower rational ranks. Adding zero makes every cut nonempty;
the rational scale lies in (0,1), so all cuts are bounded, even at extreme ranks.
-/

namespace Kreps.ConsumerDemand.Representation

variable {X : Type*} {v : X → ℝ} {D : Set X}

/-- A countable interior rank's rational value, viewed as a real number. -/
def RationalRankValue (e : InteriorRankSet v D ≃o RationalUnit)
    (a : InteriorRankSet v D) : ℝ := (e a).val

/-- All rational ranks are strictly between zero and one. -/
theorem rationalRankValue_bounds (e : InteriorRankSet v D ≃o RationalUnit)
    (a : InteriorRankSet v D) : 0 < RationalRankValue e a ∧ RationalRankValue e a < 1 := by
  have h := (e a).property
  change 0 < ((e a).val : ℝ) ∧ ((e a).val : ℝ) < 1
  exact_mod_cast h

/-- The real-valued rank scale preserves every strict comparison. -/
theorem rationalRankValue_strictMono (e : InteriorRankSet v D ≃o RationalUnit) :
    StrictMono (RationalRankValue e) := by
  intro a b hab
  have hq : (e a).val < (e b).val := e.strictMono hab
  change ((e a).val : ℝ) < ((e b).val : ℝ)
  exact_mod_cast hq

/-- A lower cut, with zero included to cover a possible worst bundle. -/
def RankCutSet (e : InteriorRankSet v D ≃o RationalUnit) (x : X) : Set ℝ :=
  {t | t = 0 ∨ ∃ a : InteriorRankSet v D, t = RationalRankValue e a ∧ a.val ≤ v x}

/-- Every lower cut contains zero. -/
theorem rankCutSet_nonempty (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    (RankCutSet e x).Nonempty := ⟨0, Or.inl rfl⟩

/-- One bounds every lower cut, whether or not a best bundle exists. -/
theorem rankCutSet_bddAbove (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    BddAbove (RankCutSet e x) := by
  refine ⟨1, ?_⟩
  intro t ht
  rcases ht with rfl | ⟨a, rfl, _⟩
  · exact zero_le_one
  · exact (rationalRankValue_bounds e a).2.le

/-- The supremum of the lower rational ranks is the new utility scale. -/
noncomputable def RankCutUtility (e : InteriorRankSet v D ≃o RationalUnit) (x : X) : ℝ :=
  sSup (RankCutSet e x)

/-- The completed scale never falls below zero. -/
theorem rankCutUtility_nonneg (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    0 ≤ RankCutUtility e x :=
  le_csSup (rankCutSet_bddAbove e x) (Or.inl rfl)

/-- The completed scale never exceeds one. -/
theorem rankCutUtility_le_one (e : InteriorRankSet v D ≃o RationalUnit) (x : X) :
    RankCutUtility e x ≤ 1 := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  rcases ht with rfl | ⟨a, rfl, _⟩
  · exact zero_le_one
  · exact (rationalRankValue_bounds e a).2.le

/-- Larger original utility gives a larger lower cut. -/
theorem rankCutUtility_mono (e : InteriorRankSet v D ≃o RationalUnit) {x y : X}
    (hxy : v x ≤ v y) : RankCutUtility e x ≤ RankCutUtility e y := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  apply le_csSup (rankCutSet_bddAbove e y)
  rcases ht with h0 | ⟨a, ha, hax⟩
  · exact Or.inl h0
  · exact Or.inr ⟨a, ha, hax.trans hxy⟩

/-- An upper rational rank bounds the completed utility from above. -/
theorem rankCutUtility_upper (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : v x ≤ a.val) :
    RankCutUtility e x ≤ RationalRankValue e a := by
  apply csSup_le (rankCutSet_nonempty e x)
  intro t ht
  rcases ht with rfl | ⟨b, rfl, hbx⟩
  · exact (rationalRankValue_bounds e a).1.le
  · exact (rationalRankValue_strictMono e).monotone (hbx.trans hx)

/-- A lower rational rank bounds the completed utility from below. -/
theorem rankCutUtility_lower (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : a.val ≤ v x) :
    RationalRankValue e a ≤ RankCutUtility e x :=
  le_csSup (rankCutSet_bddAbove e x) (Or.inr ⟨a, rfl, hx⟩)

/-- The extension agrees exactly with every prescribed rational rank. -/
theorem rankCutUtility_at_rank (e : InteriorRankSet v D ≃o RationalUnit)
    {x : X} {a : InteriorRankSet v D} (hx : v x = a.val) :
    RankCutUtility e x = RationalRankValue e a :=
  le_antisymm (rankCutUtility_upper e hx.le) (rankCutUtility_lower e hx.ge)

/-- Two interior ranks between distinct preferences force a strict utility inequality. -/
theorem rankCutUtility_strict (e : InteriorRankSet v D ≃o RationalUnit)
    (hs : StrictRankSeparator v D) {x y : X} (hxy : v x < v y) :
    RankCutUtility e x < RankCutUtility e y := by
  obtain ⟨a, hxa, hay⟩ := interiorRank_between hs hxy
  obtain ⟨z, hz⟩ := interiorRank_witness a
  have hzy : v z < v y := by rw [hz]; exact hay
  obtain ⟨b, hzb, hby⟩ := interiorRank_between hs hzy
  have hab : a < b := by
    change a.val < b.val
    rwa [hz] at hzb
  exact (rankCutUtility_upper e hxa.le).trans_lt
    ((rationalRankValue_strictMono e hab).trans_le (rankCutUtility_lower e hby.le))

/-- Completing the rational scale preserves the original preference representation. -/
theorem rankCutUtility_represents (e : InteriorRankSet v D ≃o RationalUnit)
    (hs : StrictRankSeparator v D) {r : X → X → Prop} (hv : Represents v r) :
    Represents (RankCutUtility e) r := by
  intro x y
  constructor
  · intro hxy
    exact rankCutUtility_mono e ((hv x y).mp hxy)
  · intro hxy
    by_contra hn
    have hlt : v x < v y := lt_of_not_ge (fun h => hn ((hv x y).mpr h))
    exact (not_lt_of_ge hxy) (rankCutUtility_strict e hs hlt)

/-- Every rational point strictly between zero and one is attained by the new utility. -/
theorem rankCutUtility_attains_rationals (e : InteriorRankSet v D ≃o RationalUnit)
    (q : RationalUnit) : ∃ x, RankCutUtility e x = (q.val : ℝ) := by
  let a := e.symm q
  obtain ⟨x, hx⟩ := interiorRank_witness a
  refine ⟨x, ?_⟩
  calc
    RankCutUtility e x = RationalRankValue e a := rankCutUtility_at_rank e hx
    _ = (q.val : ℝ) := by simp [RationalRankValue, a]

end Kreps.ConsumerDemand.Representation
