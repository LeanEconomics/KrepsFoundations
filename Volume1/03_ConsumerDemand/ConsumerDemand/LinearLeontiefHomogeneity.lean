/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.LinearDemand
import ConsumerDemand.LeontiefDemand
import ConsumerDemand.HomotheticDemand

/-!
# Homotheticity of linear and Leontief utility

Kreps I, Problems 3.6 and 3.10(a), pp. 64-65. Both utility specifications
are homogeneous of degree one on the full nonnegative orthant. The proofs
include zero scaling and do not impose uniqueness on linear demand.
-/

namespace Kreps.ConsumerDemand

open scoped BigOperators NNReal

/-- Linear utility is homogeneous of degree one, even without coefficient restrictions. -/
theorem linearUtility_scale {k : ℕ} (a : Fin k → ℝ) (t : ℝ≥0)
    (x : NonnegativeOrthant k) :
    LinearUtility a (ScaleBundle t x) = (t : ℝ) * LinearUtility a x := by
  simp only [LinearUtility, ScaleBundle, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Problem 3.10(a), linear case:** linear utility represents homothetic preference. -/
theorem linearUtility_homothetic {k : ℕ} (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (LinearUtility a)) :=
  homothetic_of_homogeneous (linearUtility_scale a)

/-- A common nonnegative scale factors out of the finite Leontief minimum. -/
theorem leontiefUtility_scale {k : ℕ} [NeZero k] (a : Fin k → ℝ) (t : ℝ≥0)
    (x : NonnegativeOrthant k) :
    LeontiefUtility a (ScaleBundle t x) = (t : ℝ) * LeontiefUtility a x := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin k => a j * x.val j)
  change LeontiefUtility a x = a j * x.val j at hj
  apply le_antisymm
  · calc
      LeontiefUtility a (ScaleBundle t x) ≤ a j * (ScaleBundle t x).val j :=
        leontiefUtility_le a _ j
      _ = (t : ℝ) * LeontiefUtility a x := by rw [hj]; simp only [ScaleBundle]; ring
  · apply le_leontiefUtility
    intro i
    have hi := mul_le_mul_of_nonneg_left (leontiefUtility_le a x i) t.property
    change (t : ℝ) * LeontiefUtility a x ≤ a i * ((t : ℝ) * x.val i)
    calc
      _ ≤ (t : ℝ) * (a i * x.val i) := hi
      _ = _ := by ring

/-- **Problem 3.10(a), Leontief case:** fixed-proportion utility is homothetic. -/
theorem leontiefUtility_homothetic {k : ℕ} [NeZero k] (a : Fin k → ℝ) :
    HomotheticPreference (UtilityPref (LeontiefUtility a)) :=
  homothetic_of_homogeneous (leontiefUtility_scale a)

end Kreps.ConsumerDemand
