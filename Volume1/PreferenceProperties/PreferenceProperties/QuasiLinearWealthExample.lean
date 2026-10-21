/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.QuasiLinear

/-!
# The ten-dollar trade at two wealth levels

Kreps I, Section 2.6, p. 43. A consumer accepts exchanging goods `x` and ten
dollars for goods `x'` at zero money left over exactly when the same exchange
is acceptable at one hundred thousand dollars left over. Both comparisons are
conditional on preference: quasi-linearity does not assert that the trade is
accepted. All money amounts belong to the nonnegative domain.
-/

namespace Kreps.PreferenceProperties

open scoped NNReal

variable {X : Type*} {r : (X × ℝ≥0) → (X × ℝ≥0) → Prop}

/-- The exact p. 43 comparison follows from common-addition invariance alone. -/
theorem moneyTranslation_wealth_example (ht : MoneyTranslation r) (x x' : X) :
    r (x', 0) (x, 10) ↔ r (x', 100000) (x, 100010) := by
  convert ht x' x 0 10 100000 using 1
  norm_num

/-- Quasi-linear preferences preserve the book's ten-dollar trade at both wealth levels. -/
theorem quasiLinear_wealth_example (hq : QuasiLinear r) (x x' : X) :
    r (x', 0) (x, 10) ↔ r (x', 100000) (x, 100010) := by
  obtain ⟨u, hu⟩ := hq
  exact moneyTranslation_wealth_example (quasiLinear_moneyTranslation hu) x x'

end Kreps.PreferenceProperties
