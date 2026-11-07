/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.WeakSeparability
import PreferenceProperties.OrthantRepresentation
import PreferenceProperties.Rationalization

/-!
# Food rankings independent of clothing

Kreps I, Section 2.5, p. 39. Food coordinates are steaks, corn, potatoes and
lettuce, in that order. The printed alternatives are `(2,2,3,0)` and `(1,5,0,3)`.
Weak separability makes their comparison independent of clothing. The book's
ranking is conditional: no particular ranking is imposed on every consumer.

We encode the skirt and jeans contexts by `(1,0)` and `(0,1)` in a nonnegative
two-good clothing block. Those numeric clothing encodings are ours; the book
names the contexts without assigning coordinates. Food is the single selected
block and clothing is the leftover block in `WeaklySeparable`.

The final utility is a constructed witness, not a utility specified by Kreps.
It gives all six goods positive weights and satisfies the illustrated ranking.
-/

namespace Kreps.PreferenceProperties

/-- Four food quantities in one selected block, together with two clothing quantities. -/
abbrev FoodClothingBundle :=
  BlockBundle (fun _ : Fin 1 => NonnegativeOrthant 4) (NonnegativeOrthant 2)

/-- Combine a food bundle with its clothing context. -/
def FoodWithClothing (food : NonnegativeOrthant 4) (clothing : NonnegativeOrthant 2) :
    FoodClothingBundle := (fun _ => food, clothing)

/-- The first printed food bundle: two steaks, two corn, three potatoes and no lettuce. -/
def FirstFoodBundle : NonnegativeOrthant 4 :=
  ⟨![2, 2, 3, 0], by intro j; fin_cases j <;> norm_num⟩

/-- The second printed bundle: one steak, five corn, no potatoes and three kilograms of lettuce. -/
def SecondFoodBundle : NonnegativeOrthant 4 :=
  ⟨![1, 5, 0, 3], by intro j; fin_cases j <;> norm_num⟩

/-- Our nonnegative two-good encoding of wearing a skirt. -/
def SkirtContext : NonnegativeOrthant 2 :=
  ⟨![1, 0], by intro j; fin_cases j <;> norm_num⟩

/-- Our nonnegative two-good encoding of wearing jeans. -/
def JeansContext : NonnegativeOrthant 2 :=
  ⟨![0, 1], by intro j; fin_cases j <;> norm_num⟩

/-- Replacing the selected block replaces precisely the food and keeps the clothing. -/
theorem replaceFoodBlock (s : FoodClothingBundle) (food : NonnegativeOrthant 4) :
    ReplaceBlock s 0 food = FoodWithClothing food s.2 := by
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [ReplaceBlock, FoodWithClothing]
  · rfl

/-- Weak separability preserves any food comparison between arbitrary clothing contexts. -/
theorem foodClothing_comparison_iff {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) (a b : NonnegativeOrthant 4) (c d : NonnegativeOrthant 2) :
    r (FoodWithClothing a c) (FoodWithClothing b c) ↔
      r (FoodWithClothing a d) (FoodWithClothing b d) := by
  simpa only [replaceFoodBlock, FoodWithClothing] using
    hs 0 a b (FoodWithClothing a c) (FoodWithClothing a d)

/-- Strict food comparisons are also independent of the surrounding clothing quantities. -/
theorem foodClothing_strict_iff {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) (a b : NonnegativeOrthant 4) (c d : NonnegativeOrthant 2) :
    Strict r (FoodWithClothing a c) (FoodWithClothing b c) ↔
      Strict r (FoodWithClothing a d) (FoodWithClothing b d) := by
  simpa only [replaceFoodBlock, FoodWithClothing] using
    weaklySeparable_strict hs 0 a b (FoodWithClothing a c) (FoodWithClothing a d)

/-- The p. 39 food bundles have the same weak comparison in the skirt and jeans contexts. -/
theorem foodClothing_printed_comparison {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r) :
    r (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) ↔
    r (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  foodClothing_comparison_iff hs FirstFoodBundle SecondFoodBundle SkirtContext JeansContext

/-- If the first printed bundle is strictly preferred in a skirt, it is preferred in jeans. -/
theorem foodClothing_printed_strict {r : FoodClothingBundle → FoodClothingBundle → Prop}
    (hs : WeaklySeparable r)
    (hfood : Strict r (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext)) :
    Strict r (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  (foodClothing_strict_iff hs FirstFoodBundle SecondFoodBundle SkirtContext JeansContext).mp hfood

/-- A constructed additive witness: steaks have weight four and every other good weight one. -/
def FoodClothingWitnessUtility (x : FoodClothingBundle) : ℝ :=
  4 * (x.1 0).val 0 + (x.1 0).val 1 + (x.1 0).val 2 + (x.1 0).val 3 +
    x.2.val 0 + x.2.val 1

/-- The constructed utility satisfies food separability on the full nonnegative domain. -/
theorem foodClothingWitness_separable :
    WeaklySeparable (UtilityPref FoodClothingWitnessUtility) := by
  intro i a b s t
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [replaceFoodBlock, UtilityPref, FoodClothingWitnessUtility, FoodWithClothing]
  constructor <;> intro h <;> linarith

/-- The constructed witness ranks the first food bundle strictly above the second in a skirt. -/
theorem foodClothingWitness_initial_ranking :
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) := by
  norm_num [Strict, UtilityPref, FoodClothingWitnessUtility, FoodWithClothing,
    FirstFoodBundle, SecondFoodBundle, SkirtContext]

/-- A rational, separable preference realizes the book's conditional ranking in both contexts. -/
theorem foodClothingWitness_properties :
    Rational (UtilityPref FoodClothingWitnessUtility) ∧
    WeaklySeparable (UtilityPref FoodClothingWitnessUtility) ∧
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle SkirtContext)
      (FoodWithClothing SecondFoodBundle SkirtContext) ∧
    Strict (UtilityPref FoodClothingWitnessUtility)
      (FoodWithClothing FirstFoodBundle JeansContext)
      (FoodWithClothing SecondFoodBundle JeansContext) :=
  ⟨proposition_1_3a _, foodClothingWitness_separable, foodClothingWitness_initial_ranking,
    foodClothing_printed_strict foodClothingWitness_separable foodClothingWitness_initial_ranking⟩

end Kreps.PreferenceProperties
