/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import PreferenceProperties.CommodityBlocks

/-!
# The beer, wine and bread projection

Kreps I, p. 40. The full bundle consists of four beers, three wines and five loaves
of bread. Selecting commodities `{1,3}` gives the beer-and-bread sub-bundle `(4,5)`;
the complementary wine quantity is three. The book uses one-based commodity names.
Here `Fin 3` uses zero-based coordinates, so the selected set is `{0,2}` and wine
has coordinate one. The example uses the chapter's actual `orthantGrouping`
equivalence, including its leftover block and reconstruction of the original bundle.
-/

namespace Kreps.PreferenceProperties

/-- The full printed bundle `(4,3,5)`, in beer, wine and bread order. -/
def BeerWineBreadBundle : NonnegativeOrthant 3 :=
  ⟨![4, 3, 5], by intro j; fin_cases j <;> norm_num⟩

/-- Assign beer and bread to block zero, leaving wine outside the selected block. -/
def BeerBreadOwner (j : Fin 3) : Option (Fin 1) := if j = 1 then none else some 0

/-- The selected coordinates are exactly `{0,2}`, the printed commodity names `{1,3}`. -/
theorem beerBreadOwner_selected :
    {j | BeerBreadOwner j = some 0} = ({0, 2} : Set (Fin 3)) := by
  ext j
  fin_cases j <;> norm_num [BeerBreadOwner]

/-- The complementary commodity is exactly wine, with zero-based coordinate one. -/
theorem beerBreadOwner_leftover :
    {j | BeerBreadOwner j = none} = ({1} : Set (Fin 3)) := by
  ext j
  fin_cases j <;> norm_num [BeerBreadOwner]

/-- Reading beer and bread from the actual selected block gives the printed pair `(4,5)`. -/
theorem beerWineBread_projection :
    (((orthantGrouping BeerBreadOwner BeerWineBreadBundle).1 0
        ⟨0, by norm_num [BeerBreadOwner]⟩ : ℝ),
      ((orthantGrouping BeerBreadOwner BeerWineBreadBundle).1 0
        ⟨2, by norm_num [BeerBreadOwner]⟩ : ℝ)) = (4, 5) := by
  rfl

/-- Reading the actual leftover block gives the original wine quantity, three. -/
theorem beerWineBread_leftover :
    ((orthantGrouping BeerBreadOwner BeerWineBreadBundle).2
      ⟨1, by norm_num [BeerBreadOwner]⟩ : ℝ) = 3 := by
  rfl

/-- The selected sub-bundle and its complement reconstruct the complete printed bundle. -/
theorem beerWineBread_reconstruction :
    (orthantGrouping BeerBreadOwner).symm
      (orthantGrouping BeerBreadOwner BeerWineBreadBundle) = BeerWineBreadBundle :=
  (orthantGrouping BeerBreadOwner).symm_apply_apply BeerWineBreadBundle

end Kreps.PreferenceProperties
