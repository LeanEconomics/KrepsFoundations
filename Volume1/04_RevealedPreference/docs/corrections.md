# Chapter 4 corrections and explicit conventions

## Page 75: positive own consumption in the finite claim

The preceding two-observation discussion assumes positive old consumption of the
changing-price good. The later finite-sequence assertion omits this condition.
Its printed hypotheses are insufficient on the nonnegative orthant.

Both observations below have income `1`:

| Observation | Prices | Bundle | Expenditure |
| --- | --- | --- | --- |
| Old | `(1,1)` | `(0,1)` | `1` |
| New | `(2,1)` | `(1/4,1/2)` | `1` |

At old prices the new bundle costs `3/4`, giving a strict old-to-new edge. At new
prices the old bundle still costs `1`, giving a weak return edge. Hence GARP fails.
[`boundaryOwnPriceData_not_garp`](../RevealedPreference/OwnPriceData.lean) proves
this, with exhaustion and the sole own-price increase separately checked.
`garp_of_own_price_data` proves the corrected finite assertion when every observed
own-good quantity is positive. `garp_two_own_price_observations` retains the
source's preceding two-observation claim with only the old quantity positive.

## Dimension and empty datasets

The book works with a positive commodity dimension. `proposition_4_3` makes
`0 < k` explicit because the zero-dimensional orthant is a singleton and cannot
have locally insatiable preferences. The numerical utility construction does not
need that condition. Empty data use an increasing affine utility rather than an
empty minimum. These explicit conventions do not alter the source conclusion.

## Inequality transcription

The PDF determines equality strokes lost in OCR. Proposition 4.6 concludes a weak
decrease; Proposition 4.8 has a nonpositive dot product. The source's WARP passage
distinguishes boundary affordability from strict slack. These are transcription
checks, not mathematical corrections.

## Conditional existence in Proposition 4.7

The source permits a conditional lower-income conclusion when continuity is not
assumed. `proposition_4_7` therefore takes the lower-income maximizer as a choice
premise. It adds neither continuity nor an unsupported attainment assertion.
