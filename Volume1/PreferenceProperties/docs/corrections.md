# Corrections and conventions

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Section 2.6, p. 44, compensating-money sentence | The final indifference uses the original goods bundle `x` again on its right side, although the preceding sentence changes consumption to `x′`. | Use `(x,m) ~ (x′,m′ + compensation)`. The printed formula was checked in the page image. Nonnegative money also requires the adjusted money to remain feasible; this is automatic when the original bundle is weakly preferred, and will be explicit in the general statement. Formal treatment pending. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Chapter 2 standing domain, p. 30 | The nonnegative finite-dimensional orthant; rational preferences throughout. | `NonnegativeOrthant k` and explicit `Rational` hypotheses. State positive-dimension hypotheses when a result needs them. The finite-product metric is the equivalent norm convention used in Chapter 1. |
| Definition 2.1 and p. 32 | Strict monotonicity allows an increase in just one coordinate; the intermediate property requires all coordinates to increase. | Distinct predicates `StrictlyMonotonePreference` and `StrictAllIncreasePreference`. |
| Definition 2.3b, p. 32 | Improvement at distance no more than epsilon. | `LocallyInsatiable` uses `≤`; `locallyInsatiable_iff_open` proves the equivalent open-ball form. |
| Minimum and Cobb-Douglas examples, p. 32 | These preferences need not be strictly monotone on the whole orthant. | Boundary failures need at least two goods; in one dimension the stated strictly increasing component functions are strictly monotone. General and counterexample dimensions will be explicit. |
| Problem 2.1, Table 2.1, p. 45 | The strictly-convex-to-strictly-concave cell is marked ???? and explicitly excluded. | No theorem is asserted for that cell. The additive-existence row retains continuity and at least three nontrivial blocks from Proposition 2.14. |
| Problem 2.14, p. 49 | The recursive assignment describes later comparisons but does not specify an initial value. | Set the first utility value to zero; only ordinal comparisons matter. The below-all case is minimum minus one, as confirmed in the image, not the OCR's spurious extra minus sign. |
| Convexity, pp. 33-34; one-good examples, p. 46 | Convex combinations inside a convex consumption domain; the one-good domain is the nonnegative half-line. | Convexity results are generalized to a convex subtype of any real vector space. `convexMenu_iff` and the three function-shape bridges identify the definitions with Mathlib. `OneGood` is the scalar nonnegative half-line, the book's one-good orthant. |
