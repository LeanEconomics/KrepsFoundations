# Corrections and conventions

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Section 2.6, p. 44, compensating-money sentence | The final indifference uses the original goods bundle `x` again on its right side, although the preceding sentence changes consumption to `x′`. | Use `(x,m) ~ (x′,m′ + compensation)` in `quasiLinear_compensation`, with an explicit nonnegative adjusted balance. `quasiLinear_compensation_of_preferred` proves feasibility when the original bundle is weakly preferred; `printed_compensation_bundle_counterexample` refutes the printed goods substitution. The formula was checked in the page image. |

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
| Proposition 2.9; Problem 2.14 | The full continuous-representation theorem, with a particular recursive construction assigned as an exercise. | `proposition_2_9` proves the full theorem through Cantor's order isomorphism on countable interior ranks and their rational-cut completion. The proof handles constant preferences and attained/unattained extrema. This does not claim completion of Problem 2.14's specified algorithm. |
| Quasi-linearity, pp. 43-44 | Write goods and money as `(x,m)` with nonnegative money. | Use `X × NNReal`, where `X` can be the nonnegative orthant of the other goods. The characterization holds for any nonempty `X`; no topology or monotonicity of the other goods is assumed. Common-addition invariance holds for each nonnegative addition. |
| Disjoint commodity blocks, pp. 40-42 | Selected subsets `J₁,...,Jₙ` may leave goods outside their union. Strong separability uses a full partition. | An assignment sends each commodity to a selected block or the leftover class. `exists_commodity_assignment` proves this covers every disjoint family; `orthantGrouping` and the replacement lemmas verify the exact coordinate interpretation. The aggregator is defined on attained ranges and is strictly monotone in their product order, holding leftovers fixed. Strong separability uses every finite union in a full product of blocks. |
