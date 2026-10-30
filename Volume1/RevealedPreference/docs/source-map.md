# Chapter 4 source map

Source: David M. Kreps, *Microeconomic Foundations I*, Chapter 4, pp. 67-78.
These results concern arbitrary finite observation families and entire nonnegative
budget sets. Original-income GARP does not assume budget exhaustion. See the
[construction guide](afriat-construction.md) for the proof chain and
[corrections](corrections.md) for the p. 75 boundary issue. The full build, frozen
fresh elaboration and all-declaration transitive-axiom audit passed; the generated
record is in [verification](../verification/verification.json).

## Definitions and numbered results

| Source | Lean interface | Scope |
| --- | --- | --- |
| Observations, pp. 67-70 | [`MarketData`, `Budget`, `Rationalizes`](../RevealedPreference/MarketData.lean) | Nonnegative bundles, positive prices, nonnegative incomes and feasibility. Full budget sets and repeated observed bundles are allowed. |
| Lemma 4.1, p. 68 | [`lemma_4_1`, `optimal_budget_exhaustion`](../RevealedPreference/GarpNecessity.lean) | Rational locally insatiable maximization strictly dominates every strictly affordable bundle and exhausts income. No utility or continuity assumption. |
| Definition 4.2a-b, p. 70 | [`DirectWeak`, `DirectStrict`, `RevealedWeak`, `RevealedStrict`](../RevealedPreference/RevealedChains.lean) | Arbitrary finite weak chains with a strict edge anywhere in a strict chain. Empty weak chains add nothing on feasible data. |
| Definition 4.2c, p. 70 | [`MatrixGARP`, `matrixGARP_iff_return_cost`](../RevealedPreference/RevealedChains.lean), [`GARP`](../RevealedPreference/MarketData.lean) | No strict revealed cycle; equivalent closing-edge criterion. The cost matrix retains original incomes, including possible slack. |
| Proposition 4.3 necessity, pp. 70-71 | [`rationalizes_garp`](../RevealedPreference/GarpNecessity.lean) | Primitive rationality and local insatiability exclude all strict cycles. |
| Proposition 4.3 equivalence, pp. 70-73 | [`proposition_4_3`, `garp_exists_concave_utility`, `garp_iff_regular_rationalizable`](../RevealedPreference/AfriatTheorem.lean) | Actual continuous strictly increasing concave utility on all real vectors; continuous strictly monotone convex rational preference on the full orthant. Positive dimension is explicit for local insatiability. Empty data are included. |
| Lemma 4.4a-c, p. 72 | [`RevealedRank`, `lemma_4_4a`, `lemma_4_4b`, `lemma_4_4c`](../RevealedPreference/RevealedRanks.lean) | Rank is the cardinality of strict successors. Both cost comparisons and existence of rank zero are proved. |
| Lemma 4.5 / (4.1), pp. 72-73 | [`afriat_of_rank_on_finset`, `lemma_4_5`](../RevealedPreference/AfriatRankInduction.lean) | Lowest-rank-class induction, the source's cross-class minimum, and positive multipliers. Solvability is derived from GARP. |
| Envelope construction, p. 73 | [`FiniteAffineEnvelope`, `finiteAffineEnvelope_at_anchor`, `finiteAffineEnvelope_maximizes`](../RevealedPreference/FiniteAffineEnvelope.lean) | Exact interpolation and maximization over entire budget half-spaces, using coefficients constructed by Lemma 4.5. |
| Proposition 4.6, p. 76 | [`proposition_4_6`](../RevealedPreference/ComparativeStatics.lean) | Compensated own-price effect is weakly nonpositive, without smoothness or uniqueness. |
| Proposition 4.7, p. 76 | [`proposition_4_7`, `giffen_lower_income_quantity`](../RevealedPreference/ComparativeStatics.lean) | Strictly lower original-price income and strict inferior-good comparison. Lower-income maximization is conditional, as permitted by the source. |
| Proposition 4.8, p. 77 | [`proposition_4_8`](../RevealedPreference/ComparativeStatics.lean) | Any compensated price-change/quantity-change dot product is nonpositive. |

## Examples and mathematical commentary

| Source | Lean interface | Scope |
| --- | --- | --- |
| Original data / Table 4.1, pp. 67-69 | [`InitialData`, `table_4_1_costs`, `initialData_exhausts`, `initialData_not_garp`, `initialData_not_rationalizable`](../RevealedPreference/MarketExamples.lean) | Exact bundles, prices, incomes and nine expenditures; explicit strict cycle and primitive nonexistence. |
| Complete indifference, p. 68 | [`constant_utility_rationalizes`](../RevealedPreference/MarketData.lean) | Every feasible dataset has a constant-utility rationalizer. |
| Indifference below 1000, p. 68 | [`ThousandPlateauUtility`, `thousandPlateauUtility_indifferent`, `thousandPlateauUtility_rationalizes`, `thousandPlateauUtility_nonconstant`](../RevealedPreference/InsatiabilityExamples.lean) | Nonconstant utility flat throughout the printed box, rationalizing the full original budgets. Formula is a constructed witness, not attributed to the source. |
| Modified third observation, p. 69 | [`ModifiedData`, `modifiedData_third_costs`, `modifiedData_garp`, `modifiedData_rationalizable`](../RevealedPreference/MarketExamples.lean) | Exact third prices `(1,2,10)`, income `115`, costs `130,134,115`, and full-domain regular rationalization. |
| Both permitted observed rankings, p. 69 | [`ModifiedUtility`, `modifiedUtility_strict_rankings`, `modifiedUtility_tied_rankings`, `modifiedUtility_rationalizes`](../RevealedPreference/PrescribedUtilities.lean) | Explicit regular full-domain utilities realize strict ranking or indifference between the first two bundles, both above the third. |
| Direct rankings, p. 71 | [`dominated_strict_ranking_not_monotone`, `midpoint_strict_rankings_not_convex`](../RevealedPreference/EconomicCommentary.lean) | Direct elicitation can reject monotonicity or convexity despite finite market data admitting regular rationalizers. |
| Source's WARP discussion, pp. 73-74 | [`unique_choice_strict`, `strictlyConvex_budget_choice_unique`, `strictlyConvex_choice_strict`](../RevealedPreference/EconomicCommentary.lean) | Unique maxima imply strict comparison against distinct boundary bundles; strict convexity implies uniqueness. |
| Boundary ties, pp. 73-74 | [`linear_boundary_tie`](../RevealedPreference/InsatiabilityExamples.lean) | Rational locally insatiable preference can have distinct tied budget maximizers. |
| Zero income / always inferior, p. 74 | [`zero_income_bundle_zero`, `globally_inferior_demand_zero`](../RevealedPreference/EconomicCommentary.lean) | Positive prices force zero demand at zero income; a globally nonincreasing nonnegative demand coordinate vanishes everywhere. |
| Two observations, p. 75 | [`garp_two_own_price_observations`](../RevealedPreference/OwnPriceData.lean) | Only the old own-good quantity must be positive; the new quantity may be zero or move in either direction. |
| Finite own-price claim, p. 75 | [`garp_of_own_price_data`, `own_price_data_rationalizable`](../RevealedPreference/OwnPriceData.lean) | Corrected positive-quantity assertion, common income and fixed other prices. Arbitrary own prices include increasing sequences. |
| Boundary correction, p. 75 | [`BoundaryOwnPriceData`, `boundaryOwnPriceData_exhausts`, `boundaryOwnPriceData_price_increase`, `boundaryOwnPriceData_not_garp`](../RevealedPreference/OwnPriceData.lean) | Exact counterexample to the printed unrestricted finite claim. |

Public transport, taxicabs, skiing, nails/lumber and corn/wheat on p. 74 are verbal
illustrations, not numerical datasets or universal assertions about actual
consumers. The inferiority implication for Giffen goods is Proposition 4.7 above.

## Problems

| Problem, p. 78 | Lean interface | Scope |
| --- | --- | --- |
| 4.1 | [`Problem41Data`, `table_4_2_costs`, `problem_4_1_garp`, `problem_4_1`](../RevealedPreference/MarketExamples.lean) | Exact four observations and 16 expenditures; GARP and the full regular consumer model. |
| 4.2, minimum properties | [`finiteMinimum_continuous`, `finiteMinimum_strictMono`, `finiteMinimum_concaveOn`](../RevealedPreference/FiniteMinimum.lean) | Arbitrary nonempty finite families, preordered domains for strict increase, and common convex domains for concavity. |
| 4.2, induction case | [`afriat_all_minimal`](../RevealedPreference/AfriatRankInduction.lean) | Zero values and unit multipliers solve the all-minimal case, actually invoked in the construction. |
| 4.3 | [`problem_4_3`](../RevealedPreference/GiffenExample.lean), [diagram](assets/giffen-example.svg) | Constructed continuous increasing concave utility, unique choices `(1,9)` and `(2,6)`, income `10`, prices `(1,1)` and `(2,1)`, reproducible indifference curves. |
| 4.4 | [`proposition_4_8`](../RevealedPreference/ComparativeStatics.lean) | General compensated dot-product inequality. |

## Independent prerequisites

`Basic.lean` and `PreferenceProperties.lean` select local Chapter 2 definitions and
elementary bridges, originating at `7d496c5`. `EconomicCommentary.lean` copies the
strict-convexity definition. No other chapter's Lake package is imported. See
[THIRD_PARTY_NOTICES](../THIRD_PARTY_NOTICES.md) for the precise source inventory.
