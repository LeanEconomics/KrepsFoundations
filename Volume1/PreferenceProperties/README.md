# Kreps Chapter 2: Structural Properties of Preferences and Utility Functions, in Lean

This is the `Volume1/PreferenceProperties` proof project in Kreps Foundations.
It follows Chapter 2, pp. 30-49, including Problems 2.1-2.15.
[Return to the library index](../../README.md).

Status: in progress. The [source map](docs/source-map.md) inventories every proposition,
problem and mathematical example; [corrections](docs/corrections.md) records statement
changes. Declarations use `Kreps.PreferenceProperties`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](PreferenceProperties/Basic.lean) | 5 | Locally copied Chapter 1 prerequisite |
| [Rationalization](PreferenceProperties/Rationalization.lean) | 12 | Locally copied Chapter 1 prerequisite |
| [FiniteUtility](PreferenceProperties/FiniteUtility.lean) | 10 | Locally copied Chapter 1 prerequisite |
| [StrictPreference](PreferenceProperties/StrictPreference.lean) | 12 | Locally copied Chapter 1 prerequisite |
| [CountableUtility](PreferenceProperties/CountableUtility.lean) | 10 | Locally copied Chapter 1 prerequisite |
| [InfiniteChoice](PreferenceProperties/InfiniteChoice.lean) | 6 | Locally copied Chapter 1 prerequisite |
| [UtilityEquivalence](PreferenceProperties/UtilityEquivalence.lean) | 13 | Locally copied Chapter 1 prerequisite |
| [ContinuousPreference](PreferenceProperties/ContinuousPreference.lean) | 10 | Locally copied Chapter 1 prerequisite |
| [OrthantRepresentation](PreferenceProperties/OrthantRepresentation.lean) | 5 | Locally copied Chapter 1 prerequisite |
| [CompactChoice](PreferenceProperties/CompactChoice.lean) | 3 | Locally copied Chapter 1 prerequisite |
| [UtilityExamples](PreferenceProperties/UtilityExamples.lean) | 9 | Locally copied Chapter 1 prerequisite |
| [Lexicographic](PreferenceProperties/Lexicographic.lean) | 3 | Locally copied Chapter 1 prerequisite |
| [Monotonicity](PreferenceProperties/Monotonicity.lean) | 17 | Definitions 2.1/2.3, Proposition 2.2 and positive implications in Problem 2.6 |
| [ConvexPreference](PreferenceProperties/ConvexPreference.lean) | 12 | Definition 2.4, Propositions 2.5-2.6 and Problem 2.4 |
| [ConcaveUtility](PreferenceProperties/ConcaveUtility.lean) | 12 | Definition 2.7, all of Proposition 2.8 and Mathlib bridges |
| [MonotonicityExamples](PreferenceProperties/MonotonicityExamples.lean) | 6 | Problem 2.6 counterexample without continuity |
| [Insatiability](PreferenceProperties/Insatiability.lean) | 3 | Problem 2.3: global insatiability and semi-strict convexity imply LNS |
| [ConvexityExamples](PreferenceProperties/ConvexityExamples.lean) | 13 | Problems 2.2-2.3: compact-menu nonattainment and a flat utility |
| [TransformationExamples](PreferenceProperties/TransformationExamples.lean) | 6 | Problem 2.5: ordinal rescalings destroy concavity or continuity |
| [ContinuousUtility](PreferenceProperties/ContinuousUtility.lean) | 5 | Forward Proposition 2.9, compact attainment and Lemma 2.10 |
| [DiagonalBounds](PreferenceProperties/DiagonalBounds.lean) | 8 | Min/max bounds and an indifferent diagonal point |
| [DiagonalRepresentation](PreferenceProperties/DiagonalRepresentation.lean) | 10 | Unique diagonal coordinate, representation and continuity |
| [IndifferenceCurves](PreferenceProperties/IndifferenceCurves.lean) | 4 | Thin classes, decreasing two-good curves and strict mixtures |
| [PathCounterexample](PreferenceProperties/PathCounterexample.lean) | 7 | Problem 2.7: coordinate bounds without monotonicity do not imply crossing |
| [QuasiLinear](PreferenceProperties/QuasiLinear.lean) | 11 | Proposition 2.16, Problem 2.11 and feasible money compensation |
| [DensePreferenceRanks](PreferenceProperties/DensePreferenceRanks.lean) | 5 | Countable interior ranks and Cantor's order isomorphism |
| [RankCutUtility](PreferenceProperties/RankCutUtility.lean) | 13 | Bounded rational-cut representation, including extreme ranks |
| [GeneralContinuousRepresentation](PreferenceProperties/GeneralContinuousRepresentation.lean) | 5 | Full Proposition 2.9 without monotonicity |
| [FiniteCoordinateComparison](PreferenceProperties/FiniteCoordinateComparison.lean) | 3 | Finite weak, strict and indifferent substitution chains |
| [WeakSeparability](PreferenceProperties/WeakSeparability.lean) | 10 | Full Proposition 2.12 and an aggregator on attained subutility ranges |
| [CommodityBlocks](PreferenceProperties/CommodityBlocks.lean) | 12 | Arbitrary disjoint commodity subsets, leftovers and the orthant equivalence |
| [AdditiveSeparability](PreferenceProperties/AdditiveSeparability.lean) | 7 | Definition 2.13, nontrivial blocks and additive-to-strong Proposition 2.14 |
| [Homotheticity](PreferenceProperties/Homotheticity.lean) | 18 | Definitions 2.17-2.18, cone scaling and the forward implication of Proposition 2.19 |
| [HomotheticRays](PreferenceProperties/HomotheticRays.lean) | 13 | Strict rank changes, cofinality and indifference on positive and negative reference rays |
| [RepresentationExtension](PreferenceProperties/RepresentationExtension.lean) | 6 | Problem 2.14c: continuous extension from a connected curve meeting every class |
| [HomogeneousExtension](PreferenceProperties/HomogeneousExtension.lean) | 10 | Scale-compatible extension, one-sided ranks and constant preferences |
| [SignedHomotheticRepresentation](PreferenceProperties/SignedHomotheticRepresentation.lean) | 11 | Full Proposition 2.19 and Problem 2.12, including ranks on both sides of the origin |
| [HomotheticIdentification](PreferenceProperties/HomotheticIdentification.lean) | 5 | Problem 2.13: one nonzero class identifies the full homothetic preference |
| [QuasiLinearIdentification](PreferenceProperties/QuasiLinearIdentification.lean) | 8 | Identified goods projection, subutility calibration and all money levels |
| [QuasiLinearIdentificationExample](PreferenceProperties/QuasiLinearIdentificationExample.lean) | 6 | Continuous strictly monotone preferences with the same curve and different rankings |
| [LinearPreference](PreferenceProperties/LinearPreference.lean) | 8 | Problem 2.9a: all seven properties and straight-line indifference curves |
| [MinimumUtility](PreferenceProperties/MinimumUtility.lean) | 6 | Page 32: finite minimum, strict all-coordinate increase and failure of strict monotonicity |
| [LeontiefPreference](PreferenceProperties/LeontiefPreference.lean) | 10 | Problem 2.9b: all seven properties and the exact two-ray indifference curves |
| [CobbDouglasMonotonicity](PreferenceProperties/CobbDouglasMonotonicity.lean) | 10 | Page 32: boundary failures, strict all-coordinate increase and interior strict monotonicity |
| [IntervalNonattainment](PreferenceProperties/IntervalNonattainment.lean) | 5 | Problem 2.2: the nonempty convex menus `(1,5)` and `(3,∞)` have no best point |
| [UpperSemicontinuousSeries](PreferenceProperties/UpperSemicontinuousSeries.lean) | 2 | Upper semicontinuity under uniform limits and summably bounded series |
| [WeightedUtilitySemicontinuity](PreferenceProperties/WeightedUtilitySemicontinuity.lean) | 13 | Problem 2.10: exact dyadic weights, upper semicontinuity and dense-enumeration representation |
| [FiniteMeasureDistribution](PreferenceProperties/FiniteMeasureDistribution.lean) | 6 | Finite-measure lower-tail distributions, upper semicontinuity and continuity at atom-free cutoffs |
| [MeasureUtility](PreferenceProperties/MeasureUtility.lean) | 10 | Lower-contour representation, cumulative-distribution identity and null-class continuity |
| [OrthantMeasure](PreferenceProperties/OrthantMeasure.lean) | 5 | Boundary neighborhoods have positive Lebesgue measure; exact Problem 2.15 hypotheses |
| [MeasureUtilityAtoms](PreferenceProperties/MeasureUtilityAtoms.lean) | 8 | Problem 2.15: a unit atom gives discontinuity under strictly increasing one-good preference |
| [ProductQuasiconcavity](PreferenceProperties/ProductQuasiconcavity.lean) | 9 | Product mixture inequalities, including strict positive-rank inequalities |
| [PlateauProductPreference](PreferenceProperties/PlateauProductPreference.lean) | 11 | Problem 2.8a, first utility: convex and continuous, no concave representation |
| [SplitProductPreference](PreferenceProperties/SplitProductPreference.lean) | 13 | Problem 2.8a, second utility: semi-strict convexity and discontinuity |
| [SplitProductNoConcavity](PreferenceProperties/SplitProductNoConcavity.lean) | 2 | Direct Jensen contradiction excludes every concave representation of the split preference |
| [RepresentationQuantifiers](PreferenceProperties/RepresentationQuantifiers.lean) | 15 | Problem 2.1: all/some statements for ordinal and representation properties |
| [RepresentationQuantifierExamples](PreferenceProperties/RepresentationQuantifierExamples.lean) | 17 | Same-preference transformations separating some from all representations |
| [RecursiveRankInsertion](PreferenceProperties/RecursiveRankInsertion.lean) | 9 | Problem 2.14d: exact tie, max-plus-one, min-minus-one and midpoint insertion rule |
| [RecursiveRanks](PreferenceProperties/RecursiveRanks.lean) | 13 | Problem 2.14d: permanent ranks, preserved comparisons and representation on the enumerated set |
| [RecursiveRankDensity](PreferenceProperties/RecursiveRankDensity.lean) | 9 | Problem 2.14e: first midpoint insertion, exclusion of gaps and density in the smallest interval |
| [AppendixMetricTopology](PreferenceProperties/AppendixMetricTopology.lean) | 21 | Appendix 2: Euclidean distance, basic topology, relative sets, closure and interior |
| [AppendixSemicontinuity](PreferenceProperties/AppendixSemicontinuity.lean) | 9 | Appendix 2: semicontinuity, compact maxima and correction of the signed-series diagnostic |
| [RatioSumUtility](PreferenceProperties/RatioSumUtility.lean) | 6 | Problem 2.8b: the exact ratio/sum utility and its rank geometry |
| [RatioSumNoConcavity](PreferenceProperties/RatioSumNoConcavity.lean) | 3 | Problem 2.8b: geometric-decay contradiction for every concave representation |
| [RatioSumPreference](PreferenceProperties/RatioSumPreference.lean) | 15 | Problem 2.8b: continuity, semi-strict convexity and the complete conclusion |
| [SampledRankExtension](PreferenceProperties/SampledRankExtension.lean) | 10 | Supremum extension of sampled ranks with bracketing and exact agreement |
| [RecursiveUtilityLimits](PreferenceProperties/RecursiveUtilityLimits.lean) | 11 | Problem 2.14f-g: finite limits, independence and continuity of the exact recursive scale |
| [AugmentedPreferenceSample](PreferenceProperties/AugmentedPreferenceSample.lean) | 6 | Dense samples containing attained extreme indifference classes |
| [PolygonalCurve](PreferenceProperties/PolygonalCurve.lean) | 8 | Continuous countable connect-the-dots curves in convex domains |
| [NumericalRankBrackets](PreferenceProperties/NumericalRankBrackets.lean) | 3 | Countable bracketing from a possibly discontinuous numerical representation |
| [PreferenceReferenceCurve](PreferenceProperties/PreferenceReferenceCurve.lean) | 15 | Problem 2.14a-g: complete book construction, with a single segment for attained extrema |
| [StrongSeparabilityCancellation](PreferenceProperties/StrongSeparabilityCancellation.lean) | 13 | Cancellation consequences of the actual strong-separability hypotheses |
| [StrongSeparabilityTopology](PreferenceProperties/StrongSeparabilityTopology.lean) | 6 | Local Thomsen cancellation from continuity, connectedness and a third block |
| [SubutilityContinuity](PreferenceProperties/SubutilityContinuity.lean) | 8 | Order-homeomorphic subutility ranges and coordinate continuity of the aggregator |
| [FiniteProductContinuity](PreferenceProperties/FiniteProductContinuity.lean) | 4 | Joint continuity from coordinate continuity and monotonicity on finite interval products |
| [AppendixSequences](PreferenceProperties/AppendixSequences.lean) | 15 | Appendix 2: convergence, accumulation, completeness and compactness |
| [AppendixContinuousFunctions](PreferenceProperties/AppendixContinuousFunctions.lean) | 12 | Appendix 2: continuity, relative domains and the intermediate-value theorem |
| [AppendixExtrema](PreferenceProperties/AppendixExtrema.lean) | 14 | Appendix 2: finite and extended extrema, empty sets and compact maximum attainment |

The current subset passes the full fresh-source audit: **704 theorems** and
**882 audited declarations**. This includes 98 theorems in twelve local Chapter 1
prerequisite modules and **606 new chapter and appendix theorems**. All 14 verifier tests pass.
The copied modules are from Chapter 1 commit `dfb548d`; the project has no dependency
on another chapter's build products. The [verification record](verification/verification.json)
contains the generated hashes and axiom checks.

The additive-existence direction of Proposition 2.14 and its Problem 2.1 table entry
are still in progress. Weak separability and homotheticity are fully characterized.
The homogeneous representation handles positive, negative and origin-indifferent
ranks without imposing commodity monotonicity.
Problem 2.13 distinguishes full identification from a nonzero homothetic curve
from identification over the observed goods projection in the quasi-linear case.
The general continuous-representation theorem is proved through Cantor's countable
order isomorphism and rational cuts; the book's diagonal proof is also complete.
Problem 2.14 is complete through the connecting curve, exact recursive assignment,
interval-dense range, finite sequence limits and continuous extension.
Problem 2.8 is complete for all three exact displayed utilities. Problem 2.1 retains only
the additive-existence dependency; the book's excluded ???? cell is unclaimed.
The [Appendix 2 inventory](docs/appendix2-source-map.md) separates completed bridges
from its remaining obligations and records the signed-series diagnostic correction.
Problem 2.15 is complete under its stated measure assumptions. Indifference classes
of zero measure suffice for continuity; atoms can prevent it even under strict monotonicity.
This is not a completed-chapter claim.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The reference verifier builds the complete project, freshly elaborates its source and
audits all named declarations. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. Pending source-map entries are not completed results.
