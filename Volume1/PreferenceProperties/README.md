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

The current subset passes the full fresh-source audit: **267 theorems** and
**375 audited declarations**. This includes 98 theorems in twelve local Chapter 1
prerequisite modules and **169 new Chapter 2 theorems**. All 14 verifier tests pass.
The copied modules are from Chapter 1 commit `dfb548d`; the project has no dependency
on another chapter's build products. The [verification record](verification/verification.json)
contains the generated hashes and axiom checks.

The additive-existence direction of Proposition 2.14, homotheticity and remaining
problem solutions are still in progress. Weak separability is fully characterized.
The general continuous-representation theorem is proved through Cantor's countable
order isomorphism and rational cuts; the book's diagonal proof is also complete.
Problem 2.14's specific recursive construction remains a separate obligation.
This is not a completed-chapter claim.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The reference verifier builds the complete project, freshly elaborates its source and
audits all named declarations. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. Pending source-map entries are not completed results.
