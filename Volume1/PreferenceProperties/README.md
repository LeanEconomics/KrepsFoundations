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

The current subset passes the full fresh-source audit: **167 theorems** and
**233 audited declarations**. This includes 98 theorems in twelve local Chapter 1
prerequisite modules and **69 new Chapter 2 theorems**. All 14 verifier tests pass.
The copied modules are from Chapter 1 commit `dfb548d`; the project has no dependency
on another chapter's build products. The [verification record](verification/verification.json)
contains the generated hashes and axiom checks.

The general continuous-representation theorem, the diagonal construction, separability,
quasi-linearity, homotheticity and remaining problem solutions are still in progress.
This is not a completed-chapter claim.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The reference verifier builds the complete project, freshly elaborates its source and
audits all named declarations. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. Pending source-map entries are not completed results.
