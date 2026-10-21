# Kreps Chapter 1: Choice, Preference, and Utility, in Lean

This is the `Volume1/ChoicePreferenceUtility` proof project in Kreps Foundations.
It follows Chapter 1, pp. 1-29, including Problems 1.1-1.17 and the results inside them.
[Return to the library index](../../README.md).

Status: Chapter 1 mathematical coverage and Appendix 1 complete; full audit passed.
See the [source map](docs/source-map.md) for itemized coverage and the explicit division
of remaining appendix work, and [corrections](docs/corrections.md) for statement changes.
All declarations are in `Kreps.ChoicePreferenceUtility`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](ChoicePreferenceUtility/Basic.lean) | 5 | Choice, preference, utility and menu-domain definitions |
| [Rationalization](ChoicePreferenceUtility/Rationalization.lean) | 12 | Propositions 1.3-1.5 and pairwise rationalization |
| [FiniteUtility](ChoicePreferenceUtility/FiniteUtility.lean) | 10 | Propositions 1.2, 1.7-1.8 and Problem 1.8 |
| [StrictPreference](ChoicePreferenceUtility/StrictPreference.lean) | 12 | Propositions 1.9-1.10 and Problem 1.9 |
| [CountableUtility](ChoicePreferenceUtility/CountableUtility.lean) | 10 | Propositions 1.11-1.12 and the positive summable-weight construction |
| [InfiniteChoice](ChoicePreferenceUtility/InfiniteChoice.lean) | 6 | Assumption 1.16, Propositions 1.17-1.18 and arbitrary infinite-menu modifications |
| [UtilityEquivalence](ChoicePreferenceUtility/UtilityEquivalence.lean) | 13 | Propositions 1.20-1.21 and Problems 1.14a-b, d |
| [RevealedPreference](ChoicePreferenceUtility/RevealedPreference.lean) | 3 | Observed relations and a proved correction to the printed definition |
| [ContinuousPreference](ChoicePreferenceUtility/ContinuousPreference.lean) | 10 | Definition 1.13, Proposition 1.14a-d and Problem 1.11 |
| [OrthantRepresentation](ChoicePreferenceUtility/OrthantRepresentation.lean) | 5 | Proposition 1.15 through connectedness and a countable dense set |
| [CompactChoice](ChoicePreferenceUtility/CompactChoice.lean) | 3 | Proposition 1.19 and the direct proof in Problem 1.13 |
| [UtilityExamples](ChoicePreferenceUtility/UtilityExamples.lean) | 9 | Problem 1.14c-d: jump utility and necessary infinite extension values |
| [ChoiceOperations](ChoicePreferenceUtility/ChoiceOperations.lean) | 14 | Problems 1.2-1.5: joint choice and Sen conditions |
| [ParetoMajority](ChoicePreferenceUtility/ParetoMajority.lean) | 12 | Problems 1.6-1.7 on the nonnegative orthant |
| [RestrictedChoice](ChoicePreferenceUtility/RestrictedChoice.lean) | 6 | Problem 1.15: rationalization from small menus |
| [SGARP](ChoicePreferenceUtility/SGARP.lean) | 7 | Definition 1.22 and Proposition 1.23, with source corrections |
| [ObservationExamples](ChoicePreferenceUtility/ObservationExamples.lean) | 5 | Problems 1.16a-b: hidden ties and cyclic pair observations |
| [WineChoice](ChoicePreferenceUtility/WineChoice.lean) | 6 | Problem 1.1: the full wine-selection rule on a counterexample universe |
| [Lexicographic](ChoicePreferenceUtility/Lexicographic.lean) | 3 | Problem 1.10: rationality without any real utility representation |

| [PartialPreference](ChoicePreferenceUtility/PartialPreference.lean) | 10 | Problem 1.17a-e: incomplete preferences, threshold utility and a counterexample |
| [InfiniteChoiceExamples](ChoicePreferenceUtility/InfiniteChoiceExamples.lean) | 8 | Semi-open-square nonattainment and necessity of Assumption 1.16 |
| [RationalUtilityExamples](ChoicePreferenceUtility/RationalUtilityExamples.lean) | 9 | Problem 1.12: geometric rational weights and discontinuities |
| [CommentaryExamples](ChoicePreferenceUtility/CommentaryExamples.lean) | 12 | Budget menus, ordinal comparisons, framing, pie choice and rejected sets |
| [ThresholdChains](ChoicePreferenceUtility/ThresholdChains.lean) | 11 | Integer-chain criterion and its necessity for threshold representation |
| [ThresholdRepresentation](ChoicePreferenceUtility/ThresholdRepresentation.lean) | 3 | Problem 1.17f: sufficiency, exact indifference and the full equivalence |
| [MathematicalInduction](ChoicePreferenceUtility/MathematicalInduction.lean) | 9 | Appendix 1: induction principles, parity and the real-number caution |

The full fresh-source audit passes: **213 theorems**, **322 audited declarations**.
All Chapter 1 numbered propositions, Problems 1.1-1.17, the mathematical commentary
examples and Appendix 1 are accounted for. Problem 1.17f uses a proved necessary-and-
sufficient integer-chain condition. Empirical discussion is documented as exposition.
The complete Appendix 2 inventory remains part of the Chapters 1-3 program.

The generated [verification record](verification/verification.json) contains source
hashes and the axiom audit for every declaration. The verifier's 14 failure-path tests
also pass.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the whole library, re-elaborates the proof source freshly, and
audits all supported named declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted; warnings and proof placeholders fail verification.
