# Source map

David M. Kreps, *Microeconomic Foundations I*, Chapter 1, pp. 1-29.
Printed pages; Lean names relative to `Kreps.ChoicePreferenceUtility`.
All numbered Chapter 1 propositions and the mathematical parts of Problems 1.1-1.17
are covered. Nonmathematical discussion and remaining appendix work are identified below.

## Definitions, assumptions and propositions

| Source | Claim | Lean |
| --- | --- | --- |
| Section 1.1; (1.1)-(1.3), pp. 1-3 | Choice model, maximization and representation | `FullMenus`, `ChoiceRule`, `FeasibleOn`, `Feasible`, `PrefChoice`, `UtilityPref`, `UtilityChoice`, `Represents` |
| Section 1.1, p. 2 | Commodity bundles, positive prices, affordable menus and the pie reversal | `NonnegativeOrthant`, `StrictlyPositiveOrthant`, `BudgetMenu`, `budgetMenu_nonempty`, `BreadCheeseSalamiBundle`, `added_option_reversal_not_coherent` |
| Definition 1.1, pp. 3-4 | Finite nonemptiness, coherence, completeness and transitivity | `FiniteNonempty`, `CoherentOn`, `Coherent`, `Complete`, `TransitivePref`, `Rational` |
| Proposition 1.2a-c, p. 4 | Finite choice/preference/utility equivalence | `proposition_1_2a`, `proposition_1_2b`, `proposition_1_2c` |
| Proposition 1.3a-b, p. 5 | Utility generates rational preference and coherent finite-nonempty choice | `proposition_1_3a`, `proposition_1_3b` |
| Proposition 1.4, pp. 5-6 | Rational preference generates coherent finite-nonempty choice | `proposition_1_4` |
| Proposition 1.5, pp. 6-7 | Pairwise rationalization with possible empty choice | `proposition_1_5` |
| Definition 1.6, p. 7 | No-better-than sets | `NoBetterThan` |
| Proposition 1.7, p. 8 | Nonemptiness, nesting and strict inclusion | `proposition_1_7`, `mem_noBetterThan_self`, `pref_iff_noBetterThan_subset`, `strict_iff_noBetterThan_ssubset` |
| Proposition 1.8, p. 8 | Finite representation by cardinality | `FiniteUtility`, `proposition_1_8` |
| Proposition 1.9a-h, pp. 9-10 | Strict preference and indifference | `proposition_1_9a` through `proposition_1_9h` |
| Proposition 1.10, p. 10 | Reconstruction from strict preference | `proposition_1_10` |
| Proposition 1.11, pp. 10-11 | Countable utility representation | `proposition_1_11` |
| Proposition 1.12, pp. 11-12 | Countable-subset representation criterion, both directions | `OrderSeparating`, `proposition_1_12` |
| Definition 1.13, p. 13 | Continuity of preferences | `ContinuousPreference`, `MetricContinuousPreference`, `continuousPreference_iff_metric` |
| Proposition 1.14a-d, p. 14 | Equivalent continuity characterizations | `proposition_1_14a` through `proposition_1_14d` |
| Proposition 1.15, pp. 14-15 | Utility representation on the nonnegative orthant | `NonnegativeOrthant`, `proposition_1_15`, `proposition_1_15_metric` |
| Section 1.6, pp. 15-16 | Nonattainment and emptying arbitrary infinite choices | `empty_infinite_menus_preserves_choice`, `SemiOpenSquare`, `SumUtility`, `semiOpenSquare_improvement`, `semiOpenSquare_empty_choice` |
| Assumption 1.16, p. 16 | Nonemptiness whenever a revealed maximum exists | `Assumption116` |
| Proposition 1.17, p. 17 | Exact rationalization iff Assumption 1.16 | `proposition_1_17` |
| Proposition 1.18, p. 17 | Empty choice without a revealed maximum | `proposition_1_18` |
| Proposition 1.19, p. 17 | Nonempty choice on compact menus | `proposition_1_19` |
| Proposition 1.20, p. 17 | Increasing transformations preserve representation | `proposition_1_20` |
| Proposition 1.21, p. 18 | Equivalent utilities and extended-real monotone extension | `proposition_1_21`, `proposition_1_21_extension` |
| Section 1.8, p. 18 | Utility differences and the utility zero have no ordinal meaning | `ordinalWarp_strictMono`, `ordinal_difference_reversal`, `ordinal_zero_not_invariant` |
| Section 1.8, pp. 19-20 | The vaccination frames give identical state-contingent outcomes | `FluProbability`, `fluProbability_valid`, `framing_A_eq_X`, `framing_B_eq_Y`, `framing_reversal_impossible` |
| Section 1.8, pp. 20-21 | Added-option reversal, rejected alternatives, and four possible comparison responses | `added_option_reversal_not_coherent`, `RejectedSet`, `rejectedSet_subset`, `partial_response_exhaustive`, `partial_positive_responses_exclusive` |
| Definition 1.22; Proposition 1.23, p. 28 | SGARP and rationalizability | `ObservedWeak`, `ObservedStrict`, `SGARP`, `RationalizesData`, `proposition_1_23`; corrections: `printed_strict_counterexample`, `empty_observation_not_rationalizable` |

## Problems

Each row records the mathematical conclusion requested in the corresponding problem.

| Source | Claim | Lean |
| --- | --- | --- |
| Problem 1.1, pp. 23-24 | Wine rule and coherence counterexample | `WineChoice`, `wine_universe_valid`, `wineChoice_feasible`, `wineChoice_nonempty`, `wineChoice_full`, `wineChoice_pair`, `problem_1_1` |
| Problem 1.2, p. 24 | Nonemptiness and failure of coherence for union choice | `problem_1_2_nonempty`, `problem_1_2_not_coherent` |
| Problem 1.3, p. 25 | Completeness and failure of transitivity for union preference | `problem_1_3_complete`, `problem_1_3_not_transitive` |
| Problem 1.4, p. 25 | Relation between the two joint constructions | `problem_1_4_revealed`, `problem_1_4_subset`, `problem_1_4_strict_subset` |
| Problem 1.5, p. 25 | Sen alpha/beta equivalence | `SenAlpha`, `SenBeta`, `problem_1_5` |
| Problem 1.6a-c, p. 25 | Pareto transitivity, incompleteness, strict preference and indifference | `problem_1_6_transitive`, `problem_1_6_not_complete`, `problem_1_6_strict`, `problem_1_6_asymmetric`, `problem_1_6_not_negativelyTransitive`, `problem_1_6_indifference`, `problem_1_6_equivalence` |
| Problem 1.7a-b, pp. 25-26 | Majority completeness, cycles and strict majority | `problem_1_7_complete`, `problem_1_7_strict`, `problem_1_7_asymmetric`, `problem_1_7_not_transitive`, `problem_1_7_not_negativelyTransitive` |
| Problem 1.8, p. 26 | Proof of Proposition 1.7 | `problem_1_8`, `proposition_1_7` |
| Problem 1.9, p. 26 | Proof of Proposition 1.10 | `problem_1_9` |
| Problem 1.10, p. 26 | Lexicographic rationality without real representation | `problem_1_10` |
| Problem 1.11, p. 26 | Proof of all four continuity equivalences | `problem_1_11` |
| Problem 1.12, p. 26 | Rational separating set and the geometric-weight construction | `rationalUnitPoints_countable`, `problem_1_12_separating`, `GeometricRationalWeights`, `geometricRationalWeights_valid`, `rationalUtility_formula`, `problem_1_12_represents` |
| Problem 1.12, p. 26 | Discontinuity at every positive rational; a continuous representation of the same continuous preference | `rationalUtility_jump`, `problem_1_12_discontinuous`, `problem_1_12_continuous_representation`, `problem_1_12_continuous_preference` |
| Problem 1.13, pp. 26-27 | Direct compactness proof; role of Assumption 1.16 | `problem_1_13_direct`, `problem_1_13_necessity`, `orthantSegment_compact`, `orthantSegment_infinite` |
| Problem 1.14a-b, p. 27 | Equal preferences and strictly increasing transforms on the utility range | `problem_1_14a`, `problem_1_14b` |
| Problem 1.14c, p. 27 | Jump utility with no globally strictly increasing transform | `JumpUtility`, `jumpUtility_represents`, `problem_1_14c` |
| Problem 1.14d, p. 27 | Monotone supremum extension; need for extended reals | `problem_1_14d`, `fractionUtility_represents`, `problem_1_14d_top`, `problem_1_14d_bot`, `problem_1_14d_no_real_extension` |
| Problem 1.15, p. 27 | Exact rationalization on a restricted domain containing small menus | `ContainsSmallMenus`, `NonemptyOn`, `problem_1_15` |
| Problem 1.16a, p. 28 | Feasible selections accommodated by constant utility | `problem_1_16a` |
| Problem 1.16b, p. 28 | Coherent pair observations with no rationalization | `cyclicMenus_injective`, `cyclicChoices_valid`, `cyclicChoices_coherent`, `problem_1_16b_not_rationalizable` |
| Problem 1.16c, p. 28 | SGARP necessity and sufficiency | `proposition_1_23`; source corrections are explicit in `docs/corrections.md` |
| Problem 1.17a, p. 29 | Strict preference excludes positive indifference in either direction | `PartialPreferenceAxioms`, `problem_1_17a` |
| Problem 1.17b, p. 29 | Induced weak preference is reflexive and transitive, but need not be complete | `PartialWeak`, `problem_1_17b`, `problem_1_17b_not_complete` |
| Problem 1.17c, p. 29 | Reflexivity and transitivity are precisely the necessary weak-preference properties | `partialWeak_strict_indifferent`, `problem_1_17c` |
| Problem 1.17d, p. 29 | Unit-threshold utility and equal utility satisfy all four axioms | `ThresholdPreference`, `EqualUtility`, `problem_1_17d` |
| Problem 1.17e, p. 29 | Two disjoint strict pairs satisfy the axioms but have no threshold representation | `TwoPlusTwo`, `twoPlusTwo_not_threshold`, `problem_1_17e` |
| Problem 1.17f, p. 29 | Bounded integer chains characterize exact threshold/equality representation on a finite set | `ThresholdStep`, `ThresholdReachable`, `BoundedThresholdChains`, `ThresholdPotential`, `boundedThresholdChains_of_representation`, `threshold_representation_of_bounded`, `problem_1_17f` |

## Appendix prerequisites

| Source | Claim | Lean |
| --- | --- | --- |
| A1, p. 439 | Natural and positive-integer induction; strong induction; parity example | `appendix_A1_nat_induction`, `appendix_A1_strong_induction`, `appendix_A1_positive_induction`, `appendix_A1_even_or_odd`, `appendix_A1_parity_exclusive` |
| A1, pp. 439-440 | Integer induction in both directions and the caution about real numbers | `appendix_A1_integer_induction`, `appendix_A1_no_next_real`, `appendix_A1_zero_rational`, `appendix_A1_not_all_nonnegative_rational` |
| A2, pp. 441-451 | Dependencies used here: metric neighborhoods, sequential closedness, connectedness, countable density and compact finite intersections | Pinned Mathlib supplies these ingredients to `ContinuousPreference`, `OrthantRepresentation` and `CompactChoice`. This is dependency use, not completion of Appendix 2. Its complete source inventory and remaining bridges belong to the Chapters 1-3 program. |

## Scope of the examples

Problem 1.12 is proved for arbitrary positive summable rational weights. The explicit
geometric recipe accepts any injective indexing and so applies to the book's displayed
enumeration; the proof does not compute its particular numerical initial values. The
formula describes the constructed utility, and its jumps establish the requested failure
of continuity even though identity continuously represents the preference.

Problem 1.17f asks for an additional condition, rather than specifying one. Our condition
uses only the primitive strict and positive-indifference relations and integer chains.
For some positive integer `M`, indifference edges have score zero, strict comparisons
raise the score by `M + 1`, and absence of a strict comparison permits a score decrease
of `M`. Every chain starts at score zero. The condition requires a common upper bound
on the scores of all finite chains. It contains no utility function or representation
assumption.

Necessity chooses a common scale for the finitely many strict utility gaps and telescopes
the chain inequalities. Sufficiency takes the largest reachable integer score at each
alternative, adds a small bounded code for its positive-indifference class, and divides
by `M + 1/2`. The code ensures equal utilities exactly for positively indifferent
alternatives; the integer gaps ensure exactly the required strict unit threshold.
Both directions, including the quotient code and all finite/empty-type cases, are in Lean.
This is a chain criterion, not a claim to have proved a different forbidden-pattern theorem.

## Nonmathematical discussion

Figure 1.1 on p. 1 motivates later supply, demand and equilibrium theory; it does not
state a Chapter 1 equilibrium theorem. Section 1.8, pp. 18-23, discusses positive versus
normative interpretation, experimental responses, framing, choice procedures, preference
formation and limits of the model. These empirical and methodological discussions are
recorded as exposition, not turned into assumed Lean propositions. Their mathematical
examples and the alternative partial-preference model are accounted for above.
