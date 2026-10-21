# Source map

David M. Kreps, *Microeconomic Foundations I*, Chapter 2, pp. 30-49.
Printed pages; Lean names relative to `Kreps.PreferenceProperties`.
This chapter is in progress. `Pending` makes no formalization claim.

## Definitions and propositions

| Source | Claim | Lean / status |
| --- | --- | --- |
| Definition 2.1; Proposition 2.2, p. 31 | Monotone/strictly monotone preferences and every representing utility | `MonotonePreference`, `StrictlyMonotonePreference`, `proposition_2_2_monotone`, `proposition_2_2_strict`; verified |
| Section 2.1, p. 32 | Strict increase in all components; minimum utility and Cobb-Douglas examples, including axes | `StrictAllIncreasePreference`; minimum and Cobb-Douglas examples pending |
| Definition 2.3, p. 32 | Global/local insatiability and numerical restatements | `GloballyInsatiable`, `LocallyInsatiable`, `locallyInsatiable_iff_open`, `locallyInsatiable_global`, numerical equivalences; verified |
| Definition 2.4, p. 33 | Convex, strictly convex and semi-strictly convex preferences | `Mix`, `ConvexMenu`, `convexMenu_iff`, `ConvexPreference`, `StrictlyConvexPreference`, `SemiStrictlyConvexPreference` |
| Proposition 2.5, p. 33 | Convex preference iff every upper weak contour is convex | `proposition_2_5`, `convexPreference_iff_contours` |
| Proposition 2.6, p. 33 | Convexity of maximizers; at most one under strict convexity | `proposition_2_6_convex`, `proposition_2_6_unique`; neither assumes nonempty choice |
| Definition 2.7, p. 34 | Concavity and its strict version; all three quasi-concavity variants | `ConcaveUtility`, `StrictlyConcaveUtility`, `QuasiConcaveUtility`, `SemiStrictlyQuasiConcaveUtility`, `StrictlyQuasiConcaveUtility`; Mathlib bridge theorems in `ConcaveUtility.lean` |
| Proposition 2.8a, p. 34 | Concave/strictly concave representation implies convex/strictly convex preference | `proposition_2_8a_concave`, `proposition_2_8a_strict` |
| Proposition 2.8b, p. 34 | Three quasi-concavity equivalences | `proposition_2_8b_quasi`, `proposition_2_8b_strict`, `proposition_2_8b_semiStrict` |
| Section 2.2, p. 35 | Concavity need not survive ordinal rescaling; quasi-concavity does | `quasiConcave_strictMono_transform`, `problem_2_5a`; nonexistence of any concave representation remains pending in Problem 2.8 |
| Proposition 2.9, pp. 35-38 | Continuous representation implies continuous preference, and full converse | `proposition_2_9`, `proposition_2_9_metric`; full converse without monotonicity, via countable interior ranks, Cantor's order isomorphism and rational cuts |
| Lemma 2.10, pp. 36, 38 | A continuous path crosses any intervening indifference class | `indifference_on_connected_image`, `lemma_2_10`; no continuous representation assumed |
| Section 2.3, pp. 36-38 | Five-step diagonal construction under the additional monotonicity assumptions | `DiagonalBounds` and `DiagonalRepresentation`: existence, uniqueness, representation and continuity; `proposition_2_9_monotone`, `continuous_representation_strictAllIncrease` |
| Section 2.3, p. 35 | Compact-menu attainment via continuous utility | `compact_choice_of_continuous_utility`; separate from the copied Chapter 1 direct compactness proof |
| Section 2.4, pp. 38-39 | Thin indifference classes; decreasing two-good curves; crossing; strict convexity | `indifferenceClass_no_ball`, `indifferenceClass_interior_empty`, `indifferenceCurve_decreasing`, `monotone_path_crossing`, `indifference_mixture_strict`; no smoothness claim |
| Definition 2.11; Proposition 2.12, pp. 40-41 | Disjoint commodity blocks; weak separability iff a strictly increasing aggregator on attained subutility ranges | `WeaklySeparable`, `BaselineSubutility`, `SubutilityAggregator`, `proposition_2_12`; `exists_commodity_assignment`, `orthantGrouping` and `proposition_2_12_orthant` cover arbitrary disjoint subsets and leftovers |
| Definition 2.13, p. 42 | Strong separability for unions of blocks; nontriviality of a block | `StronglySeparable`, `NontrivialBlock`, `ThreeNontrivialBlocks`, `stronglySeparable_weakly`, `nontrivialBlock_iff_every_context`, `threeNontrivialBlocks_card` |
| Proposition 2.14, p. 42 | Continuous strong separability with at least three nontrivial blocks gives continuous additive representation | Pending; this full theorem is in scope despite the book referring out for its proof |
| Proposition 2.14, p. 42 | An additive representation implies strong separability | `AdditiveUtility`, `AdditivelyRepresentable`, `proposition_2_14_additive`; continuous subutilities also yield continuous utility and preference |
| Definition 2.15; Proposition 2.16, pp. 43-44 | Quasi-linearity iff own-money order, common money-translation invariance and compensability | `QuasiLinearUtility`, `QuasiLinear`, `OwnMoneyOrder`, `MoneyTranslation`, `MoneyCompensable`, `proposition_2_16`; money is nonnegative throughout |
| Section 2.6, p. 44 | Utility differences measure compensating money in quasi-linear units | `QuasiLinearDifference`, `quasiLinear_compensation`, `quasiLinear_compensation_of_preferred`, `printed_compensation_bundle_counterexample`; corrected goods and explicit feasibility |
| Definitions 2.17-2.18, p. 44 | Homothetic preference, cones and homogeneous functions | `HomotheticPreference`, `NonnegativeCone`, `HomogeneousOfDegree`, `HomogeneousUtility`, `homogeneousUtility_iff_degree_one`; nonnegative scalars include zero |
| Proposition 2.19, p. 44 | Continuous homothetic preference iff continuous degree-one homogeneous representation | `proposition_2_19`; the full theorem without commodity monotonicity. Positive and negative reference rays cover all ranks; `SignedRay` joins them when both occur. One-sided and constant preferences are handled separately. |

## Problems

| Source | Claim | Lean / status |
| --- | --- | --- |
| Problem 2.1; Table 2.1, p. 45 | All/some quantifiers for every representation-property row | Monotonicity rows verified; concavity and quasi-concavity implications follow from Proposition 2.8. Remaining rows and the complete quantifier table are pending. The explicitly excluded ???? cell stays unclaimed. Strong separability uses Proposition 2.14's hypotheses. |
| Problem 2.2, p. 46 | Strictly convex preference can fail to attain a best point on a compact convex menu | `NonattainingUtility`, `problem_2_2`; the introductory open/unbounded interval examples remain to be recorded separately |
| Problem 2.3, p. 46 | Global insatiability plus semi-strict convexity implies local insatiability; convexity alone does not | `problem_2_3_implication`, `FlatUtility`, `problem_2_3_counterexample` |
| Problem 2.4, p. 46 | Proof of Proposition 2.5 | `problem_2_4` |
| Problem 2.5a-b, p. 46 | Increasing transformations can destroy concavity and continuity | `ConvexWarp`, `problem_2_5a`, `jumpUtility_not_continuous`, `problem_2_5b` |
| Problem 2.6, p. 46 | Strict all-coordinate monotonicity iff monotonicity plus LNS under continuity; conclusions without continuity | `problem_2_6`, `strictAllIncrease_locallyInsatiable`, `monotone_locallyInsatiable_strictAllIncrease`, `problem_2_6_without_continuity` |
| Problem 2.7, p. 46 | Continuous, locally insatiable preference can fail the coordinatewise path-crossing assertion without monotonicity | `NetUtility`, `AvoidingPath`, `problem_2_7`, `netPreference_not_monotone` |
| Problem 2.8a, pp. 46-47 | The two displayed product-based utilities: convexity, lack of any concave representation, semi-strictness and continuity | Pending; exact piecewise formulas were checked against page images |
| Problem 2.8b, p. 47 | The displayed continuous semi-strictly convex preference has no concave representation | Pending; the difficult nonexistence conclusion is required |
| Problem 2.9a, p. 47 | Positive linear utility: indifference curves and all seven listed preference properties | Pending |
| Problem 2.9b, p. 47 | Leontief utility: indifference curves and all seven listed preference properties | Pending |
| Problem 2.10, p. 47 | The rational-weight construction is upper semicontinuous | Pending |
| Problem 2.11, p. 48 | Full quasi-linear characterization, including the compensating-money construction | `quasiLinear_of_money_properties`, `problem_2_11`; subutility is receipt minus payment relative to a fixed reference bundle |
| Problem 2.12, p. 48 | Homogeneous representation | `problem_2_12`; no optional strict-monotonicity assumption is used |
| Problem 2.13, p. 48 | Information recoverable from one indifference curve under homotheticity or quasi-linearity | `problem_2_13_homothetic` identifies the full continuous strictly monotone homothetic preference from a nonzero class; `strictlyMonotone_origin_class` records the degenerate exception. `CurveGoods`, `curveGoods_iff_subutility_le`, `problem_2_13_quasiLinear_identified` identify all money levels over the observed goods projection, with full identification when that projection is the whole goods domain. `quasiLinear_outside_projection` ranks remaining bundles above the curve. `problem_2_13_quasiLinear_nonidentification` supplies a continuous strictly monotone two-good counterexample to global identification; its observed goods projection is `[0,1]`. |
| Problem 2.14a, p. 48 | Construct a continuous connected curve with preference bounds for every bundle, including attained/unattained extrema | Pending |
| Problem 2.14b, p. 48 | Every indifference class meets the constructed curve | Pending construction of the specified curve in part (a); the general connected-image crossing lemma is available |
| Problem 2.14c, p. 48 | Extend a continuous curve representation to the full domain by indifference | `LiftedUtility`, `liftedUtility_represents`, `liftedUtility_agrees`, `liftedUtility_range`, `continuous_of_ordConnected_range`, `problem_2_14c`; the curve is connected and meets every indifference class |
| Problem 2.14d-e, p. 49 | Recursive countable assignment represents preference and has interval-dense values | Pending; choose initial value zero for the first class |
| Problem 2.14f-g, p. 49 | Finite sequence limits, independence of sequence, continuous representation on the curve | Pending |
| Problem 2.15, p. 49 | Finite-measure lower-contour utility: representation, upper semicontinuity, discontinuity example and sufficient continuity conditions | Pending; full measure assumptions and orthant domain required |

## Local prerequisites and appendices

The independent project copies twelve Chapter 1 modules from commit `dfb548d`:
`Basic`, `Rationalization`, `FiniteUtility`, `StrictPreference`, `CountableUtility`,
`InfiniteChoice`, `UtilityEquivalence`, `ContinuousPreference`, `OrthantRepresentation`,
`CompactChoice`, `UtilityExamples` and `Lexicographic`. Their mathematical declarations
are unchanged; imports and namespaces are local. They remain covered by the
[Chapter 1 source map](../../ChoicePreferenceUtility/docs/source-map.md) and are
freshly audited again in this project. Their theorem counts are prerequisite counts,
not new Chapter 2 results.

Appendix 2, pp. 441-451, and the relevant portions of Appendix 3, pp. 452-468, need
itemized source inventories and book-statement bridges. Imported Mathlib support is
not by itself a claim that either appendix is complete. The volume proposal records
which later chapters own the rest of Appendix 3.
