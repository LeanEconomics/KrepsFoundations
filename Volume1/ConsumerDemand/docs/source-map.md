# Chapter 3 source map

Source: David M. Kreps, *Microeconomic Foundations I*, printed pp. 50–66.
The mathematical implementation and independent source review are complete.
The frozen full build, fresh elaboration and all-declaration axiom audit passed,
including the primitive-convexity API; see
[verification](../verification/verification.json).
Consumption domains include zero except for the explicitly positive logarithmic
menu. Prices are strictly positive and income is nonnegative unless a statement
explicitly assumes positive income.

| Source | Formalization | Status and scope |
| --- | --- | --- |
| Section 3.1, pp. 50–51 | `Prerequisites`, `BudgetSets`, `PrimitivePreferences` | Complete preference/utility conventions, positive prices, nonnegative income, budget and primitive continuous-representation bridge. |
| Proposition 3.1a–d, pp. 53–54 | `ConsumerProblem`, `BudgetSets`, `PrimitiveConvexChoice` | Complete. Scaling preserves the entire solution set; existence; convexity and uniqueness; local insatiability forces budget exhaustion. Convexity and uniqueness are also available directly from primitive preference assumptions, composing Chapter 2's menu arguments with the budget results and primitive existence. |
| Figure 3.1, p. 51 | `BudgetGeometry`, `BudgetTriangle` | Complete single-good vertices and exact two-good convex-hull triangle, including zero income. A strictly positive feasible bundle exists at positive income. |
| Figure 3.2a–c, p. 53 | `DemandIllustrations` | Complete constructed continuous witnesses: two distinct optima with nonconvex preferences, the entire budget line with convex but non-strict preferences, and a unique satiation bundle with slack expenditure. The formulas are not claimed to be printed in the book. |
| Figure 3.3, p. 54 | `ConsumerProblem.preferenceChoice_exhausts_budget` | Complete feasible-neighborhood argument. Continuity of expenditure supplies the slack neighborhood; this replaces the printed conservative coordinate-radius estimate. |
| Definition 3.2, p. 54 | `ConsumerProblem`, `IndirectUtility` | Complete full demand correspondence and attained indirect value, with value-at-maximizer and zero-income identities. |
| Proposition 3.3a–c, pp. 54–56 | `BudgetContinuity`, `IndirectUtility` | Complete, including the exact recovery formula, zero-income cases, closed graph, local compact bounds, modern upper hemicontinuity and singleton-selection continuity. |
| Definition 3.4, Proposition 3.5, pp. 57–59 | `CalculusOptimality` and its prerequisites | Complete within-orthant derivative formulation; necessary and concave-sufficient conditions; nonnegative multipliers, complementary slackness, full Lagrangian equivalence, right-coordinate derivative bridge. |
| Cobb–Douglas, pp. 59–60 | `CobbDouglasDemand`, `ShiftedProductDemand` | Complete unique full-domain expenditure-share demand, continuity, positive-income interiority and zero income. Proof uses logarithmic strict support and separate zero-factor comparison; it does not assume the original product is concave. |
| Expenditure shares, p. 60 | `BangForBuck` | Complete other-price independence and the literal ten-percent share formula. |
| Bang for buck and transfers, pp. 61–63 | `CalculusOptimality`, `BangForBuck`, `CommodityTransfers` | Complete marginal ratios and cross-products, the actual budget-preserving transfer, its within-domain derivative, and existence of an improving transfer when the marginal-return gap is positive. Shadow-income discussion anticipates Chapter 10 and is not an unqualified envelope theorem. |
| Ordinal differentiability, p. 63 | `OrdinalDifferentiability` | Complete constructed continuous strictly increasing kink transform, representation of linear one-good tastes, and failure of differentiability at positive consumption even within the orthant. |
| Problem 3.1, p. 64 | `DecreasingDemand` | Complete primitive-preference result: unique origin demand and direct failure of local insatiability at the origin. |
| Problem 3.2, p. 64 | `IrrelevantGoods`, `PrimitiveChoiceProperties` | Complete for any finite useful-good subset, with the literal first-good block defined. Irrelevant goods have zero demand; partial strict convexity gives uniqueness. The primitive wrapper derives existence from rational continuous preferences. |
| Problem 3.3a–c, p. 64 | `PositiveLogDemand` | Complete positive-domain logarithmic demand, coincidence with full-domain Cobb–Douglas at positive income, logarithmic transform identity, and concavity for arbitrary positive weights. Zero income has no positive logarithmic menu. |
| Problem 3.4, p. 64 | `ShiftedLogExample` | Complete exact utility, prices and all three singleton demand sets: `(0,0,5)`, `(6/25,0,398/25)`, `(87/14,167/21,446/7)`. Income 16.4 is represented exactly as 82/5. |
| Problem 3.5, p. 64 | `WaterfillingMultiplier`, `ShiftedDemandProcedure`, `FiniteShiftedDemand` | Complete positive-multiplier existence, truncated formula, zero shifts, corners, zero-income case, and finite active-set algebraic procedure with completeness and soundness. |
| Problem 3.6a–b, p. 64 | `LinearDemand`, `LeontiefDemand` | Complete entire linear demand face including ties, and unique proportional Leontief demand, both at every nonnegative income. |
| Problem 3.7, pp. 64–65 | `CESSupport`, `CESDemand`, `CESLimits`, `CESContinuity` | Complete singleton demand for every exponent below one except zero, both signs, all nonnegative incomes; exact linear tie face at exponent one; demand limit at exponent zero; continuous negative-exponent extension at the axes. |
| Problem 3.8, p. 65 | `SeparableMarginals`, `SeparableDemand`, `MarginalIntersections` | Complete scalar marginal graphs, truncation at zero, existence and uniqueness of the allocation, and necessary/sufficient common-height construction. No assumption that marginal utility tends to zero is imposed. |
| Problem 3.9, p. 65 | `QuasiLinearDemand`, `QuasiLinearUniqueness`, `QuasiLinearWealth`, `MarginalIntersections` | Complete numeraire-price restriction, unique demand, finite target regime when it exists, zero-numeraire regime below it, and absence of any finite target when some marginal curve never crosses the required price ratio. |
| Problem 3.10a, p. 65 | `ProductHomogeneity`, `CESHomogeneity`, `LinearLeontiefHomogeneity`, `SeparableNonhomothetic`, `ShiftedProductHomothetic` | Complete classifications, including positive-domain ordinary logs, the literal shifted-log counterexample, shifted-product iff all shifts vanish for at least two goods, and one-good exceptions. |
| Problem 3.10b, p. 65 | `HomotheticDemand` | Complete scaling of individual choices and the entire choice set. The source income is positive; zero target income is included separately. |
| Problem 3.11a, p. 65 | `QuasiconcaveOptimality` | Complete quasi-concave sufficiency using only the first marginal's positivity, at the actual candidate, with a genuine within-orthant derivative. |
| Problems 3.11b and 3.12, p. 65 | `StationaryCubicExamples` | Complete smooth locally insatiable and strictly convex-preference witnesses: a nonoptimal stationary bundle and a unique optimum forcing multiplier zero. |
| Problem 3.13, p. 65 | `OneSidedConditions` | Complete coordinate left/right necessary conditions and necessary derivative inequalities along genuinely differentiable feasible paths. |
| Problem 3.13 limitation | `CappedAbsoluteDerivatives`, `PartialDerivativeCounterexample` | A continuous full-domain witness with finite one-sided coordinate derivatives everywhere, unique interior optimum, unequal coordinate marginal ratios, and exchange derivative inconsistent with their linear combination. This limits a tempting interpretation; it does not contradict a printed claim. |
| Problem 3.14a–d, pp. 65–66 | `RobinsonCrusoe`, `RobinsonCrusoeConvexity` | Complete literal seedcorn problem, both interval endpoints and zero endowment, existence, convexity, two independent primitive uniqueness criteria, continuous value, upper semicontinuity, and lower semicontinuity under either uniqueness criterion. |

`BudgetContinuity` proves the book's recovery sequence through a stronger,
globally continuous feasible selection: for positive base income and a nonzero
base bundle, scale by `(new income/base income) * (old expenditure/new-price
expenditure)`. Positive prices keep its denominator positive. Zero bundles use
the constant zero selection. The local compact-bound proof uses coordinatewise
half-price bounds rather than the book's single minimum-price bound.

The chapter's Appendix 4–5 dependencies are documented separately in
[appendix prerequisites](appendix-prerequisites.md). Their use does not assert
that every statement of either generic appendix is formalized here.

Prerequisite reuse comes from commit `7d496c5f546d4301da35c1995af5a77694874155`.
`Prerequisites` selects definitions from Chapter 2's `Basic`,
`OrthantRepresentation`, `Monotonicity`, `ConvexPreference` and `ConcaveUtility`.
The eleven `Representation*` modules preserve the transitive dependency closure
of `GeneralContinuousRepresentation`, with local imports, namespace and
attribution changes only. `PrimitivePreferences` bridges their definitions to
this chapter and derives continuous utility from rational continuous preferences.
`HomotheticDemand` additionally adapts the homotheticity definition and elementary
scaling identities from the same Chapter 2 revision.
`PrimitiveConvexChoice` adapts Chapter 2's two Proposition 2.6 menu lemmas and
specializes them to budgets. Its uniqueness theorem derives existence from rational
continuous preference and requires no supplied utility representation or maximizer.

The prose motivating constant prices, resale, household services, saving and
the interpretation of a one-time shopping expedition is explanatory discussion,
not additional numerical propositions. Constructed examples are identified as
such and are never attributed to the book as printed formulas.
