# ConsumerDemand

Formalization of Kreps, *Microeconomic Foundations I*, Chapter 3, pp. 50–66.
Definitions, numbered propositions, Problems 3.1–3.14, and mathematical illustrations
are implemented and independently reviewed. The frozen audit passed **455 theorems
and 615 declarations across 65 modules**, including the primitive-convexity API,
with all 14 verifier tests passing.
The [source map](docs/source-map.md) records exact coverage; generated proof checks
and source hashes are in [verification](verification/verification.json). See
[corrections](docs/corrections.md) for domain conventions and qualifications.

This is an independent Lake project pinned to Lean and Mathlib `v4.34.0`.
It uses local attributed copies of prerequisite Chapter 2 material, with no Lake
dependency on another chapter. See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Prerequisites](ConsumerDemand/Prerequisites.lean) | 1 | Preference and consumption-domain prerequisites |
| [BudgetSets](ConsumerDemand/BudgetSets.lean) | 13 | Budget sets at positive prices |
| [ConsumerProblem](ConsumerDemand/ConsumerProblem.lean) | 10 | The consumer's problem and its basic properties |
| [ConstrainedOptimization](ConsumerDemand/ConstrainedOptimization.lean) | 2 | Boundary-compatible first-order conditions |
| [LinearBudgetMultipliers](ConsumerDemand/LinearBudgetMultipliers.lean) | 1 | Multipliers for a linear budget |
| [ConcaveSupport](ConsumerDemand/ConcaveSupport.lean) | 3 | Concave supporting inequalities within the consumption domain |
| [CalculusOptimality](ConsumerDemand/CalculusOptimality.lean) | 9 | Calculus conditions for the consumer's problem |
| [LogarithmicSupport](ConsumerDemand/LogarithmicSupport.lean) | 6 | Strict logarithmic supporting inequalities |
| [ShiftedProductDemand](ConsumerDemand/ShiftedProductDemand.lean) | 5 | Shifted Cobb-Douglas utility, including zero boundary factors |
| [CobbDouglasDemand](ConsumerDemand/CobbDouglasDemand.lean) | 10 | Full-domain Cobb-Douglas demand |
| [BangForBuck](ConsumerDemand/BangForBuck.lean) | 8 | Marginal utility per dollar and expenditure shares |
| [CorrespondenceMaximum](ConsumerDemand/CorrespondenceMaximum.lean) | 13 | Correspondences and parametric maxima |
| [BudgetContinuity](ConsumerDemand/BudgetContinuity.lean) | 13 | Continuity and local boundedness of the budget correspondence |
| [BudgetGeometry](ConsumerDemand/BudgetGeometry.lean) | 3 | Budget vertices and positive bundles |
| [BudgetTriangle](ConsumerDemand/BudgetTriangle.lean) | 2 | The two-good budget triangle |
| [CESSupport](ConsumerDemand/CESSupport.lean) | 3 | Strict support inequalities for CES powers |
| [CESDemand](ConsumerDemand/CESDemand.lean) | 15 | The CES consumer's demand |
| [CESContinuity](ConsumerDemand/CESContinuity.lean) | 7 | Continuity of CES utility at the axes |
| [HomotheticDemand](ConsumerDemand/HomotheticDemand.lean) | 10 | Homothetic preference and income scaling of all demand |
| [CESHomogeneity](ConsumerDemand/CESHomogeneity.lean) | 5 | Homotheticity of CES preferences |
| [LinearDemand](ConsumerDemand/LinearDemand.lean) | 6 | Linear utility and its complete demand correspondence |
| [CESLimits](ConsumerDemand/CESLimits.lean) | 8 | The linear and Cobb-Douglas limits of CES demand |
| [CappedAbsoluteDerivatives](ConsumerDemand/CappedAbsoluteDerivatives.lean) | 2 | One-sided derivatives of a capped absolute value |
| [CommodityTransfers](ConsumerDemand/CommodityTransfers.lean) | 7 | Budget-preserving commodity transfers |
| [DecreasingDemand](ConsumerDemand/DecreasingDemand.lean) | 2 | Strictly decreasing preferences |
| [DemandIllustrations](ConsumerDemand/DemandIllustrations.lean) | 14 | Constructed witnesses for Figure 3.2 |
| [WaterfillingMultiplier](ConsumerDemand/WaterfillingMultiplier.lean) | 4 | Existence of the shifted-product expenditure multiplier |
| [ShiftedDemandProcedure](ConsumerDemand/ShiftedDemandProcedure.lean) | 9 | The shifted-product demand procedure |
| [FiniteShiftedDemand](ConsumerDemand/FiniteShiftedDemand.lean) | 7 | A finite algebraic procedure for shifted-product demand |
| [IndirectUtility](ConsumerDemand/IndirectUtility.lean) | 10 | Marshallian demand and indirect utility |
| [IrrelevantGoods](ConsumerDemand/IrrelevantGoods.lean) | 4 | Unused goods and uniqueness with partial strict convexity |
| [LeontiefDemand](ConsumerDemand/LeontiefDemand.lean) | 9 | Leontief demand without differentiability |
| [LinearLeontiefHomogeneity](ConsumerDemand/LinearLeontiefHomogeneity.lean) | 4 | Homotheticity of linear and Leontief utility |
| [SeparableMarginals](ConsumerDemand/SeparableMarginals.lean) | 10 | Smooth increasing concave component utilities |
| [SeparableDemand](ConsumerDemand/SeparableDemand.lean) | 10 | The marginal-curve graphical procedure |
| [QuasiLinearDemand](ConsumerDemand/QuasiLinearDemand.lean) | 7 | Quasi-linear marginal conditions, including the zero-numeraire corner |
| [QuasiLinearUniqueness](ConsumerDemand/QuasiLinearUniqueness.lean) | 4 | Unique quasi-linear demand |
| [QuasiLinearWealth](ConsumerDemand/QuasiLinearWealth.lean) | 8 | The quasi-linear wealth threshold and its possible absence |
| [MarginalIntersections](ConsumerDemand/MarginalIntersections.lean) | 3 | Existence of finite marginal intersections |
| [OneSidedConditions](ConsumerDemand/OneSidedConditions.lean) | 7 | One-sided necessary conditions |
| [OrdinalDifferentiability](ConsumerDemand/OrdinalDifferentiability.lean) | 5 | Differentiability is not an ordinal property |
| [PartialDerivativeCounterexample](ConsumerDemand/PartialDerivativeCounterexample.lean) | 12 | Coordinate partial derivatives do not imply common multipliers |
| [PositiveLogDemand](ConsumerDemand/PositiveLogDemand.lean) | 5 | The positive-domain logarithmic problem |
| [RepresentationBasic](ConsumerDemand/RepresentationBasic.lean) | 5 | Choice, preference, and utility |
| [RepresentationStrictPreference](ConsumerDemand/RepresentationStrictPreference.lean) | 12 | Strict preference and indifference |
| [RepresentationCountableUtility](ConsumerDemand/RepresentationCountableUtility.lean) | 10 | Countable utility representation |
| [RepresentationContinuousPreference](ConsumerDemand/RepresentationContinuousPreference.lean) | 10 | Continuous preferences |
| [RepresentationOrthantRepresentation](ConsumerDemand/RepresentationOrthantRepresentation.lean) | 5 | Utility representation on the nonnegative orthant |
| [RepresentationMonotonicity](ConsumerDemand/RepresentationMonotonicity.lean) | 17 | Monotonicity and insatiability |
| [RepresentationLexicographic](ConsumerDemand/RepresentationLexicographic.lean) | 3 | Lexicographic preferences have no real utility representation |
| [RepresentationContinuousUtility](ConsumerDemand/RepresentationContinuousUtility.lean) | 5 | Continuous utility and intermediate indifference |
| [RepresentationDensePreferenceRanks](ConsumerDemand/RepresentationDensePreferenceRanks.lean) | 5 | Countable dense ranks for the general continuous-representation theorem |
| [RepresentationRankCutUtility](ConsumerDemand/RepresentationRankCutUtility.lean) | 13 | A bounded utility from dense rational ranks |
| [RepresentationGeneralContinuousRepresentation](ConsumerDemand/RepresentationGeneralContinuousRepresentation.lean) | 5 | The general continuous-representation theorem |
| [PrimitivePreferences](ConsumerDemand/PrimitivePreferences.lean) | 3 | Consumer demand from primitive preferences |
| [PrimitiveConvexChoice](ConsumerDemand/PrimitiveConvexChoice.lean) | 5 | Convexity and uniqueness of choice directly from primitive preferences |
| [PrimitiveChoiceProperties](ConsumerDemand/PrimitiveChoiceProperties.lean) | 2 | Primitive-preference uniqueness with irrelevant goods |
| [ProductHomogeneity](ConsumerDemand/ProductHomogeneity.lean) | 4 | Homotheticity of the explicit demand examples |
| [QuasiconcaveOptimality](ConsumerDemand/QuasiconcaveOptimality.lean) | 3 | Quasi-concave first-order sufficiency |
| [RobinsonCrusoe](ConsumerDemand/RobinsonCrusoe.lean) | 13 | Robinson Crusoe's consumption and planting problem |
| [RobinsonCrusoeConvexity](ConsumerDemand/RobinsonCrusoeConvexity.lean) | 11 | Convexity and two uniqueness routes for Robinson Crusoe |
| [SeparableNonhomothetic](ConsumerDemand/SeparableNonhomothetic.lean) | 7 | Homothetic classification of the smooth separable examples |
| [ShiftedLogExample](ConsumerDemand/ShiftedLogExample.lean) | 4 | The three numerical demands in Problem 3.4 |
| [ShiftedProductHomothetic](ConsumerDemand/ShiftedProductHomothetic.lean) | 4 | Homothetic classification of shifted products |
| [StationaryCubicExamples](ConsumerDemand/StationaryCubicExamples.lean) | 13 | Stationary but strictly increasing utility |

From this directory, run:

```sh
lake build
python -m unittest discover -s scripts -p 'test_*.py' -v
python scripts/verify.py
```

The full build, fresh recompilation and unchanged verifier's transitive-axiom audit
passed on 2026-10-30. Only `propext`, `Classical.choice` and `Quot.sound` occur.
Counts include attributed local prerequisite copies; source fidelity is recorded
separately in the source map and corrections. The
[appendix inventory](docs/appendix-prerequisites.md) distinguishes the foundations
used here from remaining general appendix material.
