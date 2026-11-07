# Kreps Chapter 6: Utility for Money, in Lean

Chapter 6 of Kreps, *Microeconomic Foundations I*, printed pp. 123–147. This independent
Lean/Mathlib `v4.34.0` project covers the numbered results, Problems 6.1–6.14 and the
chapter’s mathematical illustrations. [Return to the library index](../../README.md).

The frozen audit passed **458 theorems and 629 named declarations in 78 modules**
on 2026-11-07. The total includes 150 prerequisite theorems in 23 attributed local
copies from Chapters 3–5. All 14 verifier tests, the complete build, fresh source
elaboration and the declaration axiom audit passed. The generated record includes
the complete source hashes. [Verification record](verification/verification.json).

The [source map](docs/source-map.md) connects the textbook to the proofs. It covers
the Arrow–Pratt comparisons at one-sided interval endpoints, both finite coupling
characterizations of stochastic dominance, income and price lotteries, insurance,
risky investment and the optional stopped-gamble challenge. The
[corrections](docs/corrections.md) include the direction of the relative-risk
comparison on p. 132 and the compactness qualification for weak convergence.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MonetaryLotteries](UtilityForMoney/MonetaryLotteries.lean) | 11 | Lotteries over monetary prizes |
| [ComparativeRisk](UtilityForMoney/ComparativeRisk.lean) | 3 | Comparing risk aversion |
| [RiskMeasures](UtilityForMoney/RiskMeasures.lean) | 5 | Arrow–Pratt risk aversion and power utility |
| [Insurance](UtilityForMoney/Insurance.lean) | 6 | Insurance at fair and unfair premiums |
| [RiskyAssets](UtilityForMoney/RiskyAssets.lean) | 10 | Demand for a risky asset |
| [ArrowPrattComparison](UtilityForMoney/ArrowPrattComparison.lean) | 3 | Marginal utility ratios and comparison of risk aversion |
| [LocalRiskPremium](UtilityForMoney/LocalRiskPremium.lean) | 5 | Risk premium of a small symmetric gamble |
| [ArrowPrattTheorem](UtilityForMoney/ArrowPrattTheorem.lean) | 2 | Necessity of the Arrow–Pratt coefficient comparison |
| [WealthShifts](UtilityForMoney/WealthShifts.lean) | 6 | Wealth shifts and absolute risk aversion |
| [WealthRiskClassification](UtilityForMoney/WealthRiskClassification.lean) | 5 | Monotone and constant absolute risk aversion |
| [ConstantAbsoluteRisk](UtilityForMoney/ConstantAbsoluteRisk.lean) | 8 | The constant-absolute-risk-aversion utility family |
| [CARACalibration](UtilityForMoney/CARACalibration.lean) | 7 | The numerical CARA calibration of Problem 6.2 |
| [CARACalibrationPreferences](UtilityForMoney/CARACalibrationPreferences.lean) | 2 | Behavioral calibration and attainability of Problem 6.2 |
| [BehavioralCalibration](UtilityForMoney/BehavioralCalibration.lean) | 4 | Ranking the offers in Problem 6.2 from constant risk premia |
| [PortfolioCases](UtilityForMoney/PortfolioCases.lean) | 7 | Risk-neutral portfolios, arbitrage and uniqueness |
| [CARAPortfolio](UtilityForMoney/CARAPortfolio.lean) | 6 | Investment under constant absolute risk aversion |
| [FiniteCouplings](UtilityForMoney/FiniteCouplings.lean) | 5 | Joint laws of two finite monetary lotteries |
| [CouplingSeparation](UtilityForMoney/CouplingSeparation.lean) | 5 | Finite separation for marginal laws and conditional means |
| [DominanceFiniteMinimum](UtilityForMoney/DominanceFiniteMinimum.lean) | 6 | Finite minima for Afriat's utility construction |
| [StochasticDominance](UtilityForMoney/StochasticDominance.lean) | 4 | Stochastic dominance for finite-support monetary distributions |
| [SupermartingaleCoupling](UtilityForMoney/SupermartingaleCoupling.lean) | 3 | Constructing a supermartingale coupling from second-order dominance |
| [ConditionalRisk](UtilityForMoney/ConditionalRisk.lean) | 3 | Conditional Jensen inequality for stochastic dominance |
| [DemandPrerequisites](UtilityForMoney/DemandPrerequisites.lean) | 1 | Preference and consumption-domain prerequisites |
| [DemandBudgetSets](UtilityForMoney/DemandBudgetSets.lean) | 13 | Budget sets at positive prices |
| [DemandCorrespondenceMaximum](UtilityForMoney/DemandCorrespondenceMaximum.lean) | 13 | Correspondences and parametric maxima |
| [DemandBudgetContinuity](UtilityForMoney/DemandBudgetContinuity.lean) | 13 | Continuity and local boundedness of the budget correspondence |
| [DemandConsumerProblem](UtilityForMoney/DemandConsumerProblem.lean) | 10 | The consumer's problem and its basic properties |
| [DemandIndirectUtility](UtilityForMoney/DemandIndirectUtility.lean) | 10 | Marshallian demand and indirect utility |
| [LotteryBasic](UtilityForMoney/LotteryBasic.lean) | 5 | Choice, preference, and utility |
| [LotteryStrictPreference](UtilityForMoney/LotteryStrictPreference.lean) | 12 | Strict preference and indifference |
| [LotteryMixtureSpace](UtilityForMoney/LotteryMixtureSpace.lean) | 4 | Mixture spaces and their preference axioms |
| [LotteryMixtureAlgebra](UtilityForMoney/LotteryMixtureAlgebra.lean) | 1 | Algebra of a binary mixture segment |
| [LotteryIndependence](UtilityForMoney/LotteryIndependence.lean) | 6 | Background substitution and equally spaced comparisons |
| [LotteryProbabilityGrids](UtilityForMoney/LotteryProbabilityGrids.lean) | 7 | Preferences on probability grids |
| [LotterySegmentOrder](UtilityForMoney/LotterySegmentOrder.lean) | 11 | Order on a mixture segment |
| [LotterySegmentCalibration](UtilityForMoney/LotterySegmentCalibration.lean) | 3 | Calibration on a preference segment |
| [LotteryBoundedCalibration](UtilityForMoney/LotteryBoundedCalibration.lean) | 6 | Affine utility calibrated between two anchors |
| [LotteryUnboundedCalibration](UtilityForMoney/LotteryUnboundedCalibration.lean) | 4 | Calibration without global best and worst alternatives |
| [LotterySimpleLottery](UtilityForMoney/LotterySimpleLottery.lean) | 5 | Finite-support lotteries and expected utility |
| [LotteryLotteryEvaluation](UtilityForMoney/LotteryLotteryEvaluation.lean) | 1 | Recovering a prize index from an affine lottery index |
| [LotteryMixtureRepresentation](UtilityForMoney/LotteryMixtureRepresentation.lean) | 4 | The mixture-space and expected-utility theorems |
| [IncomeChoice](UtilityForMoney/IncomeChoice.lean) | 7 | Income risk resolved before consumption choice |
| [DominanceExample](UtilityForMoney/DominanceExample.lean) | 6 | The two-stage monetary lottery in Figure 6.2 |
| [DominanceInterpolation](UtilityForMoney/DominanceInterpolation.lean) | 4 | Capped-linear tests for second-order dominance |
| [LotteryMeasureMixtures](UtilityForMoney/LotteryMeasureMixtures.lean) | 5 | Mixtures of Borel probability measures |
| [LotteryWeakApproximation](UtilityForMoney/LotteryWeakApproximation.lean) | 5 | Approximating Borel probabilities by lotteries of finite support |
| [LotteryWeakUtilityContinuity](UtilityForMoney/LotteryWeakUtilityContinuity.lean) | 5 | Weak continuity and bounded affine utility |
| [LotteryLimits](UtilityForMoney/LotteryLimits.lean) | 7 | Continuity in lottery probabilities and prizes |
| [DominanceOrders](UtilityForMoney/DominanceOrders.lean) | 6 | The two stochastic dominance orders |
| [EqualProbabilityRisk](UtilityForMoney/EqualProbabilityRisk.lean) | 2 | Equally likely consumption gambles and concavity |
| [EscapingPrizes](UtilityForMoney/EscapingPrizes.lean) | 5 | Weak limits and small-probability monetary prizes |
| [GeneralQuantile](UtilityForMoney/GeneralQuantile.lean) | 3 | Inverse-CDF sampling for general probability laws |
| [ImperfectInsurance](UtilityForMoney/ImperfectInsurance.lean) | 9 | Full coverage with an imperfect fair policy |
| [InsuranceOptimality](UtilityForMoney/InsuranceOptimality.lean) | 5 | Marginal insurance incentives and the unrestricted coverage domain |
| [IntegratedDominance](UtilityForMoney/IntegratedDominance.lean) | 7 | Integrated distribution functions and downside risk |
| [IntervalArrowPratt](UtilityForMoney/IntervalArrowPratt.lean) | 4 | Arrow–Pratt comparison with derivatives within the prize interval |
| [IntervalWealthShifts](UtilityForMoney/IntervalWealthShifts.lean) | 6 | Wealth comparisons at one-sided endpoints |
| [IntervalCARA](UtilityForMoney/IntervalCARA.lean) | 3 | Constant risk aversion on the original monetary interval |
| [InverseUtilityDerivatives](UtilityForMoney/InverseUtilityDerivatives.lean) | 3 | Derivatives on the inverse utility scale |
| [RiskAttitudes](UtilityForMoney/RiskAttitudes.lean) | 6 | Risk attitudes and finite Jensen induction |
| [MonetaryPreference](UtilityForMoney/MonetaryPreference.lean) | 6 | Monetary utility from primitive preferences over lotteries |
| [MultipleRiskyAssets](UtilityForMoney/MultipleRiskyAssets.lean) | 4 | Hedging and dominated risky assets |
| [PriceIncomeRisk](UtilityForMoney/PriceIncomeRisk.lean) | 11 | Joint price and income risk |
| [PriceRiskExamples](UtilityForMoney/PriceRiskExamples.lean) | 11 | Risk in relative prices and the price level |
| [PrizeContinuity](UtilityForMoney/PrizeContinuity.lean) | 2 | Continuity of utility in the monetary prizes |
| [QuantileBins](UtilityForMoney/QuantileBins.lean) | 9 | Finite cumulative probabilities and inverse-CDF bins |
| [QuantileCoupling](UtilityForMoney/QuantileCoupling.lean) | 11 | First-order dominance by common uniform draws |
| [RelativeRisk](UtilityForMoney/RelativeRisk.lean) | 5 | Proportional gambles and relative risk aversion |
| [RepeatedGambles](UtilityForMoney/RepeatedGambles.lean) | 5 | Independent repetitions of the favorable-mean gamble |
| [SmallShares](UtilityForMoney/SmallShares.lean) | 7 | Buying a small share of a favorable gamble |
| [StoppedGambles](UtilityForMoney/StoppedGambles.lean) | 10 | Repeating the gamble with absorption at bankruptcy |
| [StoppedGambleLimits](UtilityForMoney/StoppedGambleLimits.lean) | 3 | Growing horizons under the bankruptcy rule |
| [StoppedRuinProbability](UtilityForMoney/StoppedRuinProbability.lean) | 6 | Limiting bankruptcy probability |
| [StoppedBoundedUtility](UtilityForMoney/StoppedBoundedUtility.lean) | 4 | A limiting criterion for bounded utility in the stopped gamble |
| [TimingExamples](UtilityForMoney/TimingExamples.lean) | 8 | Committing to a consumption quantity before learning income |
| [TimingValueBounds](UtilityForMoney/TimingValueBounds.lean) | 6 | Certified numerical optimum values for precommitted consumption |
| [TimingIncomeLotteries](UtilityForMoney/TimingIncomeLotteries.lean) | 4 | Why income lotteries fail the expected-utility test under precommitment |
| [VaryingSupport](UtilityForMoney/VaryingSupport.lean) | 3 | Changing finite supports and uniformly bounded utilities |

## Verification

From this chapter directory, run:

```sh
lake exe cache get
python -m unittest discover -s scripts -p 'test_*.py' -v
python scripts/verify.py
```

The audit permits `propext`, `Classical.choice` and `Quot.sound`. Chapter-local
names use `Kreps.UtilityForMoney`. Copied demand, lottery and finite-minimum modules
retain their sources in the [third-party notices](THIRD_PARTY_NOTICES.md).
