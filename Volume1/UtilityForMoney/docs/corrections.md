# Source corrections and domain conventions

## Relative risk aversion on p. 132

The paragraph on proportional gambles states that a nonincreasing certainty-equivalent
rate of return corresponds to a nonincreasing coefficient of relative risk aversion.
The coefficient has to be **nondecreasing**. For positive wealth w, gross return t
has utility U(wt). Its absolute risk aversion with respect to t is the relative risk
aversion at wt divided by t. A lower certainty-equivalent return at higher wealth
therefore corresponds to higher relative risk aversion there. The theorem proves
both directions over all positive wealth levels and all simple lotteries on positive
gross returns. For U(x) = −exp(−x), the relative coefficient is x. This utility has
nonincreasing certainty-equivalent returns and refutes the printed direction.
[RelativeRisk.lean](../UtilityForMoney/RelativeRisk.lean)

## Weak convergence on monetary intervals, pp. 124–125

For bounded continuous utility, weak convergence suffices. For continuous utility
unbounded on its domain, the chapter proves convergence when the lotteries stay in
one compact subset of that domain. On the real line a common bounded support bound
provides such a set.

Footnote 3 also refers to uniformly bounded supports. On an interval missing a finite
endpoint, boundedness alone need not give compact confinement. On the positive real
half-line take U(x) = −1/x. At stage n the lottery pays 1/(n+2) with probability
1/(n+1) and otherwise pays 1. Every prize is at most 1 and the lottery measures
converge weakly to the sure prize 1. Their expected utilities are all −2, while
the limiting utility is −1. This is distinct from the book’s escaping-prize example
for utility unbounded above. [EscapingPrizes.lean](../UtilityForMoney/EscapingPrizes.lean)

## Derivatives, certainty equivalents and monotonicity

- In Propositions 6.8 and 6.12 the monetary interval is nondegenerate. A single
  possible prize carries no comparisons that identify a curvature coefficient.
  The within-interval versions use one-sided derivatives at included endpoints.
  They require smooth utility only on the interval. For shifted lotteries, even
  a one-point or empty overlap is allowed. [IntervalArrowPratt.lean](../UtilityForMoney/IntervalArrowPratt.lean)
  [IntervalWealthShifts.lean](../UtilityForMoney/IntervalWealthShifts.lean)
- In Proposition 6.9 the base wealth admits both positive and negative small
  perturbations. The limit is taken along nonzero stakes. Positive marginal
  utility gives a local certainty equivalent, and the source’s strict increase
  ensures uniqueness whenever the compared prizes lie in the common domain.
  [LocalRiskPremium.lean](../UtilityForMoney/LocalRiskPremium.lean)
- Definition 6.10 gives minus the second derivative divided by the first derivative.
  With positive marginal utility the ratio before negation measures the proportional
  change in marginal utility. The displayed coefficient and inverse-transform formula
  on pp. 129–130 determine the signs. [RiskMeasures.lean](../UtilityForMoney/RiskMeasures.lean)
  [InverseUtilityDerivatives.lean](../UtilityForMoney/InverseUtilityDerivatives.lean)
- In Problem 6.2 the primary argument uses the behavioral definition of constant
  premia on the stated interval. The smooth CARA classification separately gives a
  compatible exponential utility. [BehavioralCalibration.lean](../UtilityForMoney/BehavioralCalibration.lean)

## Distribution functions and couplings

The CDF includes the atom at its argument. The integrated comparison includes
the lower limit itself, where both integrals vanish. In Figure 6.2 the supplement
is final prize minus initial prize. In Proposition 6.15(a) the nonnegative
supplement instead denotes first marginal minus second marginal. These are
consistent sign conventions for the two ways of writing the coupling.
[QuantileCoupling.lean](../UtilityForMoney/QuantileCoupling.lean)
[IntegratedDominance.lean](../UtilityForMoney/IntegratedDominance.lean)

## Income, insurance and investment

- The income in Problem 6.7 is the exact finite decimal 126.948391819. The
  first two optimized utilities agree when rounded to four decimal places.
  The proof of failure of an income index uses strict comparison of their mixture
  with each of those two values, so it needs no exact indifference premise.
  [TimingIncomeLotteries.lean](../UtilityForMoney/TimingIncomeLotteries.lean)
- The strict comparisons in Problem 6.8 require positive income. At zero income
  only the zero bundle is feasible, so all its price lotteries tie.
  [PriceRiskExamples.lean](../UtilityForMoney/PriceRiskExamples.lean)
- Proposition 6.17 allows any real insurance coverage, including negative coverage
  and overinsurance. Proposition 6.18 allows any nonnegative dollar holding of
  the risky asset, so borrowing at the safe rate is permitted. An upper bound
  equal to the investor’s wealth would rule out borrowing. Part (c) of 6.18
  concerns every maximizer if one exists, without an implicit attainment premise.
  [InsuranceOptimality.lean](../UtilityForMoney/InsuranceOptimality.lean)
  [RiskyAssets.lean](../UtilityForMoney/RiskyAssets.lean)
- The two interpretations in Problem 6.14 use different terminal wealth laws.
  The stopped law records bankruptcy permanently, with wealth measured in units
  of 500 dollars. Under bounded increasing utility, equality of the limiting
  expected utility and sure utility alone does not settle finite-horizon choices.
  [StoppedBoundedUtility.lean](../UtilityForMoney/StoppedBoundedUtility.lean)
