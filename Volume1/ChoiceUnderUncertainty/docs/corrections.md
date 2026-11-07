# Chapter 5 source qualifications

## State-dependent and state-independent utility on p. 84

The final umbrella/lotion sentence refers to equation (5.2) where the discussion
calls for (5.1). Equation (5.2) evaluates each prize with one common index. State
specific valuations in (5.1) can distinguish acts that (5.2) evaluates alike in
this example. `umbrella_stateIndependent` and `umbrella_stateDependent` give the
two calculations.

## Support at an endpoint on p. 87

The footnote qualifies the union-of-supports rule. At an interior probability,
`lottery_mix_support` gives exactly the union. `lottery_endpoint_supports` gives
the selected lottery's support at probabilities zero and one.

## Mixture axioms and utility uniqueness on pp. 88–101

Part (b) of Propositions 5.3 and 5.4 uses strict comparison at any fixed weight,
including zero and one. Part (c) requires both strict inequalities for every
weight strictly above the interior threshold, including one. The numerical
representation of weak preference uses a weak inequality. The alternative strict
independence in Proposition 5.11 uses only interior weights. The Lean statements
retain the distinctions visible in print that can be lost in OCR.

The calibrated unit and zero alternatives in Problem 5.3 can be any strictly
ranked pair. Global extrema are used only for the bounded illustration.
`problem_5_3` glues calibrations on bounded preference intervals to prove the
unrestricted result. A constant utility treats the case of universal indifference.

## Borel probabilities, finite states and null events

Proposition 5.10 uses the weak topology on actual probability measures and a
bounded continuous prize index. There is no boundedness condition on the prize
index of a simple lottery. Bochner integrals in the proof agree with ordinary
expectations by the proved integrability of the bounded continuous functions.
The unbounded-loss illustration uses extended nonnegative integration to record
infinite expected loss.

Proposition 5.13 assumes a nonempty finite state space so that probabilities can
sum to one. Positivity at every state follows in the constructed representation.
The probabilities are identified if the prize utility is nonconstant. Problem
5.6 instead permits null events. Its calibrating pair must be globally strictly
ranked and weakly ordered on each event. Dropping the latter premise can yield a
negative event weight as `event_sign_counterexample` shows.

## Allais on p. 111 and exercise cross-references

The first displayed Allais inequality prints 2,400 on its right side. Figure 5.9
and the ensuing two equations use the sure payoff 24,000. `AllaisLotteries` and
`allais_difference` use 24,000. The discussion referenced in Problem 5.4 as
beginning on p. 119 appears on pp. 105–106. The nonsimple-lottery discussion
referenced on p. 122 appears on pp. 97–100.
