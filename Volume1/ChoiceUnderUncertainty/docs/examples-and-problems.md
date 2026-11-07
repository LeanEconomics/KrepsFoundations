# Chapter 5 examples and problems

This inventory follows printed pp. 79–122 of David M. Kreps, *Microeconomic
Foundations I*. A numerical lottery in these modules is a finite-support
probability on its actual prize space. A branch table may list the same prize
twice. Its pushforward combines those probabilities, and
`expectedUtility_branchLottery` proves that this preserves expected utility.
[Finite lottery tables](../ChoiceUnderUncertainty/FiniteLotteryTables.lean)

| Source | Checked statement | Lean source |
| --- | --- | --- |
| Figures 5.1, 5.3 and 5.4, pp. 80, 86 | The Secretariat and Kelso bets give their printed net payoffs, with a refund in a dead heat. State odds 0.59, 0.36 and 0.05 produce both printed laws, and the abstention bet pays zero. An independent pair of valid objective lotteries need not have a common set of race odds. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| Sure-Thing and meals, pp. 82–83 | Changing the common dead-heat payoff from −1 to 2 preserves the ranking of the two printed bets. A constructed three-course utility realizes the contrasting shrimp/steak and melon/veal rankings under the two desserts. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| Advertising, p. 83 | The unresponsive two-state model ranks no advertising strictly higher for every strictly increasing pair of state utilities. In the repaired three-state model the expected *monetary* gain is 4000 times the responsive-state probability minus 1000. The one-quarter threshold uses risk neutrality. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| Umbrella and lotion, p. 84 | Equal chances give a tie under every common prize index. Opposite statewise rankings strictly favor the matched act under state-dependent additive utility. The last reference to (5.2) in the paragraph on (5.1) should read (5.1). | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| Figures 5.2 and 5.5, pp. 85, 87 | The two-good lottery has the printed bundle prizes and weights. For the compound lottery, the reduced law has masses 1/2, 1/30, 1/5 and 4/15. Equality holds as distributions on prizes. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean), [CompoundExamples](../ChoiceUnderUncertainty/CompoundExamples.lean) |
| Mixed discrete/density law, pp. 97–98 | The domain consists exactly of convex mixtures of a simple probability and a continuous, compactly supported density. Singleton probabilities and integrals over measurable sets determine the weighted components. The functional is mixture-affine. It values two dollars for sure at 2 and a constructed smooth density with support closure [3,4] at 1. A prize utility representing all simple lotteries must be positive affine in money, so its integral reverses this comparison. | [Decomposition](../ChoiceUnderUncertainty/AtomicDensityLaws.lean), [mixture parameters](../ChoiceUnderUncertainty/AtomicDensityMixtures.lean), [counterexample](../ChoiceUnderUncertainty/AtomicDensityCounterexample.lean) |
| Unbounded prize utility, p. 100 | An unbounded-below index admits distinct prizes below successive negative powers of two. The constructed countable prize law places mass 1/2^k on prize k, starting at k = 1. Its positive expected utility part is zero and its negative part is infinite. For Gaussian prizes, negative exponential utility is integrable with a closed-form expectation. Finite mixtures of Gaussians also have finite expected utility. | [UnboundedPrizeUtility](../ChoiceUnderUncertainty/UnboundedPrizeUtility.lean) |
| Figures 5.6 and 5.7, pp. 102–103 | Sure lotteries embed the deterministic act. The printed 3/4–1/4 mixture equals the resulting horse-race lottery in all three states, including merged −2 and 6 branches. | [CompoundExamples](../ChoiceUnderUncertainty/CompoundExamples.lean) |
| Steak and chicken, pp. 105–106 | The two 50–50 horse-first mixtures are equal state by state. When a whole dinner plan is the roulette prize, a concrete utility strictly distinguishes the two joint lotteries. A four-equation contradiction rules out an additive representation of the matching-dinner utility itself. | [CompoundExamples](../ChoiceUnderUncertainty/CompoundExamples.lean) |
| World Cup and Figure 5.8, pp. 108–109 | With strictly preferred winnings, the printed comparisons identify an American winning probability above 0.48 and a European one below 0.48. Indifference at arbitrary roulette odds identifies the corresponding subjective probability exactly. The Harsanyi doctrine is an additional assumption about consumers with the same information. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| Framing, pp. 110–111 | The 600-dollar endowment with losses gives exactly the original sure and risky terminal cash laws. A reversal on those identical alternatives is impossible for strict preference. The vaccination-program comparison cited from Chapter 1 is recorded there. | [EmpiricalCritiques](../ChoiceUnderUncertainty/EmpiricalCritiques.lean), [Chapter 1 vaccination frames](../../ChoicePreferenceUtility/ChoicePreferenceUtility/CommentaryExamples.lean) |
| Allais and Figure 5.9, pp. 111–112 | With the printed 27,500 and 24,000 prizes, the differences A−B and A′−B′ coincide for every prize utility. Strict preferences B over A and A′ over B therefore exclude expected utility. The first displayed inequality on p. 111 has 2,400 where Figure 5.9 and both subsequent inequalities require 24,000. | [EmpiricalCritiques](../ChoiceUnderUncertainty/EmpiricalCritiques.lean) |
| Ellsberg, pp. 112–113 | The urn has 100 red balls and 200 blue or green balls. The known odds are 1/3 and 2/3 for every feasible blue count. The reported strict reversal contradicts subjective expected utility for any assigned probabilities and violates Sure-Thing directly. | [EmpiricalCritiques](../ChoiceUnderUncertainty/EmpiricalCritiques.lean) |
| Portfolio and timing, pp. 114–116 | A constructed two-state portfolio illustrates the effect of dependence on existing wealth under concave utility. The three printed contracts record toss, disclosure and payment dates. All have the same terminal monetary comparison with 20,000 for sure when evaluated solely on the final amounts. | [EmpiricalCritiques](../ChoiceUnderUncertainty/EmpiricalCritiques.lean) |

The discussion of laboratory frequencies, hypothetical versus paid choices,
descriptive versus normative applications, and interpretations of risk and
uncertainty concerns empirical evidence and modeling choices. The finite
probability calculations and logical implications above can be checked without
an empirical sampling model.

## Problem 5.1

The acts in Figure 5.10 and conditional lotteries in Figure 5.11 use the
original two-good prizes and printed probabilities. The fourth-root evaluations
are proved equal to the stated exponent 0.25. Strict comparisons use certified
rational bounds on radicals. The `problem_5_1*_preference` theorems derive the
corresponding preference rankings for each specified representation.
[Numerical exercises](../ChoiceUnderUncertainty/NumericalExercises.lean),
[preference rankings](../ChoiceUnderUncertainty/ExerciseDomains.lean)

| Part | Answer, in printed order |
| --- | --- |
| 5.1(a) | Square-root expected utilities are 100, 100 and 110. The third lottery is strictly best and the first two are indifferent. |
| 5.1(b) | State-additive values are 47/5, 46/5 and 12. The ranking is third, first, second. |
| 5.1(c) | Common fourth-root utility and probabilities 1/2, 3/10 and 1/5 give the same strict ranking. |
| 5.1(d) | State-dependent values for the left and right lotteries are 348/25 and 12. The left lottery is strictly preferred. |
| 5.1(e) | The subjective value of the right lottery is √5, strictly above the left lottery. |

## Problems 5.2–5.6

| Source | Checked statement | Lean source |
| --- | --- | --- |
| 5.2, pp. 117–118 | For a nonempty finite state set the two representation classes coincide. Absorb a proposed probability into each state utility, or choose positive uniform probabilities and divide each additive component by its state weight. | [StateExamples](../ChoiceUnderUncertainty/StateExamples.lean) |
| 5.3, p. 118 | The full mixture representation uses a strict reference pair and bounded local calibrations. It includes the case of universal indifference and does not assume global best or worst elements. | [MixtureRepresentation](../ChoiceUnderUncertainty/MixtureRepresentation.lean) |
| 5.4, p. 118 | Roulette before horses gives expected utility on lotteries whose prizes are entire state-contingent acts. The dinner example explains why this permits cross-state complementarity. The relevant earlier discussion is on pp. 105–106. | [ExerciseDomains](../ChoiceUnderUncertainty/ExerciseDomains.lean), [CompoundExamples](../ChoiceUnderUncertainty/CompoundExamples.lean) |
| 5.5, pp. 118–119 | Every subset utility extends to expected utility on lotteries of whole subsets. Binary roulettes give an affine parametrization of the marginal inclusion cube by [0,1] coordinates. After subtracting the empty-subset value, the full cube index is a sum of marginal probabilities times item values. At deterministic vertices it reduces to the sum over included objects. An explicit two-object utility shows why whole-subset lotteries allow more rankings. | [ExerciseDomains](../ChoiceUnderUncertainty/ExerciseDomains.lean), [SubsetLotteries](../ChoiceUnderUncertainty/SubsetLotteries.lean) |
| 5.6(a), pp. 119–120 | A simple act factors through a finite partition of an arbitrary state space with cells in the event algebra. Pairwise intersections refine two partitions. The actual resulting domain is a convex space and the primitive axioms give affine utility and the usual choice of normalizations. | [EventSimpleActs](../ChoiceUnderUncertainty/EventSimpleActs.lean), [EventDecomposition](../ChoiceUnderUncertainty/EventDecomposition.lean), [normalization](../ChoiceUnderUncertainty/EventSubjectiveUtility.lean) |
| 5.6(b,c), p. 121 | Disjoint event contributions add by midpoint affinity. Induction over a finite partition gives the full increment even with different within-cell refinements. Splitting each act over an event and its complement gives the adapted Sure-Thing Principle. | [EventDecomposition](../ChoiceUnderUncertainty/EventDecomposition.lean) |
| 5.6(d,e), pp. 121–122 | Each conditional roulette index is affine and equals the expectation of its sure-prize values. Every event ranking satisfies the primitive mixture axioms. The normalized better prize gives finitely additive odds exactly zero on the calibrating null events. Conditional weak preference gives nonnegativity. Without it the two-state witness has signed weights −1, 2. | [EventProbabilities](../ChoiceUnderUncertainty/EventProbabilities.lean), [signed witness](../ChoiceUnderUncertainty/EventSubjectiveUtility.lean) |
| 5.6(f), p. 122 | The primitive ranking is represented by one event probability and one prize utility on every finite presentation of every doubly simple act. The construction handles null events, and affine uniqueness identifies the proportionality factor on each nonnull event. | [EventSubjectiveUtility](../ChoiceUnderUncertainty/EventSubjectiveUtility.lean) |
| Further invitation, p. 122 | On a sigma-algebra, assume continuity of calibrated event-bet values along increasing events. The resulting finitely additive probabilities generate an actual countably additive probability measure. Integrating statewise roulette utility agrees with every simple partition formula. Dominated almost-everywhere convergence gives a particular extension to limits of simple acts. These are explicit additional continuity and integrability conditions. | [CountablyAdditiveEvents](../ChoiceUnderUncertainty/CountablyAdditiveEvents.lean) |
