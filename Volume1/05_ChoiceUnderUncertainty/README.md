# Kreps Chapter 5: Choice under Uncertainty, in Lean

This independent project covers printed pp. 79–122. Its [source map](docs/source-map.md)
connects Kreps's models and problems to their Lean statements. The frozen audit passed **276 theorems and 415 named declarations across 42
modules**, including attributed prerequisites. All 14 verifier tests passed.
The [verification record](verification/verification.json) includes the checked
source hashes and transitive axioms.

The main results derive expected utility from primitive preferences on mixtures,
including when the alternatives have no best or worst element. Applications cover
finite-support lotteries on arbitrary prize spaces, Borel probability measures and
state-contingent acts. The proof of subjective expected utility identifies the
probabilities whenever the common prize utility takes at least two values.

[Return to the library index](../../README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ActSeparability](ChoiceUnderUncertainty/ActSeparability.lean) | 5 | Acts, state separability and the Sure-Thing Principle |
| [Basic](ChoiceUnderUncertainty/Basic.lean) | 5 | Choice, preference, and utility |
| [StrictPreference](ChoiceUnderUncertainty/StrictPreference.lean) | 12 | Strict preference and indifference |
| [MixtureSpace](ChoiceUnderUncertainty/MixtureSpace.lean) | 4 | Mixture spaces and their preference axioms |
| [SimpleLottery](ChoiceUnderUncertainty/SimpleLottery.lean) | 5 | Finite-support lotteries and expected utility |
| [AffineUniqueness](ChoiceUnderUncertainty/AffineUniqueness.lean) | 5 | Positive affine uniqueness of mixture and prize utilities |
| [MixtureAlgebra](ChoiceUnderUncertainty/MixtureAlgebra.lean) | 1 | Algebra of a binary mixture segment |
| [Independence](ChoiceUnderUncertainty/Independence.lean) | 6 | Background substitution and equally spaced comparisons |
| [ProbabilityGrids](ChoiceUnderUncertainty/ProbabilityGrids.lean) | 7 | Preferences on probability grids |
| [SegmentOrder](ChoiceUnderUncertainty/SegmentOrder.lean) | 11 | Order on a mixture segment |
| [SegmentCalibration](ChoiceUnderUncertainty/SegmentCalibration.lean) | 3 | Calibration on a preference segment |
| [BoundedCalibration](ChoiceUnderUncertainty/BoundedCalibration.lean) | 6 | Affine utility calibrated between two anchors |
| [UnboundedCalibration](ChoiceUnderUncertainty/UnboundedCalibration.lean) | 4 | Calibration without global best and worst alternatives |
| [LotteryEvaluation](ChoiceUnderUncertainty/LotteryEvaluation.lean) | 1 | Recovering a prize index from an affine lottery index |
| [MixtureRepresentation](ChoiceUnderUncertainty/MixtureRepresentation.lean) | 4 | The mixture-space and expected-utility theorems |
| [AlternativeMixtureAxioms](ChoiceUnderUncertainty/AlternativeMixtureAxioms.lean) | 8 | Strict independence and the Archimedean mixture axiom |
| [AlternativeRepresentation](ChoiceUnderUncertainty/AlternativeRepresentation.lean) | 4 | Equivalence of the two mixture axiom systems |
| [StateComparisons](ChoiceUnderUncertainty/StateComparisons.lean) | 7 | Local comparisons and uniqueness of additive state utilities |
| [HorseLotteries](ChoiceUnderUncertainty/HorseLotteries.lean) | 6 | Horse lotteries and state-dependent expected utility |
| [SubjectiveLotteries](ChoiceUnderUncertainty/SubjectiveLotteries.lean) | 7 | Subjective probabilities and state-independent prize utility |
| [AnscombeAumann](ChoiceUnderUncertainty/AnscombeAumann.lean) | 2 | The two Anscombe–Aumann representations |
| [MeasureMixtures](ChoiceUnderUncertainty/MeasureMixtures.lean) | 5 | Mixtures of Borel probability measures |
| [AtomicDensityLaws](ChoiceUnderUncertainty/AtomicDensityLaws.lean) | 10 | Finite atomic and compact-density probability laws |
| [AtomicDensityCounterexample](ChoiceUnderUncertainty/AtomicDensityCounterexample.lean) | 8 | A mixture-affine utility with no expected prize utility |
| [AtomicDensityMixtures](ChoiceUnderUncertainty/AtomicDensityMixtures.lean) | 5 | Normalizing the two components of the mixed-law example |
| [WeakApproximation](ChoiceUnderUncertainty/WeakApproximation.lean) | 5 | Approximating Borel probabilities by lotteries of finite support |
| [WeakUtilityContinuity](ChoiceUnderUncertainty/WeakUtilityContinuity.lean) | 5 | Weak continuity and bounded affine utility |
| [BorelExpectedUtility](ChoiceUnderUncertainty/BorelExpectedUtility.lean) | 4 | Expected utility on all Borel probability measures |
| [FiniteLotteryTables](ChoiceUnderUncertainty/FiniteLotteryTables.lean) | 5 | Finite lottery diagrams |
| [EmpiricalCritiques](ChoiceUnderUncertainty/EmpiricalCritiques.lean) | 12 | Framing, Allais, Ellsberg, portfolio effects and timing |
| [CompoundExamples](ChoiceUnderUncertainty/CompoundExamples.lean) | 8 | Compound lotteries and the order of randomization |
| [EventSimpleActs](ChoiceUnderUncertainty/EventSimpleActs.lean) | 8 | Simple acts on an algebra of state events |
| [EventDecomposition](ChoiceUnderUncertainty/EventDecomposition.lean) | 12 | Event contributions of affine utility on simple acts |
| [EventProbabilities](ChoiceUnderUncertainty/EventProbabilities.lean) | 8 | Conditional utility and finitely additive subjective odds |
| [EventSubjectiveUtility](ChoiceUnderUncertainty/EventSubjectiveUtility.lean) | 5 | A common utility and subjective probabilities on an event algebra |
| [CountablyAdditiveEvents](ChoiceUnderUncertainty/CountablyAdditiveEvents.lean) | 8 | The countably additive extension in the invitation on page 122 |
| [SubsetLotteries](ChoiceUnderUncertainty/SubsetLotteries.lean) | 8 | Lotteries over entire subsets and lotteries over inclusion marginals |
| [NumericalExercises](ChoiceUnderUncertainty/NumericalExercises.lean) | 9 | The five calculations in Problem 5.1 |
| [ExerciseDomains](ChoiceUnderUncertainty/ExerciseDomains.lean) | 12 | Representations on alternative prize spaces |
| [LotterySupport](ChoiceUnderUncertainty/LotterySupport.lean) | 3 | The support of a compound lottery |
| [StateExamples](ChoiceUnderUncertainty/StateExamples.lean) | 16 | State-contingent examples and probability calibration |
| [UnboundedPrizeUtility](ChoiceUnderUncertainty/UnboundedPrizeUtility.lean) | 7 | The countable lottery and Gaussian example on page 100 |

## Build and verify

From this chapter directory, run the pinned Lean and Mathlib environment and the
unchanged verifier.

```sh
lake exe cache get
python -m unittest discover -s scripts -p 'test_*.py' -v
python scripts/verify.py
```

The verifier checks all declared modules, recompiles their source and audits every
named declaration's axioms. See the [corrections](docs/corrections.md) and
[third-party notices](THIRD_PARTY_NOTICES.md) for source conventions and provenance.
