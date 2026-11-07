# Third-party notices

Original code and documentation are released under Apache 2.0; see `LICENSE`.
Lean, Mathlib and their dependencies retain their upstream licenses.

The verifier and its tests are copied from LeanEconomics/DynamicProgramming,
commit `d39805f553dfb9619271b32bbf858d3162ca7e4e`,
`RecursiveMethods/DeterministicDP/scripts/`, under Apache 2.0. Copyright and
attribution belong to their original contributors. The Lake configuration, dependency
pins and CI conventions follow the same repository.

David M. Kreps, *Microeconomic Foundations I: Choice and Competitive Markets*,
Princeton University Press, ISBN 978-0-691-15583-8, is cited by printed page and result.
Its text and figures are not distributed. The local PDF is excluded from version control.

Original formalization is developed with OpenAI Codex under the user's direction;
mathematical coverage and verification status are recorded separately.

The following whole-module copies preserve earlier chapter proofs in this independent
package. Their module headers record the originating revision. Project imports and
namespaces have been adapted, and the [copy inventory](../../consistency/copies.json)
identifies the source and destination of each file.

- Six Chapter 3 modules come from commit `f9c357ada1d9965dabd9eec694720ba585faf575`:
  `Prerequisites`, `BudgetSets`, `ConsumerProblem`, `CorrespondenceMaximum`,
  `BudgetContinuity` and `IndirectUtility`. They have the prefix `Demand` here and
  the namespace `Kreps.UtilityForMoney.Demand`.
- The Chapter 4 `FiniteMinimum` module comes from the same commit. Its local name
  is `DominanceFiniteMinimum`. It supports the finite concave separation witness
  for Proposition 6.15(b).
- Sixteen Chapter 5 modules come from commit `db0d8dce6618d30395cd02429d614bca59568fe7`:
  `Basic`, `StrictPreference`, `MixtureSpace`, `SimpleLottery`, `Independence`,
  `MixtureAlgebra`, `SegmentOrder`, `ProbabilityGrids`, `SegmentCalibration`,
  `BoundedCalibration`, `UnboundedCalibration`, `LotteryEvaluation`,
  `MixtureRepresentation`, `MeasureMixtures`, `WeakApproximation` and
  `WeakUtilityContinuity`. Their local names have the additional prefix `Lottery`
  and their namespace is `Kreps.UtilityForMoney.LotteryTheory`.

Mathlib’s finite simplex, convexity, derivatives, measure theory and separation
results are imported from the pinned dependency. The construction of the finite
supermartingale coupling in this project uses separation of convex sets.
