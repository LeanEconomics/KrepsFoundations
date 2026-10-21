# The additive-representation construction

This proof guide concerns the existence direction of Kreps I, Proposition 2.14,
p. 42, and the additive row of Problem 2.1. Kreps refers the difficult existence
proof to Debreu (1960). The reverse implication is the short finite-sum proof
`proposition_2_14_additive` in `AdditiveSeparability.lean`.

Status: complete. `proposition_2_14_exists` proves the general block theorem;
`proposition_2_14_orthant` gives the original commodity-partition theorem.
`table_additive` and `table_continuous_additive` complete the corresponding
existence entries in Table 2.1. The full chain is included in the chapter audit.

## Starting assumptions

The source statement concerns continuous preference on a nonnegative commodity
orthant, strongly separable across a partition of commodities, with at least three
nontrivial blocks. Preference completeness and transitivity are explicit as
`Rational` in the formal statement. Neither a utility representation nor commodity
monotonicity is an input to the original-domain theorem.

The general continuous-representation theorem supplies an initial continuous
utility. Baseline block scores and strong separability then factor it through a
finite product of real interval ranges. The scalar aggregator is continuous and
strictly increasing in the product order. This monotonicity concerns preference
ranks; it does not require more of every original commodity to be preferred.

## Local cardinal scales

`BisymmetricMeanRanks`, `BisymmetricArithmeticMean` and `BisymmetricMeanScale`
construct a continuous strictly increasing scale from dyadic mean grids. Its
midpoint identity gives additive comparisons on a small interval.
`NormalizedCoordinatePairs` moves normalized scores between active coordinates;
`AllPairsLocalScale` obtains one scale for all pairs and all surrounding contexts.
`FiniteSumTransfers` and `PairSumRepresentation` turn pair comparisons into a
representation on the entire local finite product. `LocalScalarChart` and
`ScalarAdditiveChart` provide an actual additive chart at every interior bundle.

## Common units and global continuation

Pair-sum uniqueness forces overlapping coordinate scales to have one common
positive affine coefficient. The proof uses continuity and midpoint identities,
not derivatives. For a varying target coordinate, two other essential coordinates
stay near fixed reference values. `CompanionChartCalibration` compares these
companions with a seed chart and normalizes the target transitions to translations.

`AffineIntervalContinuation` globalizes interval charts, normalized on that seed.
`TranslationIntervalAtlas` retains slope one in the normalized transitions.
`GlobalCoordinateScale` retains both companion calibration identities, so that
scales constructed for different target coordinates can be compared in common units.
A shared third essential coordinate supplies the required comparison.

`LocalToGlobalOrder` transports local comparisons along continuous paths with
monotone additive scores. `PairLocalToGlobal` constructs those paths in coordinate
score ranges. Pair comparisons then feed the finite-transfer representation theorem.
`OpenScalarAdditiveExistence` supplies the actual calibrated chart families and
assembles the open-product existence theorem from these results.

## Attained endpoints and inactive factors

An attained endpoint cannot send an interior additive scale to infinity.
`InteriorCoordinateBounds` freezes the other coordinates and uses a strict
companion comparison plus continuity of the original aggregator to prove finite
one-sided bounds. `MonotoneEndpointExtension` and `IntervalEndpointExtension`
construct continuous strictly increasing extensions from those bounds.

`DenseProductRepresentation` checks the strict-comparison step at the boundary.
Continuity alone would only preserve weak limits; an arbitrarily small coordinate
improvement rules out a collapsed strict comparison.
`FullIntervalAdditiveExtension` assembles an actual full-domain representation and
preserves the original interior scale values.

Singleton score ranges are removed by `ActiveScalarUtility` and reinserted with
zero coordinate utilities. `AdditiveScoreLifting` composes the scalar scales with
the original baseline scores. `CommodityPartitionTopology` identifies the product
of the original commodity blocks with the full nonnegative orthant by a
homeomorphism, including disjoint covering families of commodity index sets.

## Verification and scope

The [source map](source-map.md) records which book statements are complete.
The [verification record](../verification/verification.json) identifies the exact
source hashes checked by the unchanged fresh-source and transitive-axiom verifier.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Compilation checks
the encoded claims; the source inventory and this guide separately expose their
relation to the book's assumptions, conclusions and boundary cases.
