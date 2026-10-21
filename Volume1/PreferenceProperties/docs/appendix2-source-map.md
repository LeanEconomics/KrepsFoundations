# Appendix 2 source map

Source: Kreps, *Microeconomic Foundations I*, Appendix 2, printed pp. 441–451.
Chapter 2 owns this inventory. Later independent chapter packages can copy the
needed results and record their provenance. A Mathlib import alone does not close
an entry: the book's statement and hypotheses must have an explicit bridge.

| Source | Mathematical obligation | Status |
| --- | --- | --- |
| A2.1, p. 441 | Finite real coordinate spaces, nonnegative and strictly positive orthants | `NonnegativeOrthant`; explicit appendix bridges pending |
| Definition A2.1, pp. 441–442 | Euclidean distance as the square root of the sum of squared coordinate differences; positivity, definiteness, symmetry, scaling, triangle inequality and translation invariance | `definition_A2_1`, `euclidean_distance_properties`, `euclidean_distance_translation` |
| Definition A2.2 and footnote 2, p. 442 | Open balls and their openness | `definition_A2_2`, `appendix2_open_ball` |
| Definition A2.3, p. 442 | Open sets via balls, closed sets via complements; empty and whole spaces are both open and closed | `definition_A2_3_open`, `definition_A2_3_closed`, `appendix2_empty_univ_clopen` |
| Example and footnote 3, p. 442 | `(0,1]` is neither open nor closed; an infinite intersection of opens need not be open | Pending |
| Proposition A2.4, p. 442 | Arbitrary unions and finite intersections of opens; finite unions and arbitrary intersections of closed sets | `proposition_A2_4_open_union`, `proposition_A2_4_open_inter`, `proposition_A2_4_closed_union`, `proposition_A2_4_closed_inter` |
| Relative topology, p. 443 | Subtype open/closed sets as intersections with ambient open/closed sets; ambient conclusions for open/closed domains | `appendix2_relative_open`, `appendix2_relative_closed`; ambient open/closed-domain conclusions pending |
| Definition A2.5, p. 443 | Closure as the least closed superset and interior as the greatest open subset, including intersection/union constructions | `definition_A2_5_closure`, `definition_A2_5_interior`, `appendix2_closure_intersection`, `appendix2_interior_union` |
| Closure/interior exercises, p. 443 | Interior ball characterization, complement duality, subtype closure formula, relative interior of the full domain | `appendix2_interior_ball`, `appendix2_closure_interior_complement`, `appendix2_relative_interior_self`; subtype closure formula pending |
| Equivalent distances, p. 444 | Euclidean, supremum and sum norms; exact `(1,3)` to `(5,0)` distances `5`, `4`, `7`; norm inequalities and common topology | Pending |
| Definition A2.6, p. 445 | Epsilon/eventually definition of sequence convergence | `definition_A2_6` |
| Proposition A2.7, p. 445 | Sequential characterization of openness | `proposition_A2_7` |
| Proposition A2.8, p. 445 | Sequential characterization of closedness | `proposition_A2_8` |
| Sequence examples, pp. 445–446 | Diverging multiples of ten; alternating sequences approaching one and two | Pending |
| Definitions A2.9–A2.10 and exercise, p. 446 | Repeated visits to every neighborhood; strictly increasing subsequence indices; accumulation iff subsequence limit | `definition_A2_9`, `appendix2_accumulation_subsequence` |
| Set accumulation and closure, p. 446 | Closure as the points obtainable as limits of sequences from the set | `appendix2_closure_sequence`, `appendix2_set_accumulation_self`; constant sequences are allowed, as in the book |
| Definition A2.11, p. 446 | Norm boundedness equivalent to uniform coordinate bounds | `definition_A2_11` gives strict norm bounds; coordinate-bound equivalence pending |
| Proposition A2.12, pp. 446–447 | A bounded sequence has an accumulation point; finite-dimensional completeness and the Cauchy criterion | `proposition_A2_12`, `appendix2_cauchy_criterion`, `appendix2_euclidean_complete` |
| Definition A2.13, p. 447 | Closed and bounded iff compact, with the open-cover definition made explicit | `definition_A2_13`, `appendix2_compact_open_cover` |
| Corollary A2.14 and finite-set remark, p. 447 | Compact sequences have accumulation points in the set; every finite set is compact | `corollary_A2_14`, `appendix2_finite_compact` |
| Definition A2.15, p. 447 | Epsilon/delta continuity on the relative domain; uniform and Lipschitz variants in footnote 5 | `definition_A2_15`, `appendix2_uniform_continuity`, `appendix2_lipschitz_uniform`; exact pointwise Lipschitz footnote variant pending |
| Proposition A2.15a–b, p. 448 | Sequential continuity; open and closed preimage characterizations | `proposition_A2_15a`, `proposition_A2_15b_open`, `proposition_A2_15b_closed`; the duplicated printed numbering is retained |
| Proposition A2.16a–d, p. 448 | Continuity under addition, multiplication, division at a nonzero denominator and composition | `proposition_A2_16a`, `proposition_A2_16b`, `proposition_A2_16c`, `proposition_A2_16d` |
| Definition A2.17, p. 448 | Continuous paths between every pair of points | `definition_A2_17` identifies path connectedness, allowing the empty set; the printed term "simply connected" does not assert anything about homotopies |
| Proposition A2.18, p. 448 | Intermediate values on a path-connected domain | `proposition_A2_18` |
| Definition A2.19, pp. 448–449 | Upper/lower bounds; real and extended-real suprema/infima; maxima/minima as attained extrema | `definition_A2_19a`–`definition_A2_19d_min`; `appendix2_extended_sup_finite`, `appendix2_extended_inf_finite` and both unbounded-extremum results |
| Proposition A2.20a–c, p. 449 | Infimum does not exceed supremum; finite extrema for nonempty bounded sets; compact nonempty sets attain both extrema | `proposition_A2_20a`, `proposition_A2_20b`, `proposition_A2_20c`; nonemptiness applies to finite infima as well |
| Empty-set convention, p. 449 | Extended-real `sup ∅ = -∞`, `inf ∅ = +∞` | `appendix2_empty_extrema`, using extended reals |
| Proposition A2.21 and two proofs, pp. 449–450 | Continuous real functions attain a finite supremum on a nonempty compact set; sequence and finite-cover arguments | `proposition_A2_21` proves the common statement of both printed proofs using Mathlib’s compact-image extrema theorem; sequential compactness and finite-open-cover formulations are separately bridged above |
| Definition A2.22 and discussion, p. 450 | Limsup/liminf via tail suprema/infima, monotone tails, infinite cases and extreme accumulation points | Pending; extended-real values are needed for unbounded sequences |
| Proposition A2.23, pp. 450–451 | Equality of liminf and limsup characterizes convergence to their common extended-real value | Pending; finite real convergence requires the common value to be finite |
| Definition A2.24, p. 451 | Epsilon/delta definitions of upper and lower semicontinuity | `definition_A2_24_upper`, `definition_A2_24_lower` |
| Proposition A2.25, p. 451 | Sequential limsup/liminf characterization of semicontinuity | Pending |
| Proposition A2.26 and economic consequence, p. 451 | Upper semicontinuity gives an attained finite maximum and nonempty compact-menu choice | `proposition_A2_26`, `upperSemicontinuous_compact_choice` |
| Final diagnostic, p. 451 | A summable series of closed-set indicators is upper semicontinuous | Printed signed-coefficient claim is false. `appendix2_diagnostic_nonnegative` proves the corrected version. `appendix2_diagnostic_counterexample` satisfies every printed hypothesis and disproves the stated conclusion. |

The motivating prose, reading advice and descriptions of Manhattan distance are
expository. Their mathematical examples and asserted properties remain in the
inventory above. Exact statement bridges may generalize from Euclidean spaces
to metric or topological spaces when the original domains remain special cases.
