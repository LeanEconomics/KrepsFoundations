# Appendix prerequisites for Chapter 3

This inventory separates the appendix results used by Chapter 3 from the full
appendices. It does not claim complete formalization of Appendices 4 or 5.
The final chapter build, fresh elaboration and all-declaration axiom audit passed;
see [verification](../verification/verification.json).

| Source | Chapter support | Coverage and conventions |
| --- | --- | --- |
| A4.1, p. 471 | `LocalCompactBound` | Local compact containment; equivalent to the needed finite-dimensional bounded-container condition. Budget containment is proved explicitly. A general bounded-neighborhood equivalence is not yet supplied. |
| A4.2, pp. 471–472 | `SequentialUpper`, `SequentialLower` | The original sequential conventions, with eventual membership for lower continuity. Upper continuity means preservation of graph limits. |
| A4.3–4, pp. 472–473 | `SequentialUpper.isClosed`, `SequentialUpper.isCompact` | Closed fibers and compact fibers under a local compact bound. A separate general graph-closedness equivalence remains outside the current support API. |
| A4.5–6, pp. 475–476 | `continuous_of_singleton_correspondence` | Singleton upper continuity plus local compact bounds gives continuity; Mathlib supplies the open-set singleton bridge. |
| A4.7, pp. 476–477 | `maximum_theorem_auxiliary`, `maximum_theorem` | Nonempty maxima, sequential upper continuity, local compact bounds and continuous value. The auxiliary correspondence may differ from the feasible correspondence. Nonempty auxiliary fibers are explicit, matching the source proof's convention. |
| A4.7 supremum convention | `SameObjectiveUpperBounds`, `sameObjectiveUpperBounds_iff_value_eq` | Equality of all real upper bounds avoids totalized `Real.sSup` on unbounded or empty sets. The formal bridge proves equality with the printed real suprema for nonempty bounded objective ranges. |
| A4.8, p. 477 | `proposition_3_3b_unique` | Relative continuity of a unique demand selection on arbitrary parameter subsets; this includes the relatively open sets in the source. |
| A5, pp. 479–484 | `ConstrainedOptimization`, `ConcaveSupport`, `LinearBudgetMultipliers` | Boundary-compatible directional necessity, the concave tangent inequality and finite-budget multiplier construction. `CalculusOptimality` proves the consumer specialization, including actual right-coordinate derivatives and the full multiplier equivalence. |

A4.9–10, appendix illustrations and appendix exercises are not claimed covered by
these prerequisite lemmas. The general nonlinear-constraint LICQ theorem A5.3,
quasi-convex-constraint sufficiency A5.4, and general A5.5 are not replaced by the
linear-budget specialization. Their general statements remain separate appendix
obligations. Chapter 3's results can be proved directly without assuming those
more general theorems.

The informal value-function discussion on p. 482 explicitly declines to give a
precise general differentiability theorem; it is not asserted as an unconditional
uniqueness/differentiability equivalence here.
