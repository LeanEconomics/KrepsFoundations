# Source conventions and qualifications

This file records mathematical interpretation issues separately from unfinished
work, which appears in the [source map](source-map.md).

- **Nonnegative domains and weak inequalities, pp. 50–59.** The PDF's text
  extraction drops equality strokes. Budgets use `p·x ≤ y`, bundles satisfy
  `x ≥ 0`, and the multiplier in Definition 3.4 satisfies `λ ≥ 0`. Only the
  calculus necessity theorem assumes positive income. The general consumer
  problem and Berge theorem include zero income.
- **Boundary derivatives, pp. 57–59.** The calculus statements use an actual
  derivative within the nonnegative orthant. A coordinate-direction theorem
  identifies the right-hand marginal at boundary consumption. No differentiable
  extension outside the consumption domain is assumed.
- **Cobb–Douglas, pp. 59–60.** Positive exponents need not sum to at most one.
  The full-domain demand proof therefore compares logarithmic utilities at
  positive bundles and treats zero factors separately; it does not silently
  assert concavity of an unnormalized product. The replacement for the p. 60
  argument is: take logs on the positive orthant; weighted-log utility is concave
  for arbitrary positive exponents and has the same optimum, with boundary product
  values handled separately.
- **Ordinary logarithms, Problem 3.3.** Ordinary logarithms are undefined at
  zero. `PositiveLogDemand` restricts the logarithmic menu to strictly positive
  consumption. It does not use Lean's totalized `Real.log 0` as a boundary
  economic utility. At positive income this problem has the same unique demand
  as full-domain Cobb–Douglas. At zero income the logarithmic menu is empty,
  while the Cobb–Douglas problem chooses the origin.
- **Exact decimal, Problem 3.4.** Income 16.4 is the rational number 82/5.
- **Zero shifts, Problem 3.5.** Nonnegative shifts include zero. A zero product
  factor is handled directly, while the candidate's shifted quantities are
  proved positive before logarithmic comparisons are made.

- **Marginal ratios, pp. 61–62.** Cross-multiplied identities apply even when
  both marginal utilities vanish. Ratios of marginal utilities require a nonzero
  denominator. The book's informal discussion of `0/0` is not encoded as an
  arbitrary real number.
- **CES, Problem 3.7.** For negative exponents, utility is explicitly zero
  whenever any coordinate is zero. `CESContinuity` proves this is the continuous
  extension of the interior formula. The exponent-zero limit is a demand limit;
  no finite limit of unnormalized utility is asserted without normalizing the
  coefficients.
- **Marginal curves, Problems 3.8–3.9.** Strictly concave increasing scalar utility
  need not have marginal utility tending to zero. The graph-intersection theorem
  states the exact existence condition. Quasilinear demand includes the case
  where no finite numeraire target exists. At zero income the allocation is
  uniquely zero although the common graph height need not be unique.
- **Homothetic scaling, Problem 3.10.** Positive source income is required to
  recover demand by an income ratio. Zero target income is allowed. With one
  strictly increasing good, preferences are homothetic even with a positive
  shift; the zero-shift necessity theorem therefore assumes at least two goods.
- **One-sided derivatives, Problem 3.13.** Coordinate derivatives alone do not
  justify a multivariate linear approximation or common-multiplier conditions.
  The chapter proves actual coordinate necessary inequalities and actual-path
  derivative tests. A separate continuous counterexample demonstrates the
  limitation of substituting partials into the classical conditions. The source
  exercise asks for necessary conditions and does not assert that invalid
  substitution.
- **Chosen sufficient assumptions, Problem 3.14.** The exercise expressly asks
  for assumptions giving existence, convexity, uniqueness and continuity.
  The implementation chooses continuous real functions `f` and `U`; their
  monotonicity and concavity assumptions are restricted to nonnegative planting
  and consumption. The literal objective and the closed interval `[0,e]` are
  preserved, including `e=0`. Two different primitive strictness packages give
  uniqueness and hence lower semicontinuity.
