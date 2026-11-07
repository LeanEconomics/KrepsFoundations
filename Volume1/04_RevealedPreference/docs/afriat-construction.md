# The Afriat construction

The dependency chain follows Kreps I, pp. 70-73.

1. `MarketData` keeps original incomes and feasibility. Its cross-cost is
   expenditure at the first observation's prices minus that observation's income.
   GARP excludes a slack diagonal through its strict self-cycle, proving budget
   exhaustion before income is replaced by own-bundle expenditure.
2. `StrictSuccessors` is an actual finite set and `RevealedRank` its cardinality.
   Weak chains give subset inclusions; strict chains give proper inclusions under
   GARP. This proves Lemma 4.4's cost comparisons and zero-rank existence.
3. `afriat_of_rank_on_finset` removes the nonempty lowest-rank class and invokes
   strong induction on its proper complement. It retains a fixed rank-order
   certificate: its two cost implications remain valid on subsets, so ranks need
   not be recomputed after restriction.
4. Keep the complement's values and positive multipliers. Give all removed indices
   the minimum of the finitely many retained affine evaluations at removed
   bundles, exactly the source's construction. This attained minimum proves one
   cross-class direction immediately.
5. Strictly positive reverse cross-costs allow positive new multipliers: take a
   finite maximum of the required ratios and one. Equal removed-class values and
   nonnegative within-class costs finish the four cases. If all indices are
   minimal, zero values and unit multipliers solve the system. Empty finite sets
   are included. `lemma_4_5` applies this construction to ranks derived from GARP.
6. `FiniteAffineEnvelope` takes the minimum of the resulting supporting affine
   terms on **all real commodity vectors**. General finite-minimum lemmas prove
   continuity, strict increase and concavity before this specialization.
7. The inequalities give a lower bound at each observed bundle; its own affine
   term gives the reverse bound, so the value is exactly prescribed. Every
   budget-affordable bundle has its corresponding affine term at most this value.
   Thus the minimum rationalizes the entire budget, including unobserved and
   boundary bundles.
8. Restrict to the nonnegative orthant. Continuity, strict monotonicity, convexity
   and local insatiability follow from utility's proved properties. Conversely,
   Lemma 4.1 uses local improvements within strict budgets; rationality transports
   comparisons along chains and rules out a strict cycle.

`proposition_4_3` starts with primitive feasible data and positive dimension. No
utility representation, budget exhaustion, rank certificate, Afriat coefficients,
smoothness, unique demand or attainment of unobserved demand is assumed in its
GARP-to-rationalization direction. Empty datasets use a single affine utility.

`PrescribedUtilities` checks explicit coefficients for the source's two possible
rankings in the modified example. `GiffenExample` independently constructs a
two-good utility with unique maximizers; its diagram and numerical optimization
are not used to justify any proof.
