# Appendix 3 source map

David M. Kreps, *Microeconomic Foundations I*, Appendix 3, printed pp. 452–468.
Lean names below are relative to `Kreps.PreferenceProperties` unless marked Mathlib.
The source inventory covers the entire appendix. The implemented scope is the convex-set,
concavity and quasi-concavity foundation for Chapters 1–2: A3.1–A3.7 and A3.16–A3.23.
Later applications of separation, supporting functionals and calculus are listed explicitly
as deferred; their presence in this inventory does not claim their formalization.

## Convex sets

| Source | Mathematical content | Lean interface and status |
| --- | --- | --- |
| Definition A3.1, p. 452 | Closure under two-point convex combinations | `definition_A3_1` in `AppendixConvexSets`; equivalent to Mathlib `Convex ℝ S`. The empty-set convention is Mathlib `convex_empty`. |
| Proposition A3.2, p. 453 | Closure under arbitrary finite convex combinations | `proposition_A3_2`; explicit finite index set, nonnegative weights and total weight one; uses Mathlib `Convex.sum_mem`. |
| Proposition A3.3, p. 453 | Arbitrary intersections preserve convexity | `proposition_A3_3`; uses Mathlib `convex_sInter`, including an empty family. |
| Definition A3.4, p. 453 | Smallest convex and smallest closed convex superset | `definition_A3_4_convexHull`, `definition_A3_4_closedConvexHull`; both universal properties, using `convexHull` and `closedConvexHull`. The source uses A3.4 for both a definition and a proposition. |
| Proposition A3.4, p. 453 | Convex hull equals the set of finite convex combinations | `proposition_A3_4`; finite type, weights, points, normalization and weighted-sum equality. Uses Mathlib `mem_convexHull_iff_exists_fintype`. |
| Proposition A3.5, pp. 454–455 | Carathéodory: dimension plus one points suffice | `proposition_A3_5`; supplies a finite subset of cardinality at most `Module.finrank ℝ E + 1` containing the point in its hull. `mem_finiteMixtureSet_of_mem_finset_hull` supplies explicit normalized weights. Uses Mathlib's minimal-cardinality affine-independent construction. |
| Proposition A3.6, p. 455 | The convex hull of a compact set is compact in finite dimension | `proposition_A3_6` in `AppendixConvexHullCompact`; a new proof via bounded mixture length and continuous images of compact weight and point parameter sets. Includes the empty set. |
| Illustration, p. 456 | A closed unbounded set can have a nonclosed convex hull | Source illustration inventoried; its particular hyperbola example is not formalized in the Chapters 1–2 foundation. |
| Proposition A3.7, p. 456 | The closure of a convex set is convex; closing a convex hull gives the closed convex hull | `proposition_A3_7_closure`, `proposition_A3_7_closedHull`; uses Mathlib `Convex.closure` and `closedConvexHull_eq_closure_convexHull`. |
| Definition A3.8, p. 456 | Extreme points | Available in Mathlib `Set.extremePoints`, `mem_extremePoints`; no new chapter interface needed. |
| Theorem A3.9 and following corollary, pp. 456–457 | Finite-dimensional Krein–Milman; representation using extreme points | Deferred. Mathlib `closure_convexHull_extremePoints` proves the closed-hull version. The source's finite-dimensional hull equality and the ensuing extreme-point Carathéodory corollary require a further finite-dimensional argument; they are not claimed from the closed-hull theorem alone. |

## Separation and support

| Source | Mathematical content | Existing foundation and remaining work |
| --- | --- | --- |
| Proposition A3.10, p. 457 | Weak separation of disjoint nonempty convex sets | Deferred. Mathlib `geometric_hahn_banach_of_nonempty_interior` provides the nonempty-interior case; the source's unrestricted finite-dimensional statement also needs the lower-dimensional case. |
| Proposition A3.11, p. 458 | Strict separation when both sets are closed and one is compact | Deferred interface. Mathlib `geometric_hahn_banach_compact_closed` and `geometric_hahn_banach_closed_compact` provide separated continuous linear functionals; nonemptiness supplies nonzero separation, and a finite-dimensional coordinate bridge supplies the stated vector. |
| Definition A3.12, p. 458 | Boundary as closure intersected with complement closure | Mathlib `frontier` and `frontier_eq_closure_inter_closure`; no new definition needed. |
| Proposition A3.13, p. 458 | Supporting hyperplane at a convex set's boundary point | Deferred. Mathlib `geometric_hahn_banach_of_nonempty_interior_point` is the interior-case foundation; the degenerate affine-span case remains part of the full source interface. |
| Proposition A3.14, pp. 459–460 | Closed convex sets equal intersections of containing closed half-spaces | Deferred interface. Mathlib `RCLike.iInter_halfSpaces_eq'` supplies the corresponding continuous-linear-functional statement, including empty and universal sets. |
| Support-function definition and Proposition A3.15, pp. 460–461 | Recover a closed convex set from its support function | Deferred. Build on separation and an extended-real supremum, with `−∞` for the empty set and `+∞` for an unbounded support direction. No finite real supremum convention is substituted for these cases. |
| Following remark, p. 461 | Support functions are convex and degree-one homogeneous | Deferred along with the extended-real support-function definition; used later in Chapters 9–10. |

## Convex, concave and quasi-concave functions

| Source | Mathematical content | Lean interface and status |
| --- | --- | --- |
| Definition A3.16a, p. 461 | Concavity and strict concavity | Chapter 2 `ConcaveUtility`, `StrictlyConcaveUtility`; bridges `concaveUtility_iff_concaveOn` and `strictlyConcaveUtility_iff_strictConcaveOn` identify these with Mathlib. |
| Definition A3.16b, p. 461 | Convexity and strict convexity | Mathlib `ConvexOn` and `StrictConvexOn`; negation equivalences supply the concave counterparts. |
| Proposition A3.17a, p. 461 | Affine functions are convex and concave | `proposition_A3_17a` in `AppendixConvexFunctions`. |
| Proposition A3.17b, p. 462 | Finite minima and nonnegative weighted affine compositions preserve concavity | `proposition_A3_17b_min`, `proposition_A3_17b_sum`, `concaveOn_finite_sum`. Minima use a nonempty finite family. The affine-composition theorem explicitly requires that transformed arguments lie in the original domain. |
| Proposition A3.17c, p. 462 | Finite maxima and nonnegative weighted compositions preserve convexity | `proposition_A3_17c_max`, `proposition_A3_17c_sum`, `convexOn_finite_sum`; the composition theorem allows general affine maps, which includes the text's scalar rescalings. |
| Proposition A3.17d–e, p. 462 | Upper contours of concave functions and lower contours of convex functions are convex | `proposition_A3_17d`, `proposition_A3_17e`; weak contour inequalities. |
| Proposition A3.17f, p. 462 | Concavity iff convexity of the negative | `proposition_A3_17f`. |
| Proposition A3.17g, pp. 462–463 | Interior continuity in finite dimension | `proposition_A3_17g_concave`, `proposition_A3_17g_convex`; no boundary continuity is asserted. Uses Mathlib's local-Lipschitz-based continuity theorem. |
| Definition A3.18a–c, p. 464 | Quasi-, strict quasi- and semi-strict quasi-concavity | Shared Chapter 2 definitions `QuasiConcaveUtility`, `StrictlyQuasiConcaveUtility`, `SemiStrictlyQuasiConcaveUtility`. |
| Definition A3.18d–e, p. 464 | Quasi-convexity and strict quasi-convexity | `QuasiConvexUtility`, `StrictlyQuasiConvexUtility` in `AppendixConvexQuasiConcavity`. |
| Proposition A3.19 and footnote, pp. 464–465 | Quasi-concavity iff convex upper contours; dual statement for lower contours | `proposition_A3_19`, `proposition_A3_19_quasiConvex`; bridges the mixture definitions to Mathlib contour definitions. |
| Proposition A3.20, p. 465 | Nondecreasing transformations preserve quasi-concavity; strictly increasing transformations preserve strict quasi-concavity | `proposition_A3_20`, `proposition_A3_20_strict`; the weak statement only requires `Monotone`, not `StrictMono`. |
| Proposition A3.21, p. 465 | Convexity of maximizers; uniqueness under strict quasi-concavity | `proposition_A3_21`, `proposition_A3_21_ambient`, `proposition_A3_21_unique`; arbitrary convex menus and potentially empty maximizing sets. |
| Proposition A3.22, p. 465 | Concavity implies semi-strict quasi-concavity; strict concavity implies strict quasi-concavity | `proposition_A3_22_concave`, `proposition_A3_22_strict`; reuse the Chapter 2 proofs. |
| Proposition A3.23, p. 466 | Concavity iff convexity of the hypograph | `proposition_A3_23`; the epigraph counterpart is `convexOn_iff_convex_epigraph_appendix`. |

## Subgradients and calculus

| Source | Mathematical content | Scope and available foundation |
| --- | --- | --- |
| Definition A3.24, p. 466 | Supporting affine minorants and majorants | Deferred; source uses an affine function touching at the given point and bounding the function on its full domain. |
| Proposition A3.25, pp. 466–467 | Supergradients exist at interior points of a concave domain; lower-envelope representation | Deferred. Convexity of the hypograph is now covered by `proposition_A3_23`; the supporting-functional construction and normalization remain. |
| Proposition A3.26, p. 468 | Supporting affine functions of degree-one homogeneous functions have zero intercept | Deferred. A future wrapper must allow cones without their vertex and use positive scalar rescaling, as the appendix states. |
| Proposition A3.27, p. 468 | One-sided derivatives, monotonicity, countably many nondifferentiability points and the integral formula | Deferred; intended for Chapter 12. Mathlib `Analysis.Convex.Deriv` provides one-sided derivative existence, slope comparisons and monotonicity. The full countability and integration statement is not claimed here. |
| Proposition A3.28, p. 468 | Hessian criteria for concavity and strict concavity | Deferred with a source correction below. Mathlib `concaveOn_of_deriv2_nonpos` and `strictConcaveOn_of_deriv2_neg` provide relevant one-dimensional sufficient conditions. |

## Source precision and corrections

- **A3.17b–c:** affine changes of arguments need a domain-preservation condition.
  The formal statements expose this implicit requirement rather than evaluating a function
  outside its declared domain.
- **A3.21:** maximizers are defined by comparison with every feasible point. This matches
  the source's intended maximizing set even when the utility range is unbounded or empty.
  The uniqueness proof uses the strict quasi-concavity inequality. It does not use the stronger
  strict Jensen inequality appearing in the printed proof.
- **A3.28:** everywhere negative-definite Hessian is sufficient for strict concavity, but
  it is not necessary. For example, `f(x) = −x⁴` is strictly concave on the real line and
  has second derivative zero at the origin. The source's strict-concavity biconditional
  therefore must not be formalized literally. The corresponding positive-definite
  necessity for strict convexity has the same issue.
- **A3.9:** the infinite-dimensional remark requires a closed convex hull. The source's
  finite-dimensional theorem and Mathlib's general closed-hull theorem are distinguished above.
- **p. 457 linearity footnote:** a real linear map is taken to preserve both addition and
  real scalar multiplication. Additivity alone does not imply real linearity without
  extra regularity; the future hyperplane interfaces will use `LinearMap`/`ContinuousLinearMap`.

## Validation

All four new modules pass the project's normal `lake build` command, with its configured
linters, and contain no placeholders or added axioms:

- `PreferenceProperties.AppendixConvexSets`
- `PreferenceProperties.AppendixConvexHullCompact`
- `PreferenceProperties.AppendixConvexFunctions`
- `PreferenceProperties.AppendixConvexQuasiConcavity`

The modules retain the repository's copyright header, namespace, documentation style and
100-character Lean line limit. Chapter 3 has not been started by this appendix work.
