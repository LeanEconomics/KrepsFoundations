# Candidates for upstreaming to Mathlib

This inventory follows the evidence-based practice in the inspected
[LeanEconomics UPSTREAM.md](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/UPSTREAM.md).
It records possible reusable contributions, not novelty, acceptance or submission claims.
Searches below were made on 21 October 2026 against the project's pinned Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`). Repeat the search before preparing
an upstream change, since names and coverage can change.

## Candidate: compact convex hulls in finite dimension

Local result:
[proposition_A3_6](Volume1/PreferenceProperties/PreferenceProperties/AppendixConvexHullCompact.lean).

For a finite-dimensional real normed vector space and an arbitrary compact set `S`,
the theorem proves `IsCompact (convexHull ℝ S)`. It includes empty sets.
The proof uses Carathéodory to bound the number of points in a mixture, then takes a
finite union of continuous images of compact sets of weights and point tuples.

The local Mathlib search inspected `Analysis/Convex/Caratheodory.lean`,
`Analysis/Convex/Combination.lean`, `Analysis/Convex/Topology.lean`,
`Analysis/Convex/TotallyBounded.lean`, and `Analysis/Convex/KreinMilman.lean`, and searched
the whole library for compactness/convex-hull combinations. Related existing results are:

- `Set.Finite.isCompact_convexHull`: compact hull of a **finite** set;
- `totallyBounded_convexHull`: preservation of total boundedness, which by itself does
  not establish closedness of the convex hull;
- `closure_convexHull_extremePoints`: the closed-hull form of Krein–Milman;
- Carathéodory's finite affine-independent representation and cardinality bounds.

No direct theorem for the compact hull of an arbitrary compact set was found in that
search. This is a candidate for review, not a guarantee that no equivalent theorem exists.
Before an upstream proposal:

1. Recheck current Mathlib and ask whether an existing result already supplies the API.
2. Move the theorem out of the Kreps namespace, give it a Mathlib-style name, and use
   only mathematical imports. Replace the chapter-numbered Carathéodory wrapper with
   its underlying Mathlib proof.
3. Review whether the fixed-length mixture helpers should reuse the `StdSimplex` API
   or remain private implementation details, and determine suitable generality.
4. Check empty sets, dimension zero, and the necessity of the finite-dimensional
   assumption. Build and audit the proposed standalone module with the target version.

## Useful local APIs, not established gaps

`concaveOn_finite_sum`, `convexOn_finite_sum`, and the weighted affine-composition
interfaces in `AppendixConvexFunctions.lean` package short inductions and existing
`ConcaveOn.add`, `ConvexOn.add`, `smul` and `comp_affineMap` lemmas. Their convenience
does not establish a substantive Mathlib gap. If proposed, discuss naming and whether
the composition belongs in the existing API first.

The polygonal interpolation in `PolygonalCurve.lean` is more general than its economics
application, but it has not received a comprehensive duplication search. It remains a
local helper, not a listed upstream theorem.

## Additional reusable constructions under review

The additive-existence proof also separates several purely mathematical APIs:

- [Interval chart continuation](Volume1/PreferenceProperties/PreferenceProperties/AffineIntervalContinuation.lean)
  globalizes a positive affine atlas on a real interval, with a specified seed chart.
  The translation specialization preserves slope one on every chart.
- [Endpoint extension](Volume1/PreferenceProperties/PreferenceProperties/MonotoneEndpointExtension.lean)
  extends a continuous monotone real function from a dense domain whose only missing
  points are extreme elements. Finite one-sided bounds suffice at attained ends;
  strict monotonicity is preserved on densely ordered domains.
- [Dense comparison transport](Volume1/PreferenceProperties/PreferenceProperties/DenseProductRepresentation.lean)
  shows that continuous strictly increasing utilities on products of densely ordered
  blocks have identical comparisons everywhere when they agree on a dense subset.
- [Local comparison transport](Volume1/PreferenceProperties/PreferenceProperties/LocalToGlobalOrder.lean)
  turns local agreement along monotone paths into global order agreement.

The endpoint search inspected `Topology/DenseEmbedding.lean`,
`Topology/Order/MonotoneConvergence.lean`, `Topology/Order/MonotoneContinuity.lean`,
`Order/Monotone/Extension.lean`, and order-topology closure results. The local proofs
reuse `Dense.extend`, `Dense.continuous_extend`, `tendsto_atBot_ciInf`, and
`tendsto_atTop_ciSup`. Mathlib's bounded monotone extension theorem does not by itself
supply the required continuous extension on possibly unbounded intervals. The path
proof reuses `exists_monotone_Icc_subset_open_cover_unitInterval`.

These are reusable local results, not established Mathlib omissions. Before proposing
any of them, perform a broader duplication search, remove the economics namespace,
review minimal imports and hypotheses, and discuss whether the combined interfaces
are useful beyond this application. No upstream submission has been made.

## Already available in Mathlib

The appendix wrappers for closure of convex sets, closed convex hulls, finite convex
combinations, contour convexity, hypographs, and interior continuity of finite-dimensional
convex/concave functions reuse existing Mathlib theorems. The wrappers improve the book's
source map; they are not candidates merely because the Kreps-numbered names are new.

## Economics-specific material

Preference rationality, revealed choice, ordinal representations, weak and strong
separability, quasi-linear preferences and the recursive utility algorithm are currently
expressed in chapter structures. They belong in the economics formalization. A future
shared economics library may reuse them after comparing definitions and hypotheses;
they are not ready-made Mathlib additions.

## Candidates from Chapters 3–4

The Chapter 3 maximum theorem separates sequential graph closure, feasible recovery,
local compact bounds, nonempty maxima and continuous supremum values. Its auxiliary
correspondence version follows Kreps A4.7. Search at Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435` found useful sequential bridges in
`Topology/Semicontinuity/Hemicontinuity.lean`, compact subsequences in
`Topology/Sequences.lean`, and `Filter.tendsto_of_subseq_tendsto`. These are used
rather than re-proved. A broader search and a review of filter-based formulations
are required before proposing an upstream interface.

`ConcaveSupport` specializes the scalar concave slope inequality along an affine
segment to obtain a Fréchet derivative support inequality within a convex domain,
including boundary points. Existing `Analysis/Convex/Deriv.lean` slope results and
`Analysis/Calculus/LocalExtr/Basic.lean` tangent-cone necessity supply the main
analysis. Any upstream proposal should first check duplication and harmonize the
interface with existing convex analysis. No upstream submission has been made.
