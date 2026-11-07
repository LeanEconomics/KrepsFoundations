# Cross-chapter consistency

Chapters 1–6 form a mathematical dependency chain while remaining independent Lake
projects, following the DynamicProgramming structure. Later chapters contain attributed
local copies of the earlier foundations they need. An earlier edit therefore does not
automatically update every copy; the checks here detect divergence and verify composition.

The 2026-11-07 audit passed 48 complete-copy checks, 36 compatibility theorems and
joint fresh compilation of all six libraries. All 3,652 named declarations passed
the axiom audit, using only `propext`, `Classical.choice` and `Quot.sound`. All eight
consistency regression tests passed. These counts include the chapter declarations
and the additional bridge theorems; see the generated [record](verification.json).

## What is checked

| Connection | Evidence |
| --- | --- |
| Chapter 1 → Chapter 2 | All 12 complete prerequisite modules match their current originals after only declared namespace/import substitutions, comments and layout are normalized. |
| Chapter 2 → Chapter 3 | All 11 complete `Representation*` modules match their originals. Chapter 2's actual continuous-representation theorem also produces Chapter 3 demand in a joint proof. |
| Chapters 1–2 → Chapter 5 | The two Chapter 1 preference modules match their originals. On finite state spaces Lean proves the equivalence of Chapter 2's strong separability and Savage's Sure-Thing Principle. |
| Chapters 3–4 → Chapter 6 | Six modules connect the actual Chapter 3 budget problem to income risk. Chapter 4's finite-minimum theorem supplies the concave utility used in the coupling proof. All seven complete copies match their originals. |
| Chapter 5 → Chapter 6 | The 16 copied lottery and probability modules match Chapter 5. The original expected-utility theorem composes with the original budget problem and Chapter 6's optimal selection result to derive preferences over immediately resolved income lotteries. |
| Shared economic definitions | Lean proves agreement of rationality, choice, utility representation, strict preference, indifference, nonnegative domains, continuity, local insatiability, convexity and homotheticity across the applicable chapters. |
| Chapter 2 convexity → Chapter 3 choice | The independent Chapter 3 API derives convex choice sets and uniqueness from primitive preference assumptions, using budget convexity and proved existence. |
| Chapter 3 budgets → Chapter 4 observations | Lean proves equality of the budgets after packaging Chapter 4's sign proofs, and equivalence of rationalization with observed membership in Marshallian demand. |
| Chapter 4 → Chapter 3 consumer theory | The actual Afriat construction supplies utility that rationalizes observations and gives nonempty convex demand on every budget, upper semicontinuity, local compact bounds and continuous indirect utility. |
| Environment and proof policy | All six projects have identical Lean/Mathlib pins, transitive dependency revisions, Lean options and unchanged verifier scripts. All chapter sources and bridge proofs are freshly elaborated together and every named declaration's axioms are checked. |

The complete-copy inventory is [copies.json](copies.json). Selected definitions adapted
into shorter prerequisite modules are checked through the semantic equalities in
[ChapterBridges.lean](ChapterBridges.lean), rather than falsely claiming their entire
files are identical. The joint checker reads current source files, not previously built
chapter proof objects. It records source hashes and rejects changes made during its run.

These checks preserve meaningful differences in scope. Demand is a full correspondence;
observing one chosen bundle does not imply it was the unique maximizer. Afriat's finite
minimum of affine utilities is concave and continuous but need not be strictly concave
or differentiable. The bridge therefore does not claim unique or smooth demand. Zero
income and boundary bundles remain included; positivity of commodity dimension is used
only in the results that require it, such as local insatiability.

## Reproduce

First fetch the union of the six chapters' external Mathlib imports in the
`Volume1/04_RevealedPreference` dependency environment, as the CI workflow does. Then run
from the repository root:

```sh
python -m unittest discover -s scripts -p 'test_*.py' -v
python scripts/verify_consistency.py
```

The checker uses RevealedPreference's pinned Lake environment for external dependencies;
there is no root Lake package or added chapter-to-chapter Lake dependency. `--lake` may
select the pinned Lake executable explicitly. `--generate-only` prepares the ignored
joint source for inspection without claiming a successful audit.

The [verification record](verification.json) stores the checked source hashes, copy count,
joint declaration count and bridge axiom results. Generated `FreshAudit.lean` and the raw
log are ignored and reproducible. Individual chapter builds and audits remain required;
the joint check supplements them. CI runs both the regression tests (including deliberate
copy and dependency mutations) and the joint proof audit in its RevealedPreference job.

Source correspondence and chapter coverage remain documented in the chapter source maps.
The check proves the specified interfaces compose; future APIs should add their own bridge
statements and copy mappings when they reuse or adapt these foundations.
