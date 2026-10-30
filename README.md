# Kreps Foundations in Lean

A chapter-by-chapter formalization of David M. Kreps, *Microeconomic Foundations I:
Choice and Competitive Markets*. The [proposal](PROPOSAL-KrepsFoundations.md) specifies
all sixteen chapters and eight appendices, following
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
The repository also follows the mathematical and provenance practices of
[LeanEconomics/LeanEconomics](https://github.com/LeanEconomics/LeanEconomics);
[PROVENANCE.md](PROVENANCE.md) records the inspected revisions and convention choices.

Each chapter is an independent Lean/Mathlib project pinned to `v4.34.0`, with source
maps, corrections and fresh proof audits. Work proceeds in book order.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [Volume1/ChoicePreferenceUtility](Volume1/ChoicePreferenceUtility/README.md) | 1. Choice, Preference, and Utility | 263 theorems / 387 declarations; fresh audit passed | [Chapter overview](Volume1/ChoicePreferenceUtility/README.md) |
| [Volume1/PreferenceProperties](Volume1/PreferenceProperties/README.md) | 2. Structural Properties of Preferences and Utility Functions | 1064 theorems / 1378 declarations; fresh audit passed | [Chapter overview](Volume1/PreferenceProperties/README.md) |
| [Volume1/ConsumerDemand](Volume1/ConsumerDemand/README.md) | 3. Basics of Consumer Demand | 450 theorems / 610 declarations; fresh audit passed | [Chapter overview](Volume1/ConsumerDemand/README.md) |
| [Volume1/RevealedPreference](Volume1/RevealedPreference/README.md) | 4. Revealed Preference and Afriat’s Theorem | 137 theorems / 192 declarations; fresh audit passed | [Chapter overview](Volume1/RevealedPreference/README.md) |

Counts cover each complete independent project, including attributed local prerequisites.
Declarations include theorems, definitions and generated structure constants. Chapter
overviews and source maps give the breakdown and precise chapter/appendix coverage.

Chapters 1–4 are complete within the scope recorded in their source maps, including
their mathematical exercises, examples and documented corrections. Chapters 3–4
passed independent source review, full builds, fresh-source compilation and all
declaration axiom audits on 2026-10-30. Required appendix support is distinguished
from complete appendix coverage. Chapters 5–16 remain planned.

## Build and verify

From an implemented chapter directory:

```sh
lake exe cache get
python scripts/verify.py
```

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the transitive
axiom audit. The verifier checks the complete library and freshly re-elaborates its
source. Documentation distinguishes verified results from outstanding source coverage.

## License and provenance

Apache 2.0; see [LICENSE](LICENSE) and each chapter's third-party notices. Formalization
is developed with OpenAI Codex under the user's direction. The textbook is cited and
is not distributed. Read the [working guidance](AGENTS.md) before contributing;
[UPSTREAM.md](UPSTREAM.md) records possible reusable mathematical contributions and
the duplication checks still required before an upstream proposal.
