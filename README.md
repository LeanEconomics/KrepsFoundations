# Kreps Foundations in Lean

A chapter-by-chapter formalization of David M. Kreps, *Microeconomic Foundations I:
Choice and Competitive Markets*. The [proposal](PROPOSAL-KrepsFoundations.md) specifies
all sixteen chapters and eight appendices, following
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).

Each chapter is an independent Lean/Mathlib project pinned to `v4.34.0`, with source
maps, corrections and fresh proof audits. Work proceeds in book order.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [Volume1/ChoicePreferenceUtility](Volume1/ChoicePreferenceUtility/README.md) | 1. Choice, Preference, and Utility | 213 theorems / 322 declarations audited; Chapter 1 and Appendix 1 mathematical coverage complete | [Chapter overview](Volume1/ChoicePreferenceUtility/README.md) |
| [Volume1/PreferenceProperties](Volume1/PreferenceProperties/README.md) | 2. Structural Properties of Preferences and Utility Functions | In progress: 169 new Chapter 2 theorems; 267 total with local prerequisites; fresh audit passed | [Chapter overview](Volume1/PreferenceProperties/README.md) |

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
is not distributed.
