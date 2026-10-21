# Provenance and convention alignment

Reference audit: 21 October 2026. Both branch heads were resolved before inspecting the
files below. These revisions fix what was read; later upstream changes are not implicitly
adopted.

| Reference | Inspected commit | Role in this repository |
| --- | --- | --- |
| [LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming/tree/d39805f553dfb9619271b32bbf858d3162ca7e4e) | `d39805f553dfb9619271b32bbf858d3162ca7e4e` | Independent chapter packages, stable dependency pins, source maps, corrections and the fresh proof verifier. |
| [LeanEconomics/LeanEconomics](https://github.com/LeanEconomics/LeanEconomics/tree/8295256bbd64ab488c8cb436d68e7064db560dfc) | `8295256bbd64ab488c8cb436d68e7064db560dfc` | Explicit hypotheses, reusable mathematical foundations, human/AI provenance, local Mathlib checks and evidence-based upstream tracking. |

## Inspected material

DynamicProgramming:

- [README](https://github.com/LeanEconomics/DynamicProgramming/blob/d39805f553dfb9619271b32bbf858d3162ca7e4e/README.md)
  and the chapter plans `PROPOSAL-SargentStachurski.md` and
  `PROPOSAL-StokeyLucasPrescott.md`.
- The representative `RecursiveMethods/DeterministicDP` chapter's README,
  [CONTRIBUTING](https://github.com/LeanEconomics/DynamicProgramming/blob/d39805f553dfb9619271b32bbf858d3162ca7e4e/RecursiveMethods/DeterministicDP/CONTRIBUTING.md),
  third-party notices, source map, corrections, manifest, Lake configuration and toolchain.
- [Principle.lean](https://github.com/LeanEconomics/DynamicProgramming/blob/d39805f553dfb9619271b32bbf858d3162ca7e4e/RecursiveMethods/DeterministicDP/DeterministicDP/Principle.lean),
  as an example of source-numbered theorems, explicit assumptions, section documentation
  and a corrected endpoint case.
- Its verifier and failure-path tests, and the
  [CI matrix](https://github.com/LeanEconomics/DynamicProgramming/blob/d39805f553dfb9619271b32bbf858d3162ca7e4e/.github/workflows/check.yml).

LeanEconomics:

- [README](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/README.md),
  [CLAUDE.md](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/CLAUDE.md),
  and [UPSTREAM.md](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/UPSTREAM.md).
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, and its build/documentation,
  dependency-update and release workflows.
- [Berge.lean](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/LeanEconomics/Topology/Berge.lean),
  [Parametric.lean](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/LeanEconomics/DynamicProgramming/Parametric.lean),
  and [DecreasingIncrements.lean](https://github.com/LeanEconomics/LeanEconomics/blob/8295256bbd64ab488c8cb436d68e7064db560dfc/LeanEconomics/Analysis/DecreasingIncrements.lean).
  These illustrate reusable helpers, a check that substantive hypotheses can hold,
  economical assumptions and explicit discussion of existing Mathlib results.

The inspected LeanEconomics tree has a `CLAUDE.md` but no separate `AGENTS.md`,
`CONTRIBUTING.md`, `GOVERNANCE.md`, `CODEOWNERS`, `CODE_OF_CONDUCT.md` or `SECURITY.md`.
Its README describes human direction and review by its own principal. Those roles and
names do not establish governance or authorship for this separate repository.

## Decisions where the references differ

| Issue | Adopted convention |
| --- | --- |
| Package layout | DynamicProgramming's independent chapter projects; no root Lake library or cross-chapter Lake dependencies. |
| Versions | Lean/Mathlib `v4.34.0` from DynamicProgramming. LeanEconomics still uses `v4.34.0-rc2`; its release-candidate pins are not copied here. |
| Incomplete proofs | DynamicProgramming's strict prohibition on placeholders. The older LeanEconomics guidance allowing a visibly annotated unfinished proof is not adopted. |
| Verification | Keep the existing fresh recompilation and named-declaration axiom audit, in addition to normal `lake build` checks with configured linters. |
| CI | Preserve the read-only per-chapter matrix and pinned action revisions. LeanEconomics' documentation deployment, release-writing and dependency-update workflows are not required to build these chapter packages. |
| Naming | Keep chapter namespaces, established definitions and numbered source aliases; use descriptive names for reusable helpers. Do not rename the existing API merely to match another project's vocabulary. |
| Storage | Retain ignored local caches. Dropbox-specific extended attributes and local paths in the reference's environment notes do not apply here. |
| Subject matter | Formalize Kreps's microeconomics. The other repository's recursive-macroeconomics priorities and model-specific differentiability conventions do not replace the book's assumptions. |
| Attribution | State this project's own human direction and Codex assistance; preserve original notices when actual code is copied. |
| Upstream candidates | Record searches and limitations in `UPSTREAM.md`, distinguishing useful local wrappers from possible Mathlib contributions. |

## Dependency and verifier identity

Both chapter manifests have exactly the same `packages` entries as the inspected
DynamicProgramming `RecursiveMethods/DeterministicDP/lake-manifest.json`. The only
top-level manifest difference is the chapter package name. The nine pinned packages are
Mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries and Cli.
The Mathlib revision is `5ed2965256430c3649e86755f9576b54eca72435`.

Both chapters' verifier and tests are byte-for-byte copies of the reference files:

| File | SHA-256 |
| --- | --- |
| `scripts/verify.py` | `a70b1fa704dd590f937f8b37682afa88a9d85a9150065acb935c7d2c9589da3b` |
| `scripts/test_verify.py` | `3edbe360ed0a2d9071d2d3402ef2205e116f466f8af213ab241840cd9255666c` |

The convention alignment changes documentation and contribution guidance. It does not
change those scripts, the proof-checking policy, dependencies, CI permissions or Lean
proof modules. Future changes to any baseline need their own explicit provenance entry
and verification; this audit is not a claim about a later state.

## Authorship, licenses and review

The original formalization and supporting documentation are developed with OpenAI Codex,
including parallel agents, under the user's direction. Existing file headers identify
the contributors collectively. The user determines scope; economic interpretation and
source correspondence require substantive review. Lean checks the encoded propositions,
and the verifier separately records their transitive axioms and source hashes. A kernel
check does not imply that an external researcher or reference-project maintainer reviewed
the economics.

Original project material is Apache 2.0 licensed. Lean, Mathlib, copied verification code
and other dependencies retain their notices. See the chapter `THIRD_PARTY_NOTICES.md`
files for copied material, including the Chapter 1 prerequisites copied into Chapter 2.
The convention documents are newly written adaptations; no LeanEconomics proof module
was copied as part of this alignment.

Kreps's book remains copyrighted by its rights holders. The repository cites printed
pages, result numbers and bibliographic details, and keeps the locally supplied PDF
outside version control. It does not distribute the textbook or its figures.
