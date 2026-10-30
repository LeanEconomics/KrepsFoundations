# Working on KrepsFoundations

This repository formalizes David M. Kreps, *Microeconomic Foundations I*, chapter by
chapter. The user sets the mathematical scope. Chapters 1–4 have completed their source
reviews and proof audits. Chapters 5–16 remain planned until the user resumes them.
Keep status claims tied to the actual statements and completed verification, rather than
declaration counts alone.

The convention references and their exact revisions are recorded in
[PROVENANCE.md](PROVENANCE.md). This file combines DynamicProgramming's independent
chapter and audit workflow with LeanEconomics' reusable mathematics and provenance
practice. The reference repositories are sources to inspect, not additional dependencies.

## Project structure and environment

- Each `Volume1/<Chapter>/` directory is an independent Lake project. Run commands from
  that directory. There is no root Lake package or dependency on another chapter.
- Keep Lean `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`, and the committed transitive
  dependency revisions. The resolved Mathlib revision is
  `5ed2965256430c3649e86755f9576b54eca72435`. Do not silently move a chapter to another
  version, including the release-candidate version used by the LeanEconomics reference.
- Preserve the configured standard Mathlib linters, explicit implicit-variable settings,
  and `maxSynthPendingDepth`. Use ordinary `lake build` during development so these
  project options are applied.
- Preserve `.lake/` caches during ordinary development. Do not put local toolchain,
  cache, PDF or machine-specific paths into project configuration.
- Reuse prior chapter material by making attributed local copies in the receiving
  chapter's namespace. Record the originating commit and review all affected copies
  when changing a common definition or statement.
- Keep full-copy mappings in `consistency/copies.json` and semantic interface checks in
  `consistency/ChapterBridges.lean`. After changing shared foundations, run the root
  consistency tests and `python scripts/verify_consistency.py`, in addition to affected
  chapter audits. Preserve independent packages; this check compiles their sources jointly.

## Mathematical work

- Read the relevant source statement, proof, examples and exercises before implementing
  it. Record printed pages and result numbers in docstrings and source maps.
- Preserve the book's domains, quantifiers and endpoints. Supply primitive-assumption
  wrappers when an intermediate theorem uses representation, attainment, separability
  or another conclusion that the source derives.
- A theorem with the desired conclusion as an assumption does not complete the source
  result. A finite special case does not complete an infinite-domain statement. When a
  problem requests a particular construction, formalize that construction and its steps.
- If the printed claim is false or ambiguous, expose the issue in `docs/corrections.md`
  and prove a faithful corrected statement or counterexample. Do not silently strengthen
  the assumptions and report the unqualified source claim as complete.
- Search the pinned local Mathlib first and check the actual hypotheses and API names.
  Use established Mathlib notions when available; describe the bridge when the chapter
  needs a domain-internal economics definition. Prefer focused imports.
- State useful general results separately from economic specializations. Check that
  major packages of hypotheses have meaningful examples or an existing witness; do not
  introduce smoothness, monotonicity or nonemptiness merely to simplify a proof.
- Keep the existing naming scheme: descriptive theorem names, numbered source aliases,
  and the chapter's established definition names. Avoid unrelated API renaming.
- Every Lean file needs its Apache 2.0 header and module documentation. Public
  definitions and results need concise documentation. Use UTF-8, LF, and lines of at
  most 100 characters.

## Proof checking and completion

- Do not add proof placeholders, new axioms, `unsafe` proof shortcuts or `native_decide`.
  The only allowed transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
  Keep incomplete obligations in the source inventory instead of executable placeholders.
- The copied `scripts/verify.py` and `scripts/test_verify.py` are the audit baseline.
  Do not modify them to accommodate a failing proof, count or warning. Do not suppress
  configured linters to turn a failing check into a passing check.
- During iteration run `lake build <Chapter.Module>` for changed modules. Before a
  verified milestone run, from each affected chapter:

  ```sh
  python -m unittest discover -s scripts -p 'test_*.py' -v
  python scripts/verify.py
  ```

- Update the root module, `proof-manifest.json`, chapter README library map,
  `docs/source-map.md` and relevant correction/appendix inventories with mathematical
  changes. The source map distinguishes complete results, partial results and remaining
  obligations. Verification JSON records a run; it is not a proof of source fidelity.
- A passing module build is an iteration check. Full completion also requires the fresh
  recompilation, transitive-axiom audit and source review. Only report the checks actually
  performed, against the source snapshot that they checked.
- In parallel work, agree on file ownership and keep shared integration files with the
  coordinator. Review a frozen snapshot for the final audit so subsequent edits cannot
  be confused with checked source. Preserve other contributors' changes.

## Attribution and reusable work

Keep copyright and third-party notices for adapted code. Cite the book by result and page
without reproducing its text or figures. Record human direction and AI assistance
accurately; do not transfer the reference repositories' authorship or claim their
maintainers reviewed this work. See each chapter's `THIRD_PARTY_NOTICES.md`.

Track potentially reusable mathematical additions in [UPSTREAM.md](UPSTREAM.md), with
the Mathlib revision searched, existing related lemmas, and the work needed before any
upstream proposal. A candidate is not a novelty claim or an upstream submission.
