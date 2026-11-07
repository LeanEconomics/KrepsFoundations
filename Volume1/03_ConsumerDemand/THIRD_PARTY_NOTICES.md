# Third-party notices

Original code and documentation are released under Apache 2.0; see `LICENSE`.
Lean, Mathlib and their dependencies retain their upstream licenses.

The verifier and its tests are copied from LeanEconomics/DynamicProgramming,
commit `d39805f553dfb9619271b32bbf858d3162ca7e4e`,
`RecursiveMethods/DeterministicDP/scripts/`, under Apache 2.0. Copyright and
attribution belong to their original contributors. The Lake configuration, dependency
pins and CI conventions follow the same repository.

David M. Kreps, *Microeconomic Foundations I: Choice and Competitive Markets*,
Princeton University Press, ISBN 978-0-691-15583-8, is cited by printed page and result.
Its text and figures are not distributed. The local PDF is excluded from version control.

Original formalization is developed with OpenAI Codex under the user's direction;
mathematical coverage and verification status are recorded separately.

Selected prerequisite definitions are adapted from the verified Chapters 1–2
milestone, commit `7d496c5f546d4301da35c1995af5a77694874155`. Module
documentation and the source map identify local reuse. Namespace and import changes
keep each chapter independently buildable. No earlier chapter is a Lake dependency.
