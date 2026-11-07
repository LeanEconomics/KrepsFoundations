# Third-party notices

Original code and documentation are released under Apache 2.0. See `LICENSE`.
Lean, Mathlib and their dependencies retain their upstream licenses.

The verifier and its tests are copied from LeanEconomics/DynamicProgramming,
commit `d39805f553dfb9619271b32bbf858d3162ca7e4e`,
`RecursiveMethods/DeterministicDP/scripts/`, under Apache 2.0. The Lake configuration,
dependency pins and verification conventions follow the same repository.

`Basic.lean` and `StrictPreference.lean` are attributed copies of the corresponding
Chapter 1 modules in `Volume1/ChoicePreferenceUtility/ChoicePreferenceUtility/` at
`f9c357ada1d9965dabd9eec694720ba585faf575`. Only imports, namespace and attribution
were adapted. Each chapter builds as an independent Lake project.

Mathlib's standard simplex and convex-space APIs supply the finite-support lottery
and abstract mixture operations. The finite support induction in
`Convexity.IsConvexSet.of_convexCombPair_mem` underlies the extension from binary
mixture affinity to the expected-utility formula. The Borel-law development uses
Mathlib's probability measures, integrals, bounded continuous functions and weak
topology. See the source map for the economic constructions carried out here.

The book is David M. Kreps, *Microeconomic Foundations I: Choice and Competitive
Markets*, Princeton University Press, ISBN 978-0-691-15583-8. Citations use printed
pages. The textbook and its figures are not distributed. Original formalization
was developed with OpenAI Codex under the user's direction.
