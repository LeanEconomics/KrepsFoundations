# Corrections and conventions

## Corrections

The following discrepancy was checked against the original page image, not just OCR.

| Where | Book | Lean |
| --- | --- | --- |
| Problem 1.16c, p. 28, strict revealed preference before Definition 1.22 | The displayed definition requires `x` to be chosen and `y` not to be chosen at an observation, without requiring `y` to be in that menu. The following sentence says strict revealed preference implies weak revealed preference. | `ObservedStrict` also requires `y` to belong to the observed menu. Without it, choosing `true` from `{true,false}` and `false` from `{false}` is utility maximizing but creates the purported SGARP violation `true` weakly revealed above `false`, then `false` strictly revealed above `true`. Formal counterexample: `printed_strict_counterexample`. |
| Proposition 1.23, p. 28, observation nonemptiness | The proposition does not separately state nonemptiness of each observed chosen set. It needs the interpretation that observations are actual nonempty choices. | `proposition_1_23` makes feasibility and nonemptiness explicit. `empty_observation_not_rationalizable` proves that empty choice from a singleton satisfies SGARP but has no complete, transitive rationalization. The theorem does not claim sufficiency for observations that permit empty chosen sets. |
| Section 1.8, p. 20, first paragraph under the two vaccination frames | One sentence reverses the stated comparison of X and Y relative to both the preceding and following sentences. | `framing_reversal_impossible` expresses the surrounding argument: A above B and Y above X cannot both be strict rankings of the same normalized outcomes. This is a mathematical consistency statement; empirical response frequencies are not axioms. The conflicting sentence was checked in the printed page image. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Chapter 1, pp. 1-3 | Choice is defined on nonempty subsets; later problems restrict the menu domain. | Full-domain choice is extended to the empty menu by the empty set. Feasibility forces this value; all economic statements concern admissible menus. Restricted-domain predicates retain explicit menu membership. |
| Proposition 1.15, pp. 14-15 | Continuous preferences admit a utility representation; this chapter does not prove that the representing utility is continuous. | Representation and continuity of the representing function are distinct properties. |
| Proposition 1.19, p. 17 | The book defers its main proof to Chapter 2. Problem 1.13 gives a direct compactness route. | Use that direct route within this independent chapter project. |
| Definition 1.13; Proposition 1.15, pp. 13-15 | Euclidean distance; a footnote explicitly permits equivalent finite-dimensional norms. The proof uses rational bundles as a countable dense set. | `NonnegativeOrthant k` uses the standard finite-product metric and relative topology. `continuousPreference_iff_metric` proves the common-radius condition. Connectedness and an arbitrary countable dense subset give the alternative proof invited on p. 15. |
| Definition 1.22; Proposition 1.23, p. 28 | Finite weak chains; finitely many observed menus. | Finite chains use `Relation.ReflTransGen`. The proof works for arbitrary indexed families of feasible, nonempty observations, including the book's finite family. It uses Mathlib's linear extension of the quotient revealed preorder; it does not assume a real utility representation. |
