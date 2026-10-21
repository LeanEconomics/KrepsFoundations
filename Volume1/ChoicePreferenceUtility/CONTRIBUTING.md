# Contributing

Use explicit hypotheses and the book's domains. Each original Lean file has an Apache 2.0
header. Preserve attribution for adapted source. Do not introduce proof placeholders,
new axioms or trusted computation.

Run `python scripts/verify.py`. Update `proof-manifest.json`, the README library map,
`docs/source-map.md` and `docs/corrections.md` with each mathematical change. A passing
Lean build checks the encoded statements; source review checks correspondence to Kreps.
