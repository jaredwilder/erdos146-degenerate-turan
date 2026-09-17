# Erdős #146 — degenerate Turán bounds

For a fixed finite bipartite `r`-degenerate graph `H`, the target is

\[
\mathrm{ex}(n,H)=O_H\!\left(n^{2-1/r}\right),
\]

where `ex(n,H)` is the maximum number of edges in an `n`-vertex graph containing no copy of `H`.

This repository formalizes several structural ingredients and reduction lemmas around that target.

## Lean results

The recorded development proves:

- **Minimum-degree extraction.** If a finite graph has more than `k·n` edges, it contains a nonempty induced subgraph of minimum degree greater than `k`.
- **Degenerate sparsity.** An `r`-degenerate graph has at most `r·n` edges, together with the corresponding degree-sum bound on every vertex subset.
- **Degeneracy structure.** Degeneracy orderings exist, degeneracy passes to subgraphs, and complete bipartite graphs separate successive degeneracy levels.
- **Exponent separation.** The weaker AKS scale and the trivial quadratic bound do not by themselves imply the target exponent.
- **Finite-universe reduction.** Quantification over finite vertex types is reduced to finite standard universes.

The minimum-degree and sparsity lemmas are classical graph theory results, formalized here as reusable infrastructure.

## Sources

| File | Content |
|---|---|
| [`Attack01.lean`](research/Attack01.lean) | Exponents, finite-universe reduction, degeneracy ordering |
| [`Attack02.lean`](research/Attack02.lean) | Complete-bipartite hierarchy |
| [`Attack03.lean`](research/Attack03.lean) | Degree sums, minimum-degree extraction, sparsity, subgraph bridge |
| [`TERMINAL-attack03.json`](research/TERMINAL-attack03.json) | Latest recorded campaign boundary |

There are 51 named clean checks across the three recorded Lean logs. `Probe01.lean` is retained separately as incomplete exploration and is not included in that count.

## Verification

```sh
python verification/verify_source.py
```

The source manifest records exact bytes, SHA-256 values, and Git blob IDs. The historical Lean logs were produced against Mathlib commit `919544d4`.

## Open boundary

The package does not prove the full Erdős #146 bound. The recorded `r=1` route still needs the greedy embedding step and final extremal estimate; `r=2` and the general case remain open here.

Author: Jared Wilder. License: Apache-2.0.
