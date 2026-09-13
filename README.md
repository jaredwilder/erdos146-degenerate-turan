# Erdős #146: degenerate Turán program

For each fixed finite bipartite `r`-degenerate graph `H`, the target is
`ex(n,H) = O_H(n^(2−1/r))`, where `ex(n,H)` counts the most edges in an
`n`-vertex graph avoiding an ordinary (not necessarily induced) copy of `H`.
A graph is `r`-degenerate when every nonempty induced subgraph has a vertex
of degree at most `r`.

This focused home collects Jared Wilder's formal reductions and reusable
graph lemmas for this target. The campaign does not prove the conjecture.

## What is proved in the recorded Lean builds

- **Minimum-degree extraction:** a finite graph with more than `k·n` edges
  has a nonempty induced subgraph of minimum degree greater than `k`.
- **Sparsity:** an `r`-degenerate finite graph has at most `r·n` edges, with
  the corresponding degree-sum bound inside every vertex subset.
- **Degeneracy structure:** a degeneracy ordering exists, degeneracy passes
  to subgraphs, and complete bipartite graphs witness strictness of the
  degeneracy hierarchy.
- **Exponent and reduction lemmas:** the growth scales are strictly separated;
  the weaker AKS scale or the trivial quadratic bound alone does not imply
  the target scale. Quantification over finite vertex types is reduced to
  finite standard universes.

The minimum-degree and sparsity results are classical graph lemmas formalized
here. The exponent separation is an insufficiency result about numerical
bounds, not a proof that no argument using additional structure could work.

## Reading map

| Source | Content | Historical clean checks |
|---|---|---:|
| [Attack01.lean](research/Attack01.lean) / [log](research/Attack01.log) | Exponents, finite-universe reduction, degeneracy ordering | 26 |
| [Attack02.lean](research/Attack02.lean) / [log](research/Attack02.log) | Complete-bipartite hierarchy and strictness | 11 |
| [Attack03.lean](research/Attack03.lean) / [log](research/Attack03.log) | Degree-sum identity, extraction, sparsity and subgraph bridge | 14 |
| [TERMINAL.json](research/TERMINAL.json) | First two stages and their unresolved dependencies | — |
| [TERMINAL-attack03.json](research/TERMINAL-attack03.json) | Updated boundary after minimum-degree extraction | — |

There are **51 clean named historical checks**, not 37: the smaller count
covers only the first two files. All 51 logged axiom lists omit `sorryAx`.
The separate `Probe01.lean` and `Probe01.log` are retained as failed,
deliberately incomplete exploration and are excluded from this count.

## What remains unresolved

Within this package, the `r=1` proof still needs the greedy embedding step
and the final extremal-number bound assembly. The `r=2` and general target
are not proved. Read the third terminal record for the latest campaign
boundary; older comments correctly describe what was missing at their stage.

## Verification and provenance

```sh
python verification/verify_source.py
```

This verifies exact bytes, SHA-256 and Git blob IDs for the public sources.
The three Lean logs record successful historical checks against the Mathlib
pin `919544d4`; a fresh Lean build was not performed during this promotion.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) pins the full public archive commit
and records all 10 original research files plus the inherited license.

The [mixed campaign archive](https://github.com/jaredwilder/erdos-campaign-archive)
retains the originals. This repository supplies the problem-specific reading map.

Author: Jared Wilder. Campaign: 2026-09-05. Focused release: 2026-09-13.
License: inherited Apache-2.0; see [LICENSE](LICENSE).
