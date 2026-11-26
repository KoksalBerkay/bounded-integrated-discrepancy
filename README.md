# Bounded integrated discrepancy of greedy L² sequences

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24542921.svg)](https://doi.org/10.5281/zenodo.24542921)

**Author:** Köksal Berkay Denktaş (B.Sc. student in Computer Engineering,
Politecnico di Torino), ORCID [0009-0008-9261-1007](https://orcid.org/0009-0008-9261-1007)

This repository contains a Lean 4 / Mathlib formalisation, experiments and two
papers about **Kritzinger's greedy L² sequence** on `[0,1]`:

1. *Bounded integrated discrepancy of greedy L² sequences, with a Lean
   formalization* (`paper/`, doi:10.5281/zenodo.24542921): `−2/3 ≤ G_N ≤ 1/2`.
2. *Greedy L² sequences have logarithmic star discrepancy, with a Lean
   formalization* (`paper2/`): the star discrepancy is at most
   `⌈log₂ N⌉ + 3`, which proves the order-of-growth part of Kritzinger's
   conjecture.

## The sequence

Start with `x₁ = 1/2`. Given `x₁,…,x_N`, choose `x_{N+1}` in `[0,1]` to minimise
the L² star discrepancy of the extended list; Kritzinger takes the least
minimiser. This gives `1/2, 1/4, 5/6, 1/8, 7/10, 5/12, 13/14, 1/16, …`
(R. Kritzinger, 2022). Steinerberger (2022/2024) showed that greedy minimisation
of the Wasserstein distance `W₂` to the uniform measure gives the same sequence.

With `D_N(t) = #{k ≤ N : x_k ≤ t} − N t`, the **integrated discrepancy** is

    G_N(t) = ∫_0^t D_N(s) ds = Σ_k (t − x_k)_+ − N t²/2.

Steinerberger proved `max_t |G_N(t)| ≤ 2 N^{1/3}` for infinitely many `N`, and
remarked that it is unclear whether `G_N` is bounded.

## Main results (verified in Lean)

For every greedy L² sequence started from the empty set (any tie-break, so in
particular Kritzinger's sequence), for every `N` and every `t ∈ [0,1]`:

1. **Two-sided bound:** `−2/3 ≤ G_N(t) ≤ 1/2`. So the integrated discrepancy is
   bounded for every `N`.
2. **Upper envelope:** `G_N(t) ≤ min(t/2, G_N(1) + (1−t)/2)`.
3. **Chord invariant:** `G_N` lies at most `√p − p/2` below its chord on any
   `[a,b] ⊆ [0,1]`, where `p = (t−a)(b−t)`.
4. **Centre of mass:** `|x₁ + … + x_N − N/2| ≤ 1/2`.
5. **Quadrature:** for every `f ∈ C²[0,1]`,
   `|Σ_{k≤N} f(x_k) − N ∫_0^1 f| ≤ |f'(1)|/2 + (2/3) ∫_0^1 |f''|`.
   For convex `f`, `Σ f(x_k) − N∫f ≤ (f(0)+f(1))/2 − f(b_N)`, where
   `b_N = (N+1)/2 − Σ x_k`.
6. **Arbitrary starts:** after any fixed initial list, the same bounds hold
   with additive constants that depend on the initial list.

Numerically, `−0.48764 < G_N < 0.49086` for all `N ≤ 300000`. We conjecture
`|G_N| ≤ 1/2`.

## Second paper (verified in Lean)

For every greedy L² sequence started from the empty set (any tie-break), every
`N ≥ 1` and every `t ∈ [0,1]`:

    #{k ≤ N : x_k ≤ t} − N t ≤ ⌈log₂ N⌉ + 3,   N t − #{k ≤ N : x_k < t} ≤ ⌈log₂ N⌉ + 3.

So the star discrepancy is `O(log N)`. This is the first part of Kritzinger's
Conjecture 2 (arXiv:2109.06298); his sharper constant `1/(3 log 2)` remains
open. The key step is the chord invariant of the first paper with a symmetric
chord, `G(t+h) + G(t−h) − 2G(t) ≤ 2h`, followed by a dyadic argument.
Also proved:
- Kritzinger's sequence (search over `[0,1)` as in his Algorithm 2) exists and is
  unique, and it is the same sequence as with search over `[0,1]`.
- From any initial list of `m` points: star discrepancy `≤ ⌈log₂ N⌉ + 3 + 3m²`
  for `N ≥ 2m`, and eventually `−2/3 − ε ≤ G_N ≤ 1/2 + ε`.

## Verify

Lean 4.31 and Mathlib (rev `fabf563`) are pinned in `lean/`:

    cd lean
    lake exe cache get        # prebuilt Mathlib (first time only)
    lake build
    lake env lean AxiomAudit.lean

`lean/check.sh` runs the build and the axiom audit. Every headline theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

| File | Contents |
|---|---|
| `lean/GreedyDiscrepancy/Defs.lean` | Kritzinger's objective, greedy step, the sequence, the conjecture |
| `lean/GreedyDiscrepancy/Warnock.lean` | adding one point changes the L² discrepancy by Kritzinger's objective |
| `lean/GreedyDiscrepancy/FirstSteps.lean` | the first two terms `1/2, 1/4` |
| `lean/GreedyDiscrepancy/Envelope.lean` | upper envelope, `G ≤ 1/2`, centre of mass |
| `lean/GreedyDiscrepancy/EnvelopeGeneral.lean` | upper envelope from arbitrary starts |
| `lean/GreedyDiscrepancy/LowerBound.lean` | chord invariant, `G ≥ −2/3`, arbitrary starts |
| `lean/GreedyDiscrepancy/Quadrature.lean` | quadrature identity, convex bounds |
| `lean/GreedyDiscrepancy/QuadratureTwoSided.lean` | two-sided quadrature bound |
| `lean/GreedyDiscrepancy/StarDiscrepancy.lean` | slope lemmas; star discrepancy `≤ √(7N/3)` (paper 2) |
| `lean/GreedyDiscrepancy/LogStar.lean` | second differences, dyadic argument, `kritzinger_conjecture_holds` (paper 2) |
| `lean/GreedyDiscrepancy/Existence.lean` | existence and uniqueness of Kritzinger's sequence (paper 2) |
| `lean/GreedyDiscrepancy/HalfOpen.lean` | Kritzinger's search space `[0,1)`; the conjecture in his formulation (paper 2) |
| `lean/GreedyDiscrepancy/Repair.lean` | excess over the envelopes decays from any start (paper 2) |
| `lean/GreedyDiscrepancy/RepairLower.lean` | chord invariant with decaying excess, universal limits (paper 2) |
| `lean/GreedyDiscrepancy/LogStarFrom.lean` | logarithmic star discrepancy from any start (paper 2) |
| `lean/GreedyDiscrepancy/Integrals.lean` | the closed forms equal `∫D_N`, `∫D_N²` (Warnock) and `−∫D_N f'` |

Scope of the formalisation: `G_N` and the L² discrepancy are defined by their
closed forms. `Integrals.lean` proves that they equal the integrals of `D_N`
they stand for. This file was added after the first version of the paper,
which still describes these identities as not formalised. The remarks on
sharpness in the paper are proved in the text only.

## Layout

- `paper/note.tex`: the first paper.
- `paper2/note.tex`: the second paper.
- `lean/`: Lean library, `check.sh`, `AxiomAudit.lean`.
- `experiments/`: scripts behind the numerical statements of the papers
  (floating point with exact tie resolution; empirical only);
  `paper2_numerics.py` for the second paper.
- `data/`: the first 30000 terms and how to regenerate the larger datasets.
- `RESEARCH_LOG.md`: how the results were found, including AI contributions.

## AI assistance

First paper: carried out with the help of Claude Opus 5.5 in Claude Code and
GPT-6.2 Sol in Codex; the chord invariant and the constant 2/3 were found by
GPT-6.2 Sol. Second paper: carried out with the help of Claude Opus 5.5 in
Claude Code and reviewed by GPT-6.2 Sol in Codex. All theorems are checked by
the Lean kernel.

## License

Copyright 2026 Köksal Berkay Denktaş. Code and data: Apache License 2.0
(`LICENSE`, `NOTICE`). Paper texts: CC BY 4.0 (`paper/LICENSE.md`, `paper2/LICENSE.md`). Both licenses
require attribution.

## How to cite

Köksal Berkay Denktaş, *Bounded integrated discrepancy of greedy L² sequences,
with a Lean formalization* (2026). Zenodo,
[doi:10.5281/zenodo.24542921](https://doi.org/10.5281/zenodo.24542921).
GitHub's "Cite this repository" button gives the same reference.

## References

- R. Kritzinger, *Uniformly distributed sequences generated by a greedy
  minimization of the L2 discrepancy*, Moscow J. Combin. Number Theory 11 (2022);
  [arXiv:2109.06298](https://arxiv.org/abs/2109.06298).
- S. Steinerberger, *On combinatorial properties of greedy Wasserstein
  minimization*, J. Math. Anal. Appl. 532 (2024);
  [arXiv:2207.08043](https://arxiv.org/abs/2207.08043).
- F. Clément, *Outperforming the best 1D low-discrepancy constructions with a
  greedy algorithm*, [arXiv:2406.18132](https://arxiv.org/abs/2406.18132).
