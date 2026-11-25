# Research log

How the results were found. All work was done on 2026-11-25 by the author with
two AI agents: Claude Opus 5.5 (in Claude Code) and GPT-6.2 Sol (in Codex).
Every theorem listed below is checked by the Lean kernel; experiments are
empirical.

## 1. Setup and experiments (Claude)

- Generated Kritzinger's sequence with exact tie resolution and compared it
  with the terms listed by Kritzinger.
- Rewrote the greedy step as "insert at the maximum of `G_N + t(1−t)/2`"
  (equivalent to Steinerberger, §§2.2–2.3), which gave a fast generator.
- Observed that `|G_N| < 1/2` for all `N` tested and stated the conjecture.

## 2. Upper bound (Claude)

- Found the envelopes `G_N(t) ≤ t/2` and `G_N(t) ≤ G_N(1) + (1−t)/2` in the data
  and proved by induction that every greedy step preserves them. Consequences:
  `G_N ≤ 1/2` and `|x_1 + … + x_N − N/2| ≤ 1/2`.
- Extended this to arbitrary initial sets and to quadrature of convex
  functions.
- Formalised all of these in Lean.

## 3. Lower bound: negative results (Claude)

- Counterexample searches showed that simple lower bounds (`G ≥ −1/2`,
  `G ≥ −t + t²/2`, interval versions) are not preserved by a single greedy step
  for arbitrary point sets.
- Value iteration showed that the natural two-point invariant schemes cannot
  give a lower bound.

## 4. Lower bound: the chord invariant (GPT-6.2 Sol)

- GPT-6.2 Sol found the three-point chord invariant, proved the lower bound
  `G_N ≥ −173/240` and checked it in Lean.
- Claude integrated the code into the library and re-ran the full build and
  the axiom audit.

## 5. Independent reviews (GPT-6.2 Sol)

- Two independent referee-style reviews of the paper and the Lean code found
  no critical errors. They corrected the numerical minimum (which had not been
  tracked separately), sharpened several statements, and contributed:
  - the sharp convex quadrature bound `(f(0)+f(1))/2 − f(b_N)`, formalised by
    Claude;
  - the strengthened chord invariant `√p − p/2`, giving `G_N ≥ −2/3`;
  - the lower bound from arbitrary starts.
- Claude re-checked every contributed proof by hand and in Lean before adding
  it.

## 6. Data

- Every `N ≤ 300000`, with the maximum and minimum of `G_N` tracked separately:
  `−0.48764 < G_N < 0.49086`.
