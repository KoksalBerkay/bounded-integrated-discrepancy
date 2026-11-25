# Data

- `kritzinger_30000.seq`: the first 30000 terms of Kritzinger's sequence. Line
  `N i` means `x_N = (2i+1)/(2N)`. SHA-256 in `kritzinger_30000.sha256`.

Regenerate (each command stops after its time budget and can be resumed):

    python3 experiments/kritzinger.py 30000 data/kritzinger_30000
    python3 experiments/fast_potential.py 300000 data/raw/kp 10 420
    python3 experiments/records.py data/raw/kp.seq 2 300001 data/raw/records.csv 420

The two generators agree term by term for N ≤ 30000. Both screen candidates in
floating point and compare near-ties exactly, so data beyond the Lean-checked
statements are empirical.
