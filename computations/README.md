# Programs and raw outputs

These programs independently compute the same quantities that the Lean files
certify (or, for a few larger cases, only the programs were run).

## `#18` (`e18/`)

- `h.c` — byte-array dynamic program for `h(n!)`. Compile with
  `cc -O2 -o h h.c` and run `./h 12`. The recorded output for `n = 12` is
  `h12.txt`.
- `hm.c` — a variant that takes the modulus `m` itself as the argument
  rather than `n` (so `./hm 479001600` for `12!`). Prefer `h.c`.
- `bits.py` — the same recurrence as the Lean bitset DP, using Python
  integers and SymPy's divisor list. Requires `sympy`. Recorded outputs:
  `py11.txt`, `py12.txt`.
- `H3_8.out`, `H9_10.out`, `H11_native.out` — `#print axioms` traces from
  the Lean runs (also copied under `/axioms`).

## `#710` (`e710/`)

- `f710.py` — computes `f(n)` by growing a matching in the interval `(n, n+L)`.
- `cert710.py` — writes matching and Hall certificates for `n = 1..N`
  (`cert_200.json` is the `N = 200` run used to generate the Lean files).
- `b390246.txt` — the OEIS A390246 b-file used for comparison (values agree
  for `n = 1..200`).

## `#711` (`e711/`)

- `f711.c` — exhaustive search of `max_m f(n,m)` for `n = 1..N`, using
  periodicity modulo `lcm(1..n)`. Recorded output: `max711_18.txt`.
- `f711b.c` — the same program for a range `N0..N`. Recorded output for
  `n = 19`: `max711_19.txt`.
- `cert711.py` — matching and Hall certificates; `up_3.json` … `up_10.json`
  were used to generate `E711/M3.lean` … `M10.lean`. `hall17.json` is the
  Hall certificate for `f(17, 485749) = 34`.
