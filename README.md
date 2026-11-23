# Small formally verified data for Erdős problems #18, #710 and #711

This repository contains Lean 4 formalisations and independent programs for
**small cases** of three Erdős problems:

- [#18](https://www.erdosproblems.com/18) — the function `h(n!)`
- [#710](https://www.erdosproblems.com/710) — the function `f(n)`
- [#711](https://www.erdosproblems.com/711) — the function `f(n,m)`

**None of these problems is solved here.** The files are exact values,
periodicity lemmas and a few general inequalities, offered as data for the
problem pages or the forum. A short English note is in
[`paper/Michalak_Erdos18_710_711.pdf`](paper/Michalak_Erdos18_710_711.pdf).

Toolchain: **Lean 4.36.0**, Mathlib **v4.36.0**. There are no `sorry`s in the
Lean sources.

Licence: [CC0 1.0](LICENSE). See also [NOTICE.md](NOTICE.md) for authorship
and for the use of an AI assistant.

## How to read the claims

The tables below separate three levels of evidence. Please do not cite a
row at a stronger level than the one given.

1. **Kernel-checked.** Proved in Lean and checked by the Lean kernel only.
   The recorded axioms are `propext`, `Classical.choice` and `Quot.sound`.
   The tactic `decide +kernel` is used for finite checks; `native_decide`
   is **not** used.
2. **`native_decide`.** The same Lean development, but the final numerical
   evaluation uses `native_decide`, which trusts the Lean compiler and the
   compiled C code. This is labelled wherever it occurs.
3. **Exhaustive computation.** A C or Python program, in some cases run
   independently in two languages. Not a Lean proof.

## Results

### Problem #18 — `h(n!)`

`h(m)` is the least `c` such that every integer `k` with `1 ≤ k < m` is a
sum of at most `c` distinct divisors of `m`. The Lean development proves
correctness of a bitset dynamic program once and for all
(`R6E18Core.lean`); each instance then supplies a prime factorisation of
`n!` and checks the resulting bitmasks.

| `n` | `n!` | `h(n!)` | first witness `k` | evidence |
| ---: | ---: | ---: | ---: | --- |
| 3 | 6 | 2 | — | kernel (`E18/H3_8.lean`, `h3_eq`) |
| 4 | 24 | 3 | — | kernel (`h4_eq`) |
| 5 | 120 | 4 | — | kernel (`h5_eq`) |
| 6 | 720 | 5 | — | kernel (`h6_eq`) |
| 7 | 5040 | 5 | — | kernel (`h7_eq`) |
| 8 | 40320 | 6 | — | kernel (`h8_eq`) |
| 9 | 362880 | 7 | 362783 | kernel (`E18/H9_10.lean`, `h9_eq`) |
| 10 | 3628800 | 7 | 2979161 | kernel (`h10_eq`) |
| 11 | 39916800 | 7 | 29749079 | **`native_decide`** (`E18/H11_native.lean`, `h11_eq`) |
| 12 | 479001600 | 8 | 475785157 | **`native_decide`** (`E18/H12_native.lean`, `h12_eq`; checked 23 Nov 2026, axioms in `axioms/h12_native.txt`); C and Python agree |

To our knowledge the public discussion went up to `n = 11`. The value
`h(12!) = 8` is offered as new data. It is checked in Lean with
`native_decide` (which trusts the compiler), not by the kernel alone.

### Problem #710 — `f(n)`

`f(n)` is the least `K` such that the numbers `1,…,n` can be matched to
distinct multiples in the open interval `(n, n+K)`. Exact values for
`n = 1..200` are proved in Lean from an explicit matching (upper bound)
and a Hall certificate (lower bound):

- `E710/F1_50.lean` — `f_1` … `f_50`
- `E710/F51_200.lean` — `f_51` … `f_200`

All of these are kernel-checked. The values agree with
[OEIS A390246](https://oeis.org/A390246) (b-file in
`computations/e710/b390246.txt`). A few entries:

`2, 3, 4, 6, 6, 9, 9, 11, 13, 15, 15, 17, 16, 19, 20, 25, 24, 27, 26, 29, …`
and `f(200) = 341`.

A small remark, also kernel-checked (`R6E710.f_eq_g_sub`): the conjecture
stated in A390246 that `a(n) = A219787(n) − (n−1)` holds for every
`n ≥ 1`, because the two sequences describe the same quantity on an open
versus a closed interval.

### Problem #711 — `f(n,m)`

`f(n,m)` is the same matching problem in the interval `(m, m+K)` rather
than `(n, n+K)`. Two general facts are kernel-checked in `R6E711Core.lean`:

- **Periodicity** (`good_mod`): if `P` is a common multiple of `1,…,n`,
  then `f(n,m)` depends only on `m` modulo `P`. In particular the maximum
  over `m` is a finite computation, of length `lcm(1..n)`.
- **A uniform lower bound** (`f_sq_ge`): for every `n ≥ 2`,
  `f(n, (n-1)²) ≥ 2n−1`. (In the interval starting at `(n-1)²`, the
  indices `n−1` and `n` share the single multiple `n(n−1)`.)

Exact maxima over `m`, kernel-checked for every residue class, for
`3 ≤ n ≤ 10`:

| `n` | `max_m f(n,m)` | pattern `2n−1` | Lean |
| ---: | ---: | --- | --- |
| 3 | 5 | yes | `E711/M3.lean`, `max3` |
| 4 | 7 | yes | `M4.lean` |
| 5 | 9 | yes | `M5.lean` |
| 6 | 11 | yes | `M6.lean` |
| 7 | 13 | yes | `M7.lean` |
| 8 | 15 | yes | `M8.lean` |
| 9 | 17 | yes | `M9.lean` |
| 10 | 19 | yes | `M10.lean` |

The pattern `max_m f(n,m) = 2n−1` continues computationally through
`n = 16`, and **breaks at `n = 17`**:

- kernel-checked: `f(17, 485749) = 34 > 33` (`E711/F17.lean`, `f17` and
  `f17_gt`). Hall certificate: the indices `{11,12,13,14,15,17}` have all
  their multiples in `(485749, 485782)` among the five numbers
  `485758, 485760, 485771, 485772, 485775`.

Exhaustive C search (`computations/e711/f711.c`, `f711b.c`) gives
`max_m f(n,m)` for `n = 1..22`:

```
n:     1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22
max:   2  3  5  7  9 11 13 15 17 19 21 23 25 27 29 31 34 35 40 43 43 49
```

The entries for `n = 11..16` and `n = 18..22` are **exhaustive
computation only** (not Lean). This sequence does not appear to be in the
OEIS. Recorded outputs: `max711_18.txt` … `max711_22.txt`. The maxima are
attained at `m = 1407302` (`n = 19`), `m = 790370` (`n = 20` and `21`) and
`m = 503104` (`n = 22`); for `n = 20, 21, 22` the value of `f(n,m)` at these
`m` was rechecked independently in Python (networkx bipartite matching).
For comparison, `f(n,n) = 26, 29, 30, 31` for `n = 19, 20, 21, 22`.

## Build

```bash
# optional, uses the community cache
lake exe cache get

# the three core libraries (definitions and general lemmas)
lake build R6E18Core R6E710Core R6E711Core

# kernel-checked instances (light)
lake env lean E18/H3_8.lean
lake env lean E18/H9_10.lean
lake env lean E711/F17.lean
lake env lean E711/M3.lean   # similarly M4, M5, M6

# heavier kernel-checked instances — several GB of RAM
lake env lean E710/F1_50.lean
lake env lean E710/F51_200.lean
lake env lean E711/M7.lean    # M8, M9, M10 are larger still
```

`E18/H11_native.lean` uses `native_decide` and also needs several GB of
RAM. `E18/H12_native.lean` uses `native_decide` as well; it completed on
23 Nov 2026 (about 30 minutes) and needs a comfortable margin of free
memory (an earlier attempt was stopped at a limit of about 10.5 GB).

Recorded `#print axioms` traces are in `axioms/`.

The first build will download Mathlib and may take substantial disk space
and time. On the machine where this repository was prepared, a full
rebuild of the large instance files was not repeated at publication time,
in order not to compete for memory with an unrelated long-running
computation. The light files listed above were rechecked with
`lake env lean` against Lean 4.36.0 and Mathlib v4.36.0; the heavier
files had been checked earlier in the same toolchain, and their sources
are unchanged.

## Programs

See [`computations/README.md`](computations/README.md) for how to run the
C and Python programs that generated the certificates and the
computational values.

## Problems that remain open

- `#18` asks for the behaviour of `h(n)` in general, not only at
  factorials, and even `h(n!)` is not given here for `n ≥ 13`.
- `#710` asks for the asymptotic size of `f(n)`; the values up to 200 do
  not settle it.
- `#711` asks for the behaviour of `f(n,m)` in general; the break of the
  pattern `2n−1` at `n = 17` and the values up to `n = 22` are data, not a solution.

See also https://github.com/IronCodeTrade/erdos-128-n23 (Erdős #128, no
counterexample for `n ≤ 23`).
