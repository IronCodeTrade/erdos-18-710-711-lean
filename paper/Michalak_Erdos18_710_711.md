---
title: "Small formally verified data for Erdős problems #18, #710 and #711"
author: "Krzysztof Paweł Michalak"
date: "22 November 2026"
---

**Author.** Krzysztof Paweł Michalak.

**Email.** krzysztof.michalak.biz@gmail.com

**Code.** <https://github.com/IronCodeTrade/erdos-18-710-711-lean>

**Licence.** CC0 1.0.

This note records a few exact values and short lemmas for three Erdős problems. **It does not solve any of them.** The Lean 4 formalisations (toolchain Lean 4.36.0, Mathlib v4.36.0) are in the repository named above. An AI assistant was used to write code and documentation, under the author's direction. Claims below are labelled by the strength of the evidence: *kernel-checked* (Lean kernel only; axioms `propext`, `Classical.choice`, `Quot.sound`); *`native_decide`*; or *exhaustive computation* (C or Python, not a Lean proof).

## 1. Problem #18 — h(n!)

Write h(m) for the least c such that every integer k with 1 ≤ k < m is a sum of at most c distinct divisors of m. A bitset dynamic program for this quantity is proved correct once, in general, in `R6E18Core.lean`. Instantiating the prime factorisation of n! then yields:

| n | h(n!) | Evidence |
|--:|------:|----------|
| 3 | 2 | kernel |
| 4 | 3 | kernel |
| 5 | 4 | kernel |
| 6 | 5 | kernel |
| 7 | 5 | kernel |
| 8 | 6 | kernel |
| 9 | 7 | kernel (first k needing 7 divisors: 362783) |
| 10 | 7 | kernel (first k: 2979161) |
| 11 | 7 | `native_decide` (first k: 29749079) |
| 12 | 8 | C and Python, independently (first k: 475785157). A Lean file using `native_decide` is included but was not successfully checked, for lack of memory. |

The public discussion of this problem appears to have listed values up to n = 11. The value h(12!) = 8 is offered as computational data, not as a kernel-checked theorem.

## 2. Problem #710 — f(n)

Here f(n) is the least K such that 1, …, n admit distinct multiples in the open interval (n, n+K). For each n = 1, …, 200, Lean checks an explicit matching (so f(n) ≤ K) and a Hall certificate (so f(n) > K−1). These proofs are kernel-checked and agree with OEIS A390246. In particular f(1) = 2, f(10) = 15, f(100) = 161, f(200) = 341.

The comment on A390246 conjecturing a(n) = A219787(n) − (n−1) holds for every n ≥ 1: both sequences describe the same matching, on an open versus a closed interval. This identity is kernel-checked as `R6E710.f_eq_g_sub`.

## 3. Problem #711 — f(n, m)

The same matching problem in the interval (m, m+K) is denoted f(n, m). Two general facts are kernel-checked:

- **Periodicity.** If P is a common multiple of 1, …, n, then f(n, m) depends only on m modulo P. Thus max_m f(n, m) is a finite computation of length lcm(1..n).
- **A uniform lower bound.** For every n ≥ 2, f(n, (n−1)²) ≥ 2n − 1.

The exact maximum over m is kernel-checked for every residue class when 3 ≤ n ≤ 10: it equals 2n − 1. An exhaustive C search continues this pattern through n = 16, and the pattern **breaks at n = 17**: kernel-checked, f(17, 485749) = 34 > 33. A Hall certificate is the set of indices {11, 12, 13, 14, 15, 17}, all of whose multiples in (485749, 485782) lie among the five numbers 485758, 485760, 485771, 485772, 485775.

The C program gives the maxima for n = 1..19:

2, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 34, 35, 40.

The entries for n = 11..16, n = 18 and n = 19 are exhaustive computation only. For n = 19 the value 40 is attained at m = 1407302. This sequence does not appear to be in the OEIS.

## 4. What is not claimed

These are small cases and supporting lemmas. They do not determine the general behaviour of h(n), of f(n), or of f(n, m), and they do not earn a prize. The repository states, for each theorem, whether it was checked by the Lean kernel, by `native_decide`, or only by a program.
