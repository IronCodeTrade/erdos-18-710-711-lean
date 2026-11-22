# Licence, authorship and AI assistance

This repository is released under CC0 1.0 (`LICENSE`).

## Authorship

The Lean formalisations, programs and the short note in `paper/` were prepared
for Krzysztof Paweł Michalak (GitHub: [IronCodeTrade](https://github.com/IronCodeTrade)).

Contact: krzysztof.michalak.biz@gmail.com

## AI assistance

An AI assistant (Grok Bot, running in Cursor) was used to write Lean code,
search programs and documentation, under the direction of the author. The
mathematical claims that are marked as kernel-checked have been verified by
the Lean 4.36.0 kernel (axioms: `propext`, `Classical.choice`, `Quot.sound`
only). Claims that use `native_decide`, and claims that rest only on C or
Python programs, are labelled as such and should not be cited as
kernel-checked theorems.

## This does not solve the problems

The files here are small cases and supporting lemmas for
[Erdős problems #18](https://www.erdosproblems.com/18),
[#710](https://www.erdosproblems.com/710) and
[#711](https://www.erdosproblems.com/711). None of these problems is solved
by this repository.
