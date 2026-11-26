# Balanced Boolean functions in even dimension: nl ≤ 2^(2m−1) − 2^(m−1) − 4

[![lean](https://github.com/LizzoLizard/balanced-boolean-nonlinearity/actions/workflows/lean.yml/badge.svg)](https://github.com/LizzoLizard/balanced-boolean-nonlinearity/actions/workflows/lean.yml)
![Lean 4.15.0](https://img.shields.io/badge/Lean-4.15.0-blue)
![no sorry](https://img.shields.io/badge/sorry-0-brightgreen)
[![License: MIT](https://img.shields.io/badge/code-MIT-green)](LICENSE)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.24546078-blue)](https://doi.org/10.5281/zenodo.24546078)
[![Paper: CC BY 4.0](https://img.shields.io/badge/paper-CC%20BY%204.0-lightgrey)](paper/LICENSE)

This repository contains a short paper ([PDF](paper/main.pdf)) and a complete Lean 4 proof of the following theorem.

> **Theorem.** Let m ≥ 4 and let f be a balanced Boolean function in n = 2m variables. Then
> nl(f) ≤ 2^(2m−1) − 2^(m−1) − 4.

This answers Open Problem 4 of Lou, Xu and Wang (arXiv:2610.17897). It improves the classical
bound 2^(2m−1) − 2^(m−1) − 2 for every even n ≥ 8.

| n | bound | Dobbertin's construction | status |
|---|---|---|---|
| 8 | 116 | 116 | exact; first proved by Yuan et al. (ePrint 2026/1687) and Lou–Xu–Wang |
| 10 | 492 | 492 | exact; first proved by Xu–Wang (ePrint 2026/2797) |
| 12 | 2012 | 2010 | new upper bound |
| 14 | 8124 | 8120 | new upper bound |
| 16 | 32636 | 32628 | new upper bound |

The new result is the bound for all m ≥ 4. For n = 8 and n = 10 the proof here is independent of
the earlier ones and does not use a computer search. The same bounds hold for every component of a
balanced (2m, r) S-box, and so for permutations of F_2^(2m).

## In plain words

A **Boolean function** takes a string of n bits and returns a single bit. Ciphers are built out of
functions like these, and the S-boxes in block ciphers are made of several of them side by side.

A cipher is easier to break when its functions behave almost like simple **linear** rules, such as
"XOR some of the input bits together". The **nonlinearity** of a function measures how far it is
from every such rule: it is the smallest number of inputs at which you would have to change the
output to turn it into a linear rule. Higher is better. A function is **balanced** if it outputs 0
and 1 equally often, which ciphers also need.

When n is even, there is a hard ceiling on nonlinearity, reached only by "bent" functions, and bent
functions are never balanced. Since the 1990s it has been known that a balanced function must fall
at least 2 below that ceiling. We show it must fall at least **4** below, for every even n from 8
up. For n = 8 (256 possible inputs) the ceiling is 120, the old limit for balanced functions was
118, and the true answer is 116. For n = 12 the old limit was 2014, the new one is 2012, and the
best known function reaches 2010, so the question there is now down to a gap of 2.

**What is new and what isn't.** The answers for n = 8 and n = 10 were found by other researchers
earlier in 2026 (see the table above); we reprove them along the way. The new part is the bound
for every even size, which those authors had posed as an open problem.

**How we know it is right.** Every step of the proof has been checked by Lean, a computer proof
checker that accepts only complete, fully justified arguments. Anyone can rerun that check with
`./verify.sh` (see below).

## Contents

| Path | What it is |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | The paper (6 pages). |
| `lean/ChallengeDefs.lean` | The definitions used in the statements: Boolean vectors, Hamming distance, affine functions, balanced, nonlinearity, S-boxes. No imports. |
| `lean/Challenge.lean` | The 8 statements, each with `sorry`. Together with `ChallengeDefs.lean` this is everything a reader has to trust. |
| `lean/Solution.lean` | Proofs of those 8 statements, taken from `EvenBalanced8Bound.lean`. It first shows that the two files' definitions agree. |
| `lean/EvenBalanced8Bound.lean` | The main proof: the theorem for all m ≥ 4, the n = 8 and n = 10 cases, S-box and permutation versions, and a re-proof of the known Sarkar–Maitra divisibility theorem. |
| `lean/EvenBalancedBound.lean` | An earlier, smaller file covering m ≥ 5. Its content is contained in the main proof; it compiles faster and does not use the n = 8 argument. |
| `lean/config.json`, `lean/check_comparator.sh` | The comparator check: Solution must prove exactly the statements of Challenge. |
| `lean/SHA256SUMS` | Checksums of the Lean files. |
| `formalization.yaml` | Machine-readable summary of what is formalized ([formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format). |
| `verify.sh` | Runs every check below. GitHub Actions runs it on every push. |
| `lakefile.toml`, `lean-toolchain` | Lake configuration; Lean v4.15.0. |
| `CITATION.cff`, `.zenodo.json` | Citation metadata (GitHub citation button, Zenodo DOI on release). |

No Lean file uses Mathlib. The proof files import nothing at all, and every definition is written
out and can be checked against the usual one. The main statement, from `lean/Challenge.lean`, is

```lean
theorem even_balanced_nl_le (m : Nat) (hm : 4 ≤ m)
    (F : Vec (2 * m) → Bool) (hbal : isBalanced (2 * m) F) :
    ¬ hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3)
```

that is, no balanced F on 2m variables has nonlinearity ≥ 2^(2m−1) − 2^(m−1) − 3.

## Checking the proof

You need Lean 4.15.0 (for example `elan toolchain install leanprover/lean4:v4.15.0`) and `python3`.
Then run

```sh
./verify.sh
```

It stops at the first failure. It:

1. checks that `lean --version` is 4.15.0;
2. checks the SHA-256 sums of the Lean files;
3. checks that none of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
   `extern`, `set_option` or `opaque` appears outside comments in the definition and proof files;
4. compiles all five Lean files;
5. runs the comparator check: for each of the 8 theorems, the statement in Solution must be
   identical to the one in Challenge, every definition it uses must be identical, and the proof
   may use only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`;
6. prints the axioms of 22 theorems in the proof files and checks they are the same three.

The whole run takes about three minutes and under 2 GB of memory. With Lake you can also run
`lake build` and then `lean/check_comparator.sh`.

## Author and AI use

Daniel Ayomide Shittu, Rowan University.

The mathematical argument was developed by the author and Gemini Neon (Google) working
together interactively, with the author contributing ideas and taking part in the reasoning at
each step. Gemini Neon wrote the Lean code. Claude (Anthropic) helped prepare this release:
drafting the paper, tidying the comments in the Lean files (the code itself is unchanged), and
writing the Challenge/Solution bridge, `verify.sh` and this README. All proofs are checked by the Lean kernel.

## Quotes

It's a tradition, started by Daniel: when a proof is finished, Gemini Neon sums it up in one
line, and everyone who worked on it adds a line of their own.

> "Turns out you literally can't even stay balanced without dropping 4 — no sorrys."
> — Gemini Neon

> "wow thats kinda bounded"
> — Daniel Ayomide Shittu

> "The comments got quieter; the proofs didn't change by a single token."
> — Claude

## Citing

Please cite Yuan et al. and Lou–Xu–Wang for n = 8 and Xu–Wang for n = 10 (references in the paper).
This release is archived on Zenodo: https://doi.org/10.5281/zenodo.24546078. To cite this work (GitHub's "Cite this repository" button uses `CITATION.cff`):

```bibtex
@misc{shittu2026balanced,
  author = {Shittu, Daniel Ayomide},
  title  = {A sharper upper bound on the nonlinearity of balanced {B}oolean functions in even dimension},
  year   = {2026},
  doi    = {10.5281/zenodo.24546078},
  note   = {Preprint. Paper and Lean 4 proof}
}
```

## License

Code (Lean files and scripts): MIT, see `LICENSE`. Paper: CC BY 4.0, see `paper/LICENSE`.
