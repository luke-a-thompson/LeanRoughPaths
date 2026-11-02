# LeanRoughPaths

[![CI](https://github.com/daniil-shmelev/LeanRoughPaths/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanRoughPaths/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.32-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Rough Path theory in Lean 4.

## Building

```
lake exe cache get
lake build
```


### Iterated areas

`HopfAlgebras.Word.Polynomial.word_generated` proves that every word is a rational shuffle
polynomial in letters and nested signed areas, preserving each letter's
multiplicity. The proof uses the half-shuffle product rule and induction on
the number of factors; it does not require a free-Lie or Dynkin dependency.

`RoughPaths.Signature.ext_of_area_eq` and `eq_of_area_eq_weight` give full and
weighted signature determination. `Signature.derivative_pairing_area` identifies
the signed-area derivative for polynomial signature coordinates satisfying the
word differential recursion. `Word.PolynomialPath.eval_one` recovers the Chen
segment update from constant letter velocities.

`RoughPaths.AreaReduction.diff_primitive` supplies the corresponding polynomial
reduction for any labelled family closed under signed area. It contains no
rooted trees or numerical-method assumptions; LeanBSeries supplies those.

References: Diehl–Lyons–Preiß–Reizenstein, *Areas of areas generate the shuffle
algebra*, Corollary 4.8; Salvi et al., *A structure theorem for streamed
information*, §4. Tests and axiom audits are in `Tests/Area.lean`.
