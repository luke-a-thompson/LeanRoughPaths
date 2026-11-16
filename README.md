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

## Area reduction

`HopfAlgebras.Word.AreaReduction.diff_primitive` reduces the integral of a
product of moments against one more moment, for any labelled family closed
under signed area. `eval_segment` is Chen's identity for such moment
polynomials along a straight segment, over any field of characteristic zero.
Neither refers to rooted trees or numerical methods; LeanBSeries supplies
those for the Williamson order-transfer theorem.
