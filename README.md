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

`Derivation.length_succ_nsmul_prod_smul` is integration by parts for any
derivation `D` on a commutative ring, with the signed-area form
`D.area x y = x • D y - y • D x`:

`(m + 1) • (∏ xᵢ) • D y = D (y * ∏ xᵢ) + ∑ᵢ (∏_{j ≠ i} xⱼ) • D.area xᵢ y`.

`HopfAlgebras.Word.AreaReduction.derivation_primitive` applies it to a
family closed under signed area: every `(∏ X tᵢ) • D (X v)` is `D` of an
explicit polynomial in the family. `eval_segment` is Chen's identity for
such moment polynomials along a straight segment, over any field of
characteristic zero. None of this refers to rooted trees or numerical
methods; LeanBSeries supplies those for the Williamson order-transfer
theorem.
