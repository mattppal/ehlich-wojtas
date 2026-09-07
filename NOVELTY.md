# Novelty

This repository formalizes a classical theorem. It does not claim a new
mathematical bound.

## The mathematical result

Ehlich (1964) and Wojtas (1964) independently proved that if `M` is an
`n × n` matrix with entries in `{±1}` and `n ≡ 2 (mod 4)`, then

```
|det M| ≤ (2n − 2) (n − 2)^{n/2 − 1}.
```

The same statement appears as Theorem 19 of Browne, Egan, Hegarty and
Ó Catháin, *A Survey of the Hadamard Maximal Determinant Problem*,
Electron. J. Combin. 28 (4) (2021), #P4.41. That is the write-up followed
here.

## What is claimed as new

The intended novelty is the machine-checked Lean 4 proof of this bound,
with an auditable Palomar Challenge statement. A GitHub code search for
`Ehlich` / `Wojtas` restricted to Lean, together with a check of mathlib
v4.32.0, found no existing formalization of the bound. Mathlib does
define Hadamard matrices (`Matrix.IsHadamard`) and the Hadamard product,
but not this determinant estimate, not Fischer’s inequality for a
positive definite block matrix, and not Hadamard’s `det A ≤ ∏ Aᵢᵢ`
inequality for real positive definite matrices.

Those three intermediate facts are standard. They are proved in this
library only because they are missing from the pinned mathlib revision,
not because they are original mathematics.

## What is not claimed

- A new proof of the Ehlich–Wojtas bound. The argument is Wojtas’s, as
  presented by Browne et al.: Gram matrix, 4-cycle congruence, two-class
  partition, Fischer, and the off-diagonal magnitude bound.
- The first discovery of the bound.
- Equality-case structure, constructions, or Ehlich’s `n ≡ 3 (mod 4)`
  analysis.
- An exhaustive literature search of every formalization archive. The
  searches above are the evidence we have; a missed formalization would
  change only the priority claim, not the correctness of the Lean proof.

## Fidelity

Browne et al. write `det(M) ≤ …`. The Lean statement uses `natAbs`, i.e.
`|det M|`. That is the intended inequality: determinants of `{±1}`-matrices
need not be positive, and the bound is an upper bound on magnitude.
