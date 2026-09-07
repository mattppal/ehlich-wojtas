# The Ehlich–Wojtas determinant bound

Lean 4 formalization of the 1964 Ehlich–Wojtas upper bound: if `M` is an
`n × n` matrix with entries in `{±1}` and `n ≡ 2 (mod 4)`, then

```
|det M| ≤ (2n − 2) (n − 2)^{n/2 − 1}.
```

The advertised statement is `EhlichWojtas.ehlich_wojtas_bound` in
[`Challenge.lean`](Challenge.lean). The proof is in the `EhlichWojtas`
library and is re-exported from [`Solution.lean`](Solution.lean) for
[Palomar](https://palomar-registry.org/) Comparator.

On `ℕ`, `0 ^ 0 = 1`, so the `n = 2` case is `|det M| ≤ 2`.

## Build

Requires [elan](https://github.com/leanprover/elan) and Lean 4.32.0
(see [`lean-toolchain`](lean-toolchain)). Mathlib is pinned in
[`lake-manifest.json`](lake-manifest.json).

```bash
lake build
./scripts/verify.sh
./scripts/verify-submit.sh
```

`verify.sh` rebuilds the project, checks Palomar metadata, checks that
the proof development contains no `sorry`, and checks the bound at
`n = 2, 6, 10`.

`verify-submit.sh` also runs the PalomarTemplate Comparator pins
(`scripts/verify-comparator.sh`). That step needs Go, Cargo, Landrun,
lean4export, and NanoDa.

## Proof outline

The argument follows Wojtas as written in Browne, Egan, Hegarty and
Ó Catháin, Electron. J. Combin. 28 (4) (2021), Theorem 19.

1. [`EhlichWojtas/Gram.lean`](EhlichWojtas/Gram.lean) — the integer Gram
   matrix `G = M Mᵀ` has diagonal `n`, even entries, and a 4-cycle
   congruence that splits `{1,…,n}` into two classes on which
   off-diagonal entries are `≡ 2 (mod 4)`.
2. [`EhlichWojtas/Hadamard.lean`](EhlichWojtas/Hadamard.lean) —
   `det A ≤ ∏ Aᵢᵢ` for a real positive definite matrix.
3. [`EhlichWojtas/Fischer.lean`](EhlichWojtas/Fischer.lean) —
   `det G ≤ det A · det D` for a positive definite `2×2` block matrix.
4. [`EhlichWojtas/Block.lean`](EhlichWojtas/Block.lean) — Wojtas’s bound
   for a positive definite matrix whose off-diagonal entries have
   magnitude at least `b` (Browne et al., Theorem 8).
5. [`EhlichWojtas/Bound.lean`](EhlichWojtas/Bound.lean) — assemble the
   pieces. If every off-diagonal Gram entry has magnitude at least `2`,
   apply Wojtas directly. Otherwise apply Fischer to the two classes and
   Wojtas on each diagonal block.

## Palomar files

| File | Role |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | Auditable statement (`sorry`) |
| [`Solution.lean`](Solution.lean) | Matching proof |
| [`comparator.json`](comparator.json) | Compared declaration |
| [`formalization.yaml`](formalization.yaml) | Provenance and metadata |
| [`NOVELTY.md`](NOVELTY.md) | What is and is not claimed as new |
| [`VERIFICATION.md`](VERIFICATION.md) | Checks that were run |
| [`SUBMIT.md`](SUBMIT.md) | How to register the result on Palomar |
| [`LICENSE`](LICENSE) | Apache-2.0 |

## References

* H. Ehlich, Determinantenabschätzungen für binäre Matrizen, *Math. Z.*
  83 (1964), 123–132. DOI: [10.1007/BF01111162](https://doi.org/10.1007/BF01111162)
* M. Wojtas, On Hadamard’s inequality for the determinants of order
  non-divisible by 4, *Colloq. Math.* 12 (1964), 73–83.
  DOI: [10.4064/cm-12-1-73-83](https://doi.org/10.4064/cm-12-1-73-83)
* P. Browne, R. Egan, F. Hegarty, P. Ó Catháin, A Survey of the Hadamard
  Maximal Determinant Problem, *Electron. J. Combin.* 28 (4) (2021),
  #P4.41, Theorem 19. DOI: [10.37236/10367](https://doi.org/10.37236/10367),
  arXiv: [2104.06756](https://arxiv.org/abs/2104.06756)
