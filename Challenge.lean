import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Ehlich–Wojtas determinant bound

Let `M` be an `n × n` matrix with entries in `{±1}` and `n ≡ 2 (mod 4)`.
Then

```
|det M| ≤ (2n − 2) (n − 2)^{n/2 − 1}.
```

This is the bound independently proved by Ehlich and by Wojtas. The statement
matches Theorem 19 of Browne, Egan, Hegarty and Ó Catháin, *A Survey of the
Hadamard Maximal Determinant Problem*, Electron. J. Combin. 28 (4) (2021),
#P4.41, which follows Wojtas’s determinant-theoretic argument.

On `ℕ`, `0 ^ 0 = 1`, so the `n = 2` case is the classical bound `|det M| ≤ 2`.

## References

* H. Ehlich, Determinantenabschätzungen für binäre Matrizen,
  *Math. Z.* 83 (1964), 123–132. DOI: 10.1007/BF01111162
* M. Wojtas, On Hadamard’s inequality for the determinants of order
  non-divisible by 4, *Colloq. Math.* 12 (1964), 73–83.
* P. Browne, R. Egan, F. Hegarty, P. Ó Catháin, Electron. J. Combin. 28 (4)
  (2021), #P4.41, Theorem 19. DOI: 10.37236/10367
-/

namespace EhlichWojtas

/-- The Ehlich–Wojtas bound for `{±1}`-matrices of order `n ≡ 2 (mod 4)`. -/
theorem ehlich_wojtas_bound {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    M.det.natAbs ≤ (2 * n - 2) * (n - 2) ^ (n / 2 - 1) := by
  sorry

end EhlichWojtas
