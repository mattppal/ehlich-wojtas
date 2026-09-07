import EhlichWojtas.Bound
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Palomar solution module: the Ehlich–Wojtas bound.
-/

namespace EhlichWojtas

theorem ehlich_wojtas_bound {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    M.det.natAbs ≤ (2 * n - 2) * (n - 2) ^ (n / 2 - 1) :=
  ehlich_wojtas_bound_main hn M hM

end EhlichWojtas
