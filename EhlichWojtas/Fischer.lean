import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Fischer’s inequality for a real positive definite 2×2 block matrix.
-/

namespace EhlichWojtas

open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `C` and `1 - C` are PSD, every eigenvalue of `C` is at most `1`. -/
lemma posSemidef_eigenvalues_le_one {C : Matrix n n ℝ}
    (hC : C.PosSemidef) (hle : (1 - C).PosSemidef) (i : n) :
    hC.1.eigenvalues i ≤ 1 := by
  set v := ⇑(hC.1.eigenvectorBasis i)
  have hnn : 0 ≤ star v ⬝ᵥ ((1 - C) *ᵥ v) := hle.dotProduct_mulVec_nonneg v
  have hCv : C *ᵥ v = hC.1.eigenvalues i • v := hC.1.mulVec_eigenvectorBasis i
  have hv1 : v ⬝ᵥ v = 1 := by
    have hon := (orthonormal_iff_ite.1 hC.1.eigenvectorBasis.orthonormal) i i
    simp only [↓reduceIte] at hon
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hon
    simpa [v, star_trivial, dotProduct_comm] using hon
  have hval : star v ⬝ᵥ ((1 - C) *ᵥ v) = 1 - hC.1.eigenvalues i := by
    simp [sub_mulVec, one_mulVec, hCv, dotProduct_sub, dotProduct_smul, star_trivial, hv1]
  linarith

lemma posSemidef_det_le_one_of_le_one {C : Matrix n n ℝ}
    (hC : C.PosSemidef) (hle : (1 - C).PosSemidef) :
    C.det ≤ 1 := by
  have hprod : C.det = ∏ i, (hC.1.eigenvalues i : ℝ) :=
    hC.1.det_eq_prod_eigenvalues
  calc
    C.det = ∏ i, (hC.1.eigenvalues i : ℝ) := hprod
    _ ≤ ∏ _i : n, (1 : ℝ) := by
      refine Finset.prod_le_prod (fun i _ => hC.eigenvalues_nonneg i) fun i _ => ?_
      exact posSemidef_eigenvalues_le_one hC hle i
    _ = 1 := by simp

/-- If `S` is PSD, `D` is PD, and `D - S` is PSD, then `det S ≤ det D`. -/
theorem det_le_of_posSemidef_le {S D : Matrix n n ℝ}
    (hS : S.PosSemidef) (hD : D.PosDef) (hle : (D - S).PosSemidef) :
    S.det ≤ D.det := by
  set Q := CFC.sqrt D
  have hQsq : Q * Q = D := CFC.sqrt_mul_sqrt_self D
  have hQpos : Q.PosDef := hD.isStrictlyPositive.sqrt.posDef
  haveI : Invertible Q := hQpos.isUnit.invertible
  have hQinv : Q⁻¹ * Q = 1 := inv_mul_of_invertible Q
  have hQinv' : Q * Q⁻¹ = 1 := mul_inv_of_invertible Q
  have hstarQ : star Q = Q := (CFC.sqrt_nonneg D).star_eq
  have hstar : star Q⁻¹ = Q⁻¹ := by
    have hQher : Q.IsHermitian := hstarQ
    have hinv : Q⁻¹.IsHermitian := hQher.inv
    exact hinv
  let C : Matrix n n ℝ := Q⁻¹ * S * Q⁻¹
  have hU : IsUnit Q⁻¹ := isUnit_nonsing_inv_iff.2 hQpos.isUnit
  have hCpsd : C.PosSemidef := by
    simpa [C, hstar] using hU.posSemidef_star_right_conjugate_iff.2 hS
  have h1 : (1 : Matrix n n ℝ) = Q⁻¹ * D * Q⁻¹ := by
    calc
      (1 : Matrix n n ℝ) = Q⁻¹ * Q := hQinv.symm
      _ = Q⁻¹ * Q * 1 := (mul_one _).symm
      _ = Q⁻¹ * Q * (Q * Q⁻¹) := by rw [hQinv']
      _ = Q⁻¹ * (Q * Q) * Q⁻¹ := by simp
      _ = Q⁻¹ * D * Q⁻¹ := by rw [hQsq]
  have hCle1 : (1 - C).PosSemidef := by
    have hform : 1 - C = Q⁻¹ * (D - S) * Q⁻¹ := by
      simp [C, h1, mul_sub, sub_mul]
    simpa [hform, hstar] using hU.posSemidef_star_right_conjugate_iff.2 hle
  have hdetC : C.det ≤ 1 := posSemidef_det_le_one_of_le_one hCpsd hCle1
  have hSQ : S = Q * C * Q := by
    simp only [C]
    calc
      S = (1 : Matrix n n ℝ) * S * 1 := by simp
      _ = (Q * Q⁻¹) * S * (Q⁻¹ * Q) := by rw [hQinv', hQinv]
      _ = Q * (Q⁻¹ * S * Q⁻¹) * Q := by simp [mul_assoc]
  have hdetS : S.det = C.det * D.det := by
    have hQCQ : (Q * C * Q).det = Q.det * C.det * Q.det := by
      simp only [det_mul]
    have hQ2 : Q.det * Q.det = (Q * Q).det := (det_mul Q Q).symm
    calc
      S.det = (Q * C * Q).det := by rw [hSQ]
      _ = Q.det * C.det * Q.det := hQCQ
      _ = C.det * (Q.det * Q.det) := by ring
      _ = C.det * (Q * Q).det := by rw [hQ2]
      _ = C.det * D.det := by rw [hQsq]
  nlinarith [hdetC, hD.det_pos]

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]

set_option linter.unusedSectionVars false

lemma posDef_block₁₁ {A : Matrix l l ℝ} {B : Matrix l m ℝ} {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) : A.PosDef := by
  have h := hG.submatrix (e := Sum.inl) Sum.inl_injective
  convert h
  ext i j
  simp [fromBlocks]

lemma posDef_block₂₂ {A : Matrix l l ℝ} {B : Matrix l m ℝ} {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) : D.PosDef := by
  have h := hG.submatrix (e := Sum.inr) Sum.inr_injective
  convert h
  ext i j
  simp [fromBlocks]

/-- Fischer’s inequality. -/
theorem fischer {A : Matrix l l ℝ} (B : Matrix l m ℝ) {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) :
    (fromBlocks A B Bᵀ D).det ≤ A.det * D.det := by
  have hA : A.PosDef := posDef_block₁₁ hG
  have hDblk : D.PosDef := posDef_block₂₂ hG
  haveI : Invertible A := hA.isUnit.invertible
  have hSchur : (D - Bᵀ * A⁻¹ * B).PosSemidef := by
    have hiff := PosDef.fromBlocks₁₁ (A := A) (B := B) (D := D) hA
    have hpsd : (fromBlocks A B Bᴴ D).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hG.posSemidef
    simpa [conjTranspose_eq_transpose_of_trivial] using hiff.1 hpsd
  have hPSD : (Bᵀ * A⁻¹ * B).PosSemidef := by
    have hAinv : A⁻¹.PosDef := (Matrix.posDef_inv_iff (M := A)).2 hA
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hAinv.posSemidef.conjTranspose_mul_mul_same B
  have hSle : (D - Bᵀ * A⁻¹ * B).det ≤ D.det :=
    det_le_of_posSemidef_le hSchur hDblk (by simpa using hPSD)
  have hdet := det_fromBlocks₁₁ A B Bᵀ D
  calc
    (fromBlocks A B Bᵀ D).det = A.det * (D - Bᵀ * A⁻¹ * B).det := by
      simpa [invOf_eq_nonsing_inv] using hdet
    _ ≤ A.det * D.det := by
      have : 0 ≤ A.det := hA.posSemidef.det_nonneg
      nlinarith [hSle]

end EhlichWojtas
