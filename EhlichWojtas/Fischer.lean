import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Fischer’s inequality for a real positive definite 2×2 block matrix.
-/

namespace EhlichWojtas

open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma posSemidef_eigenvalues_le_one {C : Matrix n n ℝ}
    (hC : C.PosSemidef) (hle : (1 - C).PosSemidef) (i : n) :
    hC.1.eigenvalues i ≤ 1 := by
  have hi : hC.1.eigenvalues i ∈ spectrum ℝ C :=
    hC.1.eigenvalues_mem_spectrum_real i
  have hset := spectrum.singleton_sub_eq (R := ℝ) (A := Matrix n n ℝ) C (1 : ℝ)
  have hmem : (1 : ℝ) - hC.1.eigenvalues i ∈
      spectrum ℝ (algebraMap ℝ (Matrix n n ℝ) 1 - C) := by
    have : (1 : ℝ) - hC.1.eigenvalues i ∈ ({1} - spectrum ℝ C) :=
      ⟨1, rfl, hC.1.eigenvalues i, hi, sub_eq_add_neg _ _⟩
    simpa [hset] using this
  have h1 : algebraMap ℝ (Matrix n n ℝ) 1 = (1 : Matrix n n ℝ) := by simp
  rw [h1] at hmem
  have hnn :=
    (posSemidef_iff_isHermitian_and_spectrum_nonneg (𝕜 := ℝ) (A := (1 - C))).1 hle
  have : (0 : ℝ) ≤ (1 : ℝ) - hC.1.eigenvalues i := hnn.2 hmem
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
  have hQsq : CFC.sqrt D * CFC.sqrt D = D := CFC.sqrt_mul_sqrt_self D
  have hQpos : (CFC.sqrt D).PosDef :=
    (IsStrictlyPositive.sqrt (A := Matrix n n ℝ) D hD.isStrictlyPositive).posDef
  haveI : Invertible (CFC.sqrt D) := hQpos.isUnit.invertible
  let Q := CFC.sqrt D
  let C : Matrix n n ℝ := Q⁻¹ * S * Q⁻¹
  have hstar : star Q⁻¹ = Q⁻¹ := by
    simp [Q, star_eq_conjTranspose, conjTranspose_nonsing_inv, hQpos.isHermitian]
  have hCpsd : C.PosSemidef := by
    have hU : IsUnit Q⁻¹ := isUnit_nonsing_inv_of_invertible _
    simpa [C, hstar] using hU.posSemidef_star_right_conjugate_iff.2 hS
  have h1 : (1 : Matrix n n ℝ) = Q⁻¹ * D * Q⁻¹ := by
    calc
      (1 : Matrix n n ℝ) = Q⁻¹ * Q := by simp [Q]
      _ = Q⁻¹ * (Q * Q) * Q⁻¹ := by
        simp [hQsq, Matrix.mul_assoc]
      _ = Q⁻¹ * D * Q⁻¹ := by
        simp [hQsq, Matrix.mul_assoc]
  have hCle1 : (1 - C).PosSemidef := by
    have : 1 - C = Q⁻¹ * (D - S) * Q⁻¹ := by
      simp [C, h1, Matrix.mul_sub, Matrix.sub_mul]
    have hU : IsUnit Q⁻¹ := isUnit_nonsing_inv_of_invertible _
    simpa [this, hstar] using hU.posSemidef_star_right_conjugate_iff.2 hle
  have hdetC : C.det ≤ 1 := posSemidef_det_le_one_of_le_one hCpsd hCle1
  have hSQ : S = Q * C * Q := by
    simp [C, Matrix.mul_assoc, inv_mul_of_invertible, mul_inv_of_invertible]
  have hdetS : S.det = C.det * D.det := by
    calc
      S.det = (Q * C * Q).det := by rw [hSQ]
      _ = Q.det * C.det * Q.det := by simp [det_mul]
      _ = C.det * (Q.det) ^ 2 := by ring
      _ = C.det * D.det := by
        have := congrArg det hQsq
        simp [det_mul, pow_two] at this
        rw [← this]
  nlinarith [hD.det_pos]

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]

lemma posDef_block₁₁ {A : Matrix l l ℝ} {B : Matrix l m ℝ} {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) : A.PosDef :=
  hG.submatrix (e := Sum.inl) Sum.inl_injective

lemma posDef_block₂₂ {A : Matrix l l ℝ} {B : Matrix l m ℝ} {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) : D.PosDef :=
  hG.submatrix (e := Sum.inr) Sum.inr_injective

/-- Fischer’s inequality. -/
theorem fischer {A : Matrix l l ℝ} (B : Matrix l m ℝ) {D : Matrix m m ℝ}
    (hG : (fromBlocks A B Bᵀ D).PosDef) :
    (fromBlocks A B Bᵀ D).det ≤ A.det * D.det := by
  have hA : A.PosDef := posDef_block₁₁ hG
  have hDblk : D.PosDef := posDef_block₂₂ hG
  haveI : Invertible A := hA.isUnit.invertible
  have hSchur : (D - Bᵀ * A⁻¹ * B).PosSemidef := by
    have hiff := PosDef.fromBlocks₁₁ (A := A) (B := B) (D := D) hA
    refine hiff.1 ?_
    simpa [star_eq_conjTranspose] using hG.posSemidef
  have hPSD : (Bᵀ * A⁻¹ * B).PosSemidef := by
    have hAinv : A⁻¹.PosDef := (Matrix.posDef_inv_iff (M := A)).2 hA
    simpa [star_eq_conjTranspose] using
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
