import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Hadamard’s inequality for real positive definite matrices: `det A ≤ ∏ Aᵢᵢ`.
-/

namespace EhlichWojtas

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma posDef_conj_inv_diagonal {A : Matrix n n ℝ} (hA : A.PosDef)
    {d : n → ℝ} (hd : ∀ i, 0 < d i) :
    ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).PosDef := by
  have hD : (diagonal d).PosDef := PosDef.diagonal hd
  have hU : IsUnit (diagonal d)⁻¹ := isUnit_nonsing_inv_of_invertible _
  have hstar : star (diagonal d)⁻¹ = (diagonal d)⁻¹ := by
    simp [star_eq_conjTranspose, conjTranspose_nonsing_inv, hD.isHermitian]
  simpa [hstar] using (hU.posDef_star_right_conjugate_iff.2 hA)

lemma correlation_diag {A : Matrix n n ℝ} (hA : A.PosDef)
    (d : n → ℝ) (hd : ∀ i, d i = Real.sqrt (A i i)) (i : n) :
    ((diagonal d)⁻¹ * A * (diagonal d)⁻¹) i i = 1 := by
  have hdi : d i ≠ 0 := by
    have := hA.diag_pos (i := i)
    have : 0 < d i := by
      rw [hd]
      exact Real.sqrt_pos.2 this
    exact this.ne'
  have hinv : (diagonal d)⁻¹ i i = (d i)⁻¹ := by
    rw [inv_diagonal]
    simp [Pi.inv_apply]
  simp [Matrix.mul_apply, diagonal, hinv]
  have hsq : d i ^ 2 = A i i := by
    rw [hd]
    exact Real.sq_sqrt (hA.diag_pos (i := i)).le
  field_simp [hdi, (hA.diag_pos (i := i)).ne']
  nlinarith [hsq]

lemma posDef_det_eq_corr_mul_prod {A : Matrix n n ℝ} (hA : A.PosDef)
    (d : n → ℝ) (hd : ∀ i, d i = Real.sqrt (A i i)) :
    A.det =
      ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).det * ∏ i, A i i := by
  have hdpos : ∀ i, 0 < d i := fun i => by
    rw [hd]
    exact Real.sqrt_pos.2 (hA.diag_pos (i := i))
  have hD : (diagonal d).PosDef := PosDef.diagonal hdpos
  have hdetD : (diagonal d).det = ∏ i, d i := det_diagonal
  have hinv : ((diagonal d)⁻¹).det = ((diagonal d).det)⁻¹ := det_nonsing_inv
  have hC :
      ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).det =
        ((diagonal d)⁻¹.det) ^ 2 * A.det := by
    simp [det_mul, pow_two]
  have hprod : ((diagonal d).det) ^ 2 = ∏ i, A i i := by
    rw [hdetD, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hd]
    exact Real.sq_sqrt (hA.diag_pos (i := i)).le
  have hne : (diagonal d).det ≠ 0 := hD.det_pos.ne'
  field_simp [hC, hinv, hprod, hne]
  ring

lemma posDef_corr_eigen_prod_le_one {C : Matrix n n ℝ} (hC : C.PosDef)
    (hCii : ∀ i, C i i = 1) :
    (∏ i, (hC.isHermitian.eigenvalues i : ℝ)) ≤ 1 := by
  rcases isEmpty_or_nonempty n with hι | hι
  · simp [Fintype.card_eq_zero]
  have hλpos : ∀ i, 0 < hC.isHermitian.eigenvalues i := hC.eigenvalues_pos
  have htr : C.trace = Fintype.card n := by
    simp [trace, hCii]
  have hsum : ∑ i, hC.isHermitian.eigenvalues i = C.trace :=
    hC.isHermitian.trace_eq_sum_eigenvalues
  have hw' : 0 < ∑ _i : n, (1 : ℝ) := by
    simp [Finset.card_univ, Fintype.card_pos]
  have hAMGM :=
    Real.geom_mean_le_arith_mean Finset.univ (fun _ : n => (1 : ℝ))
      (fun i => hC.isHermitian.eigenvalues i)
      (fun _ _ => by norm_num) hw'
      (fun i _ => (hλpos i).le)
  have hmean : (∑ i, (1 : ℝ) * hC.isHermitian.eigenvalues i) / ∑ _i : n, (1 : ℝ) = 1 := by
    simp [hsum, htr, Finset.card_univ]
  have hgeom :
      (∏ i, hC.isHermitian.eigenvalues i) ^ (Fintype.card n : ℝ)⁻¹ ≤ 1 := by
    convert hAMGM.trans_eq hmean using 2
    · simp
    · simp [Finset.card_univ]
  have hn : 0 < (Fintype.card n : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hpow :=
    Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => (hλpos i).le) hgeom hn.le
  have hinv : ((Fintype.card n : ℝ)⁻¹) * Fintype.card n = 1 := by
    field_simp [hn.ne']
  simpa [Real.rpow_mul (Finset.prod_nonneg fun i _ => (hλpos i).le), hinv,
    Real.rpow_one, Real.one_rpow, Real.rpow_natCast] using hpow

/-- Hadamard’s inequality for a real positive definite matrix. -/
theorem posDef_det_le_prod_diag (A : Matrix n n ℝ) (hA : A.PosDef) :
    A.det ≤ ∏ i, A i i := by
  let d : n → ℝ := fun i => Real.sqrt (A i i)
  have hd : ∀ i, d i = Real.sqrt (A i i) := fun _ => rfl
  let C : Matrix n n ℝ := (diagonal d)⁻¹ * A * (diagonal d)⁻¹
  have hC : C.PosDef := posDef_conj_inv_diagonal hA fun i =>
    Real.sqrt_pos.2 (hA.diag_pos (i := i))
  have hCii : ∀ i, C i i = 1 := fun i => correlation_diag hA d hd i
  have hdet := posDef_det_eq_corr_mul_prod hA d hd
  have hprodλ : C.det = ∏ i, (hC.isHermitian.eigenvalues i : ℝ) :=
    hC.isHermitian.det_eq_prod_eigenvalues
  have hle := posDef_corr_eigen_prod_le_one hC hCii
  calc
    A.det = C.det * ∏ i, A i i := hdet
    _ = (∏ i, (hC.isHermitian.eigenvalues i : ℝ)) * ∏ i, A i i := by rw [hprodλ]
    _ ≤ 1 * ∏ i, A i i := by gcongr
    _ = ∏ i, A i i := by simp

end EhlichWojtas
