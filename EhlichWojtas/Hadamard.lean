import Mathlib.Algebra.Order.Star.Real
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

lemma inv_diagonal_apply {d : n → ℝ} (hd : ∀ i, d i ≠ 0) (i j : n) :
    (diagonal d)⁻¹ i j = if i = j then (d i)⁻¹ else 0 := by
  have hmul : diagonal d * diagonal (fun k => (d k)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]
    ext a b
    simp [diagonal_apply, one_apply]
    split_ifs with hab
    · exact mul_inv_cancel₀ (hd a)
    · rfl
  rw [inv_eq_right_inv hmul, diagonal_apply]

lemma posDef_conj_inv_diagonal {A : Matrix n n ℝ} (hA : A.PosDef)
    {d : n → ℝ} (hd : ∀ i, 0 < d i) :
    ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).PosDef := by
  have hD : (diagonal d).PosDef := PosDef.diagonal hd
  have hU : IsUnit (diagonal d)⁻¹ := isUnit_nonsing_inv_iff.2 hD.isUnit
  have hne : ∀ k, d k ≠ 0 := fun k => (hd k).ne'
  have hstar : star (diagonal d)⁻¹ = (diagonal d)⁻¹ := by
    ext i j
    rw [star_eq_conjTranspose, conjTranspose_apply, star_trivial]
    rw [inv_diagonal_apply hne i j, inv_diagonal_apply hne j i]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  simpa [hstar] using (hU.posDef_star_right_conjugate_iff.2 hA)

lemma correlation_diag {A : Matrix n n ℝ} (hA : A.PosDef)
    (d : n → ℝ) (hd : ∀ i, d i = Real.sqrt (A i i)) (i : n) :
    ((diagonal d)⁻¹ * A * (diagonal d)⁻¹) i i = 1 := by
  have hdpos : ∀ k, 0 < d k := fun k => by
    rw [hd]
    exact Real.sqrt_pos.2 (hA.diag_pos (i := k))
  have hne : ∀ k, d k ≠ 0 := fun k => (hdpos k).ne'
  have hsq : d i ^ 2 = A i i := by
    rw [hd]
    exact Real.sq_sqrt (hA.diag_pos (i := i)).le
  have hii : (diagonal d)⁻¹ i i = (d i)⁻¹ := by
    rw [inv_diagonal_apply hne]; simp
  have hoff : ∀ k, k ≠ i → (diagonal d)⁻¹ k i = 0 := by
    intro k hk
    rw [inv_diagonal_apply hne, if_neg hk]
  have hoff' : ∀ j, j ≠ i → (diagonal d)⁻¹ i j = 0 := by
    intro j hj
    rw [inv_diagonal_apply hne, if_neg (Ne.symm hj)]
  simp only [Matrix.mul_apply]
  have hsumk :
      ∑ k, (∑ j, (diagonal d)⁻¹ i j * A j k) * (diagonal d)⁻¹ k i =
        (∑ j, (diagonal d)⁻¹ i j * A j i) * (diagonal d)⁻¹ i i := by
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    simp [hoff k hk]
  rw [hsumk, hii]
  have hsumj :
      ∑ j, (diagonal d)⁻¹ i j * A j i = (diagonal d)⁻¹ i i * A i i := by
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    simp [hoff' j hj]
  rw [hsumj, hii]
  field_simp [hne i, (hA.diag_pos (i := i)).ne']
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
  have hinv : ((diagonal d)⁻¹).det = ((diagonal d).det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv]
  have hC :
      ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).det =
        ((diagonal d)⁻¹.det) ^ 2 * A.det := by
    simp [det_mul, pow_two, mul_assoc, mul_comm]
  have hprod : ((diagonal d).det) ^ 2 = ∏ i, A i i := by
    rw [hdetD, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hd]
    exact Real.sq_sqrt (hA.diag_pos (i := i)).le
  have hne : (diagonal d).det ≠ 0 := hD.det_pos.ne'
  have hscale : ((diagonal d)⁻¹.det) ^ 2 * ((diagonal d).det) ^ 2 = 1 := by
    rw [hinv]
    field_simp [hne]
  have hAeq :
      A.det =
        ((diagonal d)⁻¹ * A * (diagonal d)⁻¹).det * ((diagonal d).det) ^ 2 := by
    rw [hC]
    have := congrArg (fun x => x * ((diagonal d).det) ^ 2 * A.det) hscale
    -- `(D⁻¹.det)² * A.det * (D.det)² = A.det`
    have : ((diagonal d)⁻¹.det) ^ 2 * A.det * ((diagonal d).det) ^ 2 = A.det := by
      calc
        ((diagonal d)⁻¹.det) ^ 2 * A.det * ((diagonal d).det) ^ 2 =
            (((diagonal d)⁻¹.det) ^ 2 * ((diagonal d).det) ^ 2) * A.det := by
          ring
        _ = 1 * A.det := by rw [hscale]
        _ = A.det := by simp
    linarith
  rw [hAeq, hprod]

lemma posDef_corr_eigen_prod_le_one {C : Matrix n n ℝ} (hC : C.PosDef)
    (hCii : ∀ i, C i i = 1) :
    (∏ i, hC.isHermitian.eigenvalues i) ≤ 1 := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · simp
  have hpos : ∀ i, 0 < hC.isHermitian.eigenvalues i := hC.eigenvalues_pos
  have htr : C.trace = Fintype.card n := by
    simp [trace, hCii]
  have hsum : ∑ i, hC.isHermitian.eigenvalues i = C.trace :=
    (hC.isHermitian.trace_eq_sum_eigenvalues).symm
  have hw' : 0 < ∑ _i : n, (1 : ℝ) := by
    simp [Finset.card_univ, Fintype.card_pos]
  have hAMGM :=
    Real.geom_mean_le_arith_mean Finset.univ (fun _ : n => (1 : ℝ))
      (fun i => hC.isHermitian.eigenvalues i)
      (fun _ _ => by norm_num) hw'
      (fun i _ => (hpos i).le)
  have hmean : (∑ i, (1 : ℝ) * hC.isHermitian.eigenvalues i) / ∑ _i : n, (1 : ℝ) = 1 := by
    simp [hsum, htr, Finset.card_univ]
  have hgeom :
      (∏ i, hC.isHermitian.eigenvalues i) ^ (Fintype.card n : ℝ)⁻¹ ≤ 1 := by
    convert hAMGM.trans_eq hmean using 2
    · simp
    · simp [Finset.card_univ]
  have hnpos : 0 < (Fintype.card n : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hnonneg : 0 ≤ ∏ i, hC.isHermitian.eigenvalues i :=
    Finset.prod_nonneg fun i _ => (hpos i).le
  have : (∏ i, hC.isHermitian.eigenvalues i) ^ (Fintype.card n : ℝ)⁻¹ ≤
      (1 : ℝ) ^ (Fintype.card n : ℝ)⁻¹ := by
    simpa [Real.one_rpow] using hgeom
  exact (Real.rpow_le_rpow_iff hnonneg (by norm_num) (inv_pos.2 hnpos)).1 this

/-- Hadamard's inequality for a real positive definite matrix. -/
theorem posDef_det_le_prod_diag (A : Matrix n n ℝ) (hA : A.PosDef) :
    A.det ≤ ∏ i, A i i := by
  let d : n → ℝ := fun i => Real.sqrt (A i i)
  have hd : ∀ i, d i = Real.sqrt (A i i) := fun _ => rfl
  let C : Matrix n n ℝ := (diagonal d)⁻¹ * A * (diagonal d)⁻¹
  have hC : C.PosDef := posDef_conj_inv_diagonal hA fun i =>
    Real.sqrt_pos.2 (hA.diag_pos (i := i))
  have hCii : ∀ i, C i i = 1 := fun i => correlation_diag hA d hd i
  have hdet := posDef_det_eq_corr_mul_prod hA d hd
  have hprodEig : C.det = ∏ i, (hC.isHermitian.eigenvalues i : ℝ) :=
    hC.isHermitian.det_eq_prod_eigenvalues
  have hle := posDef_corr_eigen_prod_le_one hC hCii
  have hdiagpos : 0 ≤ ∏ i, A i i :=
    Finset.prod_nonneg fun i _ => (hA.diag_pos (i := i)).le
  calc
    A.det = C.det * ∏ i, A i i := hdet
    _ = (∏ i, (hC.isHermitian.eigenvalues i : ℝ)) * ∏ i, A i i := by rw [hprodEig]
    _ ≤ 1 * ∏ i, A i i := mul_le_mul_of_nonneg_right hle hdiagpos
    _ = ∏ i, A i i := by simp

end EhlichWojtas
