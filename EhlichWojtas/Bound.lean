import EhlichWojtas.Block
import EhlichWojtas.Fischer
import EhlichWojtas.Gram
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
Assembly of the Ehlich–Wojtas bound from the two-class Gram partition,
Fischer’s inequality, and Wojtas’s off-diagonal magnitude bound.
-/

namespace EhlichWojtas

open Matrix Int

variable {n : ℕ}

/-- Realification of the integer Gram matrix. -/
def gramR (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  (gram M).map Int.cast

lemma gramR_apply (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    gramR M i j = (gram M i j : ℝ) :=
  rfl

lemma gramR_det (M : Matrix (Fin n) (Fin n) ℤ) :
    (gramR M).det = ((gram M).det : ℝ) := by
  simpa [gramR, RingHom.mapMatrix] using (Int.castRingHom ℝ).map_det (gram M)

lemma gramR_det_sq (M : Matrix (Fin n) (Fin n) ℤ) :
    (gramR M).det = (M.det : ℝ) ^ 2 := by
  simp [gramR_det, gram_det, sq]

lemma gramR_symm (M : Matrix (Fin n) (Fin n) ℤ) : (gramR M)ᵀ = gramR M := by
  ext i j
  simp [gramR, gram_symm M]

lemma gramR_posDef {M : Matrix (Fin n) (Fin n) ℤ} (hdet : M.det ≠ 0) :
    (gramR M).PosDef := by
  have hmul : gramR M = (M.map Int.cast) * (M.map Int.cast)ᵀ := by
    ext i j
    simp [gramR, gram, Matrix.mul_apply, transpose_apply]
  have hstar : (M.map Int.cast)ᵀ = (M.map Int.cast)ᴴ := by
    ext i j
    simp [conjTranspose, transpose]
  have hU : IsUnit (M.map (Int.cast : ℤ → ℝ)) := by
    refine (isUnit_iff_isUnit_det _).2 ?_
    have hmap : ((M.map (Int.cast : ℤ → ℝ)).det) = (M.det : ℝ) := by
      simpa [RingHom.mapMatrix] using (Int.castRingHom ℝ).map_det M
    simpa [hmap] using (Int.cast_ne_zero.2 hdet)
  have hinj : Function.Injective (M.map (Int.cast : ℤ → ℝ)).vecMul :=
    vecMul_injective_iff_isUnit.2 hU
  simpa [hmul, hstar] using
    PosDef.mul_conjTranspose_self (M.map (Int.cast : ℤ → ℝ)) hinj

lemma abs_gramR_ge_two {hn : n % 4 = 2}
    {M : Matrix (Fin n) (Fin n) ℤ} {hM : ∀ i j, M i j = 1 ∨ M i j = -1}
    {i j : Fin n} (h : gram M i j ≡ 2 [ZMOD 4]) :
    (2 : ℝ) ≤ |gramR M i j| := by
  have := abs_gram_ge_two_of_mod2 hn M hM h
  have : (2 : ℝ) ≤ (|gram M i j| : ℝ) := by exact_mod_cast this
  simpa [gramR, Int.cast_abs] using this

lemma single_class_nat_le {n : ℕ} (hn : 2 ≤ n) :
    (3 * n - 2) * (n - 2) ^ (n - 1) ≤ (2 * n - 2) ^ 2 * (n - 2) ^ (n - 2) := by
  have hpow : (n - 2) ^ (n - 1) = (n - 2) * (n - 2) ^ (n - 2) := by
    have : n - 1 = n - 2 + 1 := by omega
    rw [this, pow_succ]
  rw [hpow, mul_assoc, mul_left_comm (n - 2), ← mul_assoc]
  gcongr
  have hL : (3 * n - 2) * (n - 2) = 3 * n * n - 8 * n + 4 := by
    zify [hn]
    ring
  have hR : (2 * n - 2) ^ 2 = 4 * n * n - 8 * n + 4 := by
    zify [hn]
    ring
  rw [hL, hR]
  omega

lemma two_class_factor_le {n a b : ℕ} (hab : a + b = n) (hn : 2 ≤ n) :
    (n + 2 * a - 2) * (n + 2 * b - 2) ≤ (2 * n - 2) ^ 2 := by
  have hb : b = n - a := by omega
  subst hb
  have ha : a ≤ n := by omega
  zify [hn, ha]
  set x : ℤ := (2 * a : ℤ) - n
  have hx : (n + 2 * a - 2 : ℤ) = (2 * n - 2 : ℤ) + x := by
    simp [x]
    ring
  have hy : (n + 2 * (n - a) - 2 : ℤ) = (2 * n - 2 : ℤ) - x := by
    simp [x]
    ring
  rw [hx, hy]
  nlinarith [sq_nonneg x]

lemma ew_bound_sq {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) :
    ((2 * n - 2) * (n - 2) ^ (n / 2 - 1)) ^ 2 =
      (2 * n - 2) ^ 2 * (n - 2) ^ (n - 2) := by
  rw [mul_pow, ← pow_mul]
  congr 1
  have hdiv : n / 2 * 2 = n := Nat.div_mul_cancel (even_iff_two_dvd.1 hn)
  have : 2 * (n / 2 - 1) = n - 2 := by omega
  rw [this]

lemma fromBlocks_toBlock_eq (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Prop)
    [DecidablePred p] :
    fromBlocks (toBlock M p p) (toBlock M p fun i => ¬p i)
        (toBlock M (fun i => ¬p i) p) (toBlock M (fun i => ¬p i) fun i => ¬p i) =
      M.submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) := by
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, toBlock, Equiv.sumCompl]

/-- The Ehlich–Wojtas bound, proved form. -/
theorem ehlich_wojtas_bound_main {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    M.det.natAbs ≤ (2 * n - 2) * (n - 2) ^ (n / 2 - 1) := by
  have hn2 : 2 ≤ n := by omega
  have hneven : Even n := n_even_of_mod4 hn
  set bound : ℕ := (2 * n - 2) * (n - 2) ^ (n / 2 - 1)
  by_cases hsing : M.det = 0
  · simp [hsing]
  have hPD : (gramR M).PosDef := gramR_posDef hsing
  have hdiag : ∀ i, gramR M i i = n := by
    intro i
    simp [gramR, gram_diag M hM, Fintype.card_fin]
  have hb : (0 : ℝ) < 2 := by norm_num
  have hsq : ((M.det.natAbs : ℝ) ^ 2) = (gramR M).det := by
    have : ((M.det.natAbs : ℤ) : ℝ) ^ 2 = ((M.det ^ 2 : ℤ) : ℝ) := by
      norm_cast
      exact (Int.natAbs_mul_self' M.det).symm.trans (by ring)
    simpa [gramR_det_sq, sq, Int.natAbs_mul_self'] using this.symm
  have hclose : (gramR M).det ≤ (bound : ℝ) ^ 2 → M.det.natAbs ≤ bound := by
    intro hle
    have : (M.det.natAbs : ℝ) ^ 2 ≤ (bound : ℝ) ^ 2 := by simpa [hsq] using hle
    have hx := (sq_le_sq.1 this)
    have : (M.det.natAbs : ℝ) ≤ (bound : ℝ) := by
      simpa [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg bound)] using hx
    exact_mod_cast this
  let p : Fin n → Prop := class2 M 0
  have h0 : p 0 := class2_self hn M hM 0
  have hAcard : 1 ≤ Fintype.card { i : Fin n // p i } :=
    Nat.succ_le_of_lt (Fintype.card_pos_iff.2 ⟨⟨0, h0⟩⟩)
  refine hclose ?_
  by_cases hBempty : IsEmpty { i : Fin n // ¬p i }
  · have hoff : ∀ i j : Fin n, i ≠ j → (2 : ℝ) ≤ |gramR M i j| := by
      intro i j hij
      have hi : p i := by
        by_contra h
        exact (hBempty.elim ⟨i, h⟩)
      have hj : p j := by
        by_contra h
        exact (hBempty.elim ⟨j, h⟩)
      exact abs_gramR_ge_two (hn := hn) (hM := hM) (gram_mem_class2 hn M hM 0 i j hi hj)
    have hcard : 1 ≤ Fintype.card (Fin n) := by
      simpa [Fintype.card_fin] using hn2
    have hw := wojtas_bound (gramR M) hPD hdiag hb hoff hcard
    have hform :
        (n : ℝ) + Fintype.card (Fin n) * 2 - 2 = ((3 * n - 2 : ℕ) : ℝ) := by
      simp [Fintype.card_fin]
      have : (3 * n - 2 : ℕ) = 3 * n - 2 := rfl
      zify [hn2]
      ring
    have hnm : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.cast_sub hn2).symm
    have : (gramR M).det ≤
        ((3 * n - 2 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ^ (n - 1) := by
      simp [Fintype.card_fin] at hw
      simpa [hform, hnm] using hw
    have hnat := single_class_nat_le hn2
    have hcast : ((3 * n - 2 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ^ (n - 1) ≤
        ((2 * n - 2 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by
      exact_mod_cast hnat
    have hbound : (bound : ℝ) ^ 2 =
        ((2 * n - 2 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) (ew_bound_sq hneven hn2)
      simpa [bound, Nat.cast_pow, Nat.cast_mul] using this
    nlinarith
  · have : Nonempty { i : Fin n // ¬p i } := not_isEmpty_iff.mp hBempty
    have hDcard : 1 ≤ Fintype.card { i : Fin n // ¬p i } :=
      Nat.succ_le_of_lt Fintype.card_pos
    let A := toBlock (gramR M) p p
    let B := toBlock (gramR M) p fun i => ¬p i
    let D := toBlock (gramR M) (fun i => ¬p i) fun i => ¬p i
    have hC : toBlock (gramR M) (fun i => ¬p i) p = Bᵀ :=
      toBlock_symm (gramR_symm M) p
    have hmat :
        fromBlocks A B Bᵀ D =
          (gramR M).submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) := by
      simpa [A, B, D, hC] using fromBlocks_toBlock_eq (gramR M) p
    have hGblk : (fromBlocks A B Bᵀ D).PosDef := by
      simpa [hmat] using
        hPD.submatrix (e := Equiv.sumCompl p) (Equiv.sumCompl p).injective
    have hf := fischer (A := A) B (D := D) hGblk
    have hAPD : A.PosDef := posDef_block₁₁ hGblk
    have hDPD : D.PosDef := posDef_block₂₂ hGblk
    have hAdiag : ∀ i, A i i = (n : ℝ) := fun i => hdiag _
    have hDdiag : ∀ i, D i i = (n : ℝ) := fun i => hdiag _
    have hAoff : ∀ i j, i ≠ j → (2 : ℝ) ≤ |A i j| := by
      intro i j hij
      have : i.1 ≠ j.1 := mt (congrArg Subtype.val) hij
      exact abs_gramR_ge_two (hn := hn) (hM := hM)
        (gram_mem_class2 hn M hM 0 i.1 j.1 i.2 j.2)
    have hDoff : ∀ i j, i ≠ j → (2 : ℝ) ≤ |D i j| := by
      intro i j hij
      have : i.1 ≠ j.1 := mt (congrArg Subtype.val) hij
      exact abs_gramR_ge_two (hn := hn) (hM := hM)
        (gram_mem_compl hn M hM 0 i.1 j.1 i.2 j.2)
    have hAb := wojtas_bound A hAPD hAdiag hb hAoff hAcard
    have hDb := wojtas_bound D hDPD hDdiag hb hDoff hDcard
    set a := Fintype.card { i : Fin n // p i }
    set d := Fintype.card { i : Fin n // ¬p i }
    have had : a + d = n := by
      have hsum := Fintype.card_sum (α := { i : Fin n // p i })
        (β := { i : Fin n // ¬p i })
      have hcongr := Fintype.card_congr (Equiv.sumCompl p)
      simpa [a, d, Fintype.card_fin, hsum] using hcongr
    have hnm : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.cast_sub hn2).symm
    have hAdet : A.det ≤ ((n + 2 * a - 2 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ^ (a - 1) := by
      have : (n : ℝ) + a * 2 - 2 = ((n + 2 * a - 2 : ℕ) : ℝ) := by
        have ha : 1 ≤ a := hAcard
        zify [hn2, ha]
        ring
      simpa [a, hnm, this, mul_comm (a : ℝ)] using hAb
    have hDdet : D.det ≤ ((n + 2 * d - 2 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ^ (d - 1) := by
      have : (n : ℝ) + d * 2 - 2 = ((n + 2 * d - 2 : ℕ) : ℝ) := by
        have hd : 1 ≤ d := hDcard
        zify [hn2, hd]
        ring
      simpa [d, hnm, this, mul_comm (d : ℝ)] using hDb
    have hGdet : (gramR M).det = (fromBlocks A B Bᵀ D).det := by
      have := det_toBlock (gramR M) p
      simpa [A, B, D, hC] using this
    have hprod : (fromBlocks A B Bᵀ D).det ≤ A.det * D.det := hf
    have hAnn : 0 ≤ A.det := hAPD.posSemidef.det_nonneg
    have hDnn : 0 ≤ D.det := hDPD.posSemidef.det_nonneg
    have hmul : A.det * D.det ≤
        ((n + 2 * a - 2 : ℕ) : ℝ) * ((n + 2 * d - 2 : ℕ) : ℝ) *
          ((n - 2 : ℕ) : ℝ) ^ (a - 1 + (d - 1)) := by
      have := mul_le_mul hAdet hDdet hDnn (by
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      simpa [mul_mul_mul_comm, pow_add] using this
    have hpow : a - 1 + (d - 1) = n - 2 := by omega
    have hfac := two_class_factor_le (n := n) (a := a) (b := d) had hn2
    have hfacR :
        ((n + 2 * a - 2 : ℕ) : ℝ) * ((n + 2 * d - 2 : ℕ) : ℝ) ≤
          ((2 * n - 2 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hfac
    have hbound : (bound : ℝ) ^ 2 =
        ((2 * n - 2 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) (ew_bound_sq hneven hn2)
      simpa [bound, Nat.cast_pow, Nat.cast_mul] using this
    have : (gramR M).det ≤
        ((2 * n - 2 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by
      calc
        (gramR M).det = (fromBlocks A B Bᵀ D).det := hGdet
        _ ≤ A.det * D.det := hprod
        _ ≤ ((n + 2 * a - 2 : ℕ) : ℝ) * ((n + 2 * d - 2 : ℕ) : ℝ) *
              ((n - 2 : ℕ) : ℝ) ^ (a - 1 + (d - 1)) := hmul
        _ = ((n + 2 * a - 2 : ℕ) : ℝ) * ((n + 2 * d - 2 : ℕ) : ℝ) *
              ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by simp [hpow]
        _ ≤ ((2 * n - 2 : ℕ) : ℝ) ^ 2 * ((n - 2 : ℕ) : ℝ) ^ (n - 2) := by
          have hnn : 0 ≤ ((n - 2 : ℕ) : ℝ) ^ (n - 2) :=
            pow_nonneg (Nat.cast_nonneg _) _
          nlinarith [hfacR]
    simpa [hbound] using this

end EhlichWojtas
