import EhlichWojtas.Hadamard
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Positivity

/-!
Wojtas’s determinant bound for a positive definite matrix with a uniform
off-diagonal magnitude lower bound (Browne–Egan–Hegarty–Ó Catháin, Lemma 7
and Theorem 8).
-/

namespace EhlichWojtas

open Matrix

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- Clearing matrix for the last row and column of a bordered Gram block. -/
def borderClear (v : Matrix l Unit ℝ) (b : ℝ) : Matrix (l ⊕ Unit) (l ⊕ Unit) ℝ :=
  fromBlocks (1 : Matrix l l ℝ) (-(b⁻¹ • v)) 0 (1 : Matrix Unit Unit ℝ)

lemma det_borderClear (v : Matrix l Unit ℝ) (b : ℝ) :
    (borderClear v b).det = 1 := by
  simp [borderClear, det_fromBlocks_zero₂₁, det_one]

lemma borderClear_mul {A : Matrix l l ℝ} {v : Matrix l Unit ℝ} {b : ℝ}
    (hb : b ≠ 0) :
    borderClear v b * fromBlocks A v vᵀ (fun _ _ => b) =
      fromBlocks (A - b⁻¹ • (v * vᵀ)) 0 vᵀ (fun _ _ => b) := by
  have h1 : (b⁻¹ • v) * vᵀ = b⁻¹ • (v * vᵀ) := smul_mul_assoc _ _ _
  have h2 : (b⁻¹ • v) * (fun _ _ => b : Matrix Unit Unit ℝ) = v := by
    have : v * (fun _ _ => b : Matrix Unit Unit ℝ) = b • v := by
      ext i j
      simp [Matrix.mul_apply]
    simp [this, smul_smul, inv_mul_cancel₀ hb]
  simp [borderClear, fromBlocks_multiply, h1, h2, sub_eq_add_neg]

lemma mul_borderClear_transpose {S : Matrix l l ℝ} {v : Matrix l Unit ℝ} {b : ℝ}
    (hb : b ≠ 0) :
    fromBlocks S 0 vᵀ (fun _ _ => b) * (borderClear v b)ᵀ =
      fromBlocks S 0 0 (fun _ _ => b) := by
  have hE : (borderClear v b)ᵀ =
      fromBlocks (1 : Matrix l l ℝ) 0 (-(b⁻¹ • vᵀ)) (1 : Matrix Unit Unit ℝ) := by
    simp [borderClear, fromBlocks_transpose, transpose_neg, transpose_smul]
  have h2 : (fun _ _ => b : Matrix Unit Unit ℝ) * (b⁻¹ • vᵀ) = vᵀ := by
    have : (fun _ _ => b : Matrix Unit Unit ℝ) * vᵀ = b • vᵀ := by
      ext i j
      simp [Matrix.mul_apply]
    simp [this, smul_smul, mul_inv_cancel₀ hb]
  rw [hE, fromBlocks_multiply]
  simp [h2, sub_eq_add_neg]

lemma border_congr {A : Matrix l l ℝ} {v : Matrix l Unit ℝ} {b : ℝ}
    (hb : b ≠ 0) :
    borderClear v b * fromBlocks A v vᵀ (fun _ _ => b) * (borderClear v b)ᵀ =
      fromBlocks (A - b⁻¹ • (v * vᵀ)) 0 0 (fun _ _ => b) := by
  rw [borderClear_mul hb, mul_borderClear_transpose hb]

/-- Wojtas’s bordering lemma: a PD matrix with last diagonal `b` and last
row/column of magnitude at least `b` has determinant at most `b (m-b)^k`. -/
theorem wojtas_border (A : Matrix l l ℝ) (v : Matrix l Unit ℝ) (m b : ℝ)
    (hM : (fromBlocks A v vᵀ (fun _ _ => b)).PosDef)
    (hdiag : ∀ i, A i i = m) (hb : 0 < b) (hv : ∀ i, b ≤ |v i ()|) :
    (fromBlocks A v vᵀ (fun _ _ => b)).det ≤ b * (m - b) ^ Fintype.card l := by
  set M := fromBlocks A v vᵀ (fun _ _ => b)
  set E := borderClear v b
  set S := A - b⁻¹ • (v * vᵀ)
  have hb0 : b ≠ 0 := hb.ne'
  have hcong : E * M * Eᵀ = fromBlocks S 0 0 (fun _ _ => b) :=
    border_congr (A := A) (v := v) hb0
  have hEdet : E.det = 1 := det_borderClear v b
  have hU : IsUnit E := isUnit_iff_isUnit_det.2 (by simp [hEdet])
  have hstar : star E = Eᵀ := by
    simp [E, star_eq_conjTranspose]
  have hEM : (E * M * Eᵀ).PosDef := by
    simpa [hstar] using (hU.posDef_star_right_conjugate_iff (x := M)).2 hM
  have hS : S.PosDef := by
    have : S = (E * M * Eᵀ).submatrix Sum.inl Sum.inl := by
      ext i j
      simp [hcong, fromBlocks_apply₁₁]
    simpa [this] using hEM.submatrix (e := Sum.inl) Sum.inl_injective
  have hSii : ∀ i, S i i = m - (v i ()) ^ 2 / b := by
    intro i
    have hvv : (v * vᵀ) i i = (v i ()) ^ 2 := by
      simp [Matrix.mul_apply, pow_two]
    simp [S, hdiag, hvv, smul_apply, div_eq_inv_mul, mul_comm]
  have hdiag_le : ∀ i, S i i ≤ m - b := by
    intro i
    have hmag : b ≤ |v i ()| := hv i
    have hsq : b ≤ (v i ()) ^ 2 / b := by
      have : b ^ 2 ≤ (v i ()) ^ 2 := by
        simpa [sq_abs, abs_of_pos hb] using (sq_le_sq.2 hmag)
      exact (le_div_iff₀ hb).2 (by simpa [pow_two] using this)
    linarith [hSii i]
  have hprod : S.det ≤ ∏ i, S i i := posDef_det_le_prod_diag S hS
  have hprod2 : (∏ i, S i i) ≤ (m - b) ^ Fintype.card l := by
    have hnn : ∀ i, 0 ≤ S i i := fun i => (hS.diag_pos (i := i)).le
    have : (∏ i, S i i) ≤ ∏ _i : l, (m - b) :=
      Finset.prod_le_prod (fun i _ => hnn i) fun i _ => hdiag_le i
    simpa [Finset.card_univ] using this
  have hdetM : M.det = b * S.det := by
    have hdetE : (E * M * Eᵀ).det = M.det := by
      simp [det_mul, hEdet]
    have : (fromBlocks S 0 0 (fun _ _ => b)).det = S.det * b := by
      simp [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_unique]
    simpa [hcong, this, mul_comm] using hdetE.symm
  have hSdet : 0 ≤ S.det := hS.posSemidef.det_nonneg
  have hbnn : 0 ≤ b := hb.le
  calc
    M.det = b * S.det := hdetM
    _ ≤ b * ∏ i, S i i := by nlinarith [hprod]
    _ ≤ b * (m - b) ^ Fintype.card l := by nlinarith [hprod2]

lemma det_split_last (A : Matrix l l ℝ) (B : Matrix l Unit ℝ) (C : Matrix Unit l ℝ)
    (m b : ℝ) :
    (fromBlocks A B C (fun _ _ => m)).det =
      (fromBlocks A B C (fun _ _ => b)).det +
        (fromBlocks A B 0 (fun _ _ => (m - b))).det := by
  let G := fromBlocks A B C (fun _ _ => m)
  let last : l ⊕ Unit := Sum.inr ()
  have hrow :
      G last =
        (fun j => Sum.elim (fun i => C () i) (fun _ => b) j) +
          fun j => Sum.elim (fun _ => (0 : ℝ)) (fun _ => m - b) j := by
    funext j
    cases j with
    | inl i =>
      simp [G, last, fromBlocks]
    | inr u =>
      simp [G, last, fromBlocks]
  have hG : G = G.updateRow last (G last) := (updateRow_eq_self _ _).symm
  have h1 : G.updateRow last (Sum.elim (fun i => C () i) (fun _ => b)) =
      fromBlocks A B C (fun _ _ => b) := by
    ext i j
    cases i with
    | inl i =>
      cases j <;> simp [G, last, fromBlocks, updateRow]
    | inr u =>
      cases j <;> simp [G, last, fromBlocks, updateRow]
  have h2 : G.updateRow last (Sum.elim (fun _ => (0 : ℝ)) (fun _ => m - b)) =
      fromBlocks A B 0 (fun _ _ => m - b) := by
    ext i j
    cases i with
    | inl i =>
      cases j <;> simp [G, last, fromBlocks, updateRow]
    | inr u =>
      cases j <;> simp [G, last, fromBlocks, updateRow]
  calc
    G.det = (G.updateRow last (G last)).det := by rw [← hG]
    _ = (G.updateRow last
          ((fun j => Sum.elim (fun i => C () i) (fun _ => b) j) +
            fun j => Sum.elim (fun _ => (0 : ℝ)) (fun _ => m - b) j)).det := by
      rw [hrow]
    _ = (G.updateRow last (Sum.elim (fun i => C () i) (fun _ => b))).det +
          (G.updateRow last (Sum.elim (fun _ => (0 : ℝ)) (fun _ => m - b))).det := by
      simpa [Pi.add_def] using
        det_updateRow_add G last
          (Sum.elim (fun i => C () i) (fun _ => b))
          (Sum.elim (fun _ => (0 : ℝ)) (fun _ => m - b))
    _ = (fromBlocks A B C (fun _ _ => b)).det +
          (fromBlocks A B 0 (fun _ _ => m - b)).det := by
      rw [h1, h2]

lemma det_fromBlocks_last_zero (A : Matrix l l ℝ) (B : Matrix l Unit ℝ) (c : ℝ) :
    (fromBlocks A B 0 (fun _ _ => c)).det = A.det * c := by
  simp [det_fromBlocks_zero₂₁, det_unique]

lemma toBlock_symm {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℝ} (hG : Gᵀ = G) (p : n → Prop) [DecidablePred p] :
    toBlock G (fun i => ¬p i) p = (toBlock G p (fun j => ¬p j))ᵀ := by
  ext i j
  simpa [toBlock, transpose_apply] using congrFun (congrFun hG j.1) i.1

lemma card_subtype_ne {n : Type*} [Fintype n] [DecidableEq n] (a : n) :
    Fintype.card { x : n // x ≠ a } = Fintype.card n - 1 := by
  have h1 : Fintype.card { x : n // x = a } = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨a, rfl⟩, fun y => Subtype.ext y.property⟩
  simpa [h1] using (Fintype.card_subtype_compl (fun x : n => x = a))

lemma posDef_of_pos_det_border {A : Matrix l l ℝ} {B : Matrix l Unit ℝ} {b : ℝ}
    (hA : A.PosDef) (hdet : 0 < (fromBlocks A B Bᵀ (fun _ _ => b)).det) :
    (fromBlocks A B Bᵀ (fun _ _ => b)).PosDef := by
  haveI : Invertible A := hA.isUnit.invertible
  let S : Matrix Unit Unit ℝ := (fun _ _ => b) - Bᵀ * A⁻¹ * B
  have hdet' : (fromBlocks A B Bᵀ (fun _ _ => b)).det = A.det * S.det := by
    simpa [S, invOf_eq_nonsing_inv] using det_fromBlocks₁₁ A B Bᵀ (fun _ _ => b)
  have hSpos : 0 < S.det := by
    have : 0 < A.det := hA.det_pos
    nlinarith
  have hSii : 0 < S () () := by simpa [S, det_unique] using hSpos
  have hSdiag : S = diagonal fun _ => S () () := by
    ext i j
    simp [S, diagonal]
  have hS : S.PosSemidef := by
    rw [hSdiag]
    exact (PosDef.diagonal fun _ => hSii).posSemidef
  have hPSD : (fromBlocks A B Bᵀ (fun _ _ => b)).PosSemidef :=
    (PosDef.fromBlocks₁₁ (A := A) (B := B)
      (D := (fun _ _ => b : Matrix Unit Unit ℝ)) hA).2 (by simpa [S] using hS)
  exact hPSD.posDef_iff_det_ne_zero.2 hdet.ne'

lemma diag_gt_off {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℝ} (hG : G.PosDef) {m b : ℝ}
    (hdiag : ∀ i, G i i = m) (hb : 0 < b)
    (hoff : ∀ i j, i ≠ j → b ≤ |G i j|)
    {i j : n} (hij : i ≠ j) : b < m := by
  have h2 : (G.submatrix ![i, j] ![i, j]).PosDef :=
    hG.submatrix (e := ![i, j]) <| by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
  have hdet : 0 < (G.submatrix ![i, j] ![i, j]).det := h2.det_pos
  have : (G.submatrix ![i, j] ![i, j]).det = m * m - G i j * G j i := by
    simp [det_fin_two, hdiag]
  have hsym : G j i = G i j := by
    simpa using congrFun (congrFun hG.isHermitian.eq j) i
  have : 0 < m ^ 2 - (G i j) ^ 2 := by
    simpa [this, hsym, pow_two, mul_comm] using hdet
  have : |G i j| < |m| := by
    have := sq_lt_sq.1 (by linarith)
    -- `sq_lt_sq` is `|x| < |y|`
    exact this
  have hmpos : 0 < m := by simpa [hdiag i] using hG.diag_pos (i := i)
  have : |G i j| < m := by
    simpa [abs_of_pos hmpos] using this
  exact lt_of_le_of_lt (hoff i j hij) this

/-- Wojtas’s bound (Browne et al., Theorem 8). -/
theorem wojtas_bound {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : G.PosDef) {m b : ℝ}
    (hdiag : ∀ i, G i i = m) (hb : 0 < b)
    (hoff : ∀ i j, i ≠ j → b ≤ |G i j|)
    (hcard : 1 ≤ Fintype.card n) :
    G.det ≤ (m + Fintype.card n * b - b) * (m - b) ^ (Fintype.card n - 1) := by
  generalize hk : Fintype.card n = k at hcard ⊢
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst hk
    cases k with
    | zero =>
      exact (Nat.not_succ_le_zero 0 (by simpa using hcard)).elim
    | succ k =>
      cases k with
      | zero =>
        -- 1×1: `det = m` and the right-hand side is `m`.
        have h1 : Fintype.card n = 1 := by simp
        have : Nonempty (Unique n) := Fintype.card_eq_one_iff_nonempty_unique.mp h1
        inhabit n
        haveI : Unique n := ‹Nonempty (Unique n)›.some
        simp [det_unique, hdiag (default : n)]
      | succ k' =>
        -- `card n ≥ 2`.
        have hge : 2 ≤ Fintype.card n := by simp
        have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
        inhabit n
        set last : n := default
        let p : n → Prop := fun i => i ≠ last
        let A := toBlock G p p
        let B := toBlock G p (fun i => ¬p i)
        let C := toBlock G (fun i => ¬p i) p
        let D := toBlock G (fun i => ¬p i) (fun i => ¬p i)
        have hdetG : G.det = (fromBlocks A B C D).det := det_toBlock G p
        have hGsym : Gᵀ = G := hG.isHermitian.eq
        have hC : C = Bᵀ := toBlock_symm hGsym p
        haveI : Unique { i : n // ¬p i } := by
          refine ⟨⟨⟨last, by simp [p]⟩⟩, ?_⟩
          intro i
          ext
          have : ¬i.1 ≠ last := i.2
          simpa [p] using this
        have hD : D = fun _ _ => m := by
          ext i j
          have hi : i.1 = last := by
            have : ¬i.1 ≠ last := i.2
            simpa [p] using this
          have hj : j.1 = last := by
            have : ¬j.1 ≠ last := j.2
            simpa [p] using this
          simp [D, toBlock, hdiag, hi, hj]
        -- Identify the complement type with `Unit`.
        let e : { i : n // ¬p i } ≃ Unit := Equiv.equivPUnit.{_, 0} _
        -- Work after reindexing the last block to `Unit`.
        let Bu : Matrix { i : n // p i } Unit ℝ :=
          B.submatrix id e.symm
        let Cu : Matrix Unit { i : n // p i } ℝ :=
          C.submatrix e.symm id
        have hre :
            (fromBlocks A B C D).det =
              (fromBlocks A Bu Cu (fun _ _ => m)).det := by
          -- Reindex the last summand by `e`.
          have :=
            Matrix.det_submatrix_equiv_self
              (e := Equiv.sumCongr (Equiv.refl _) e) (fromBlocks A B C D)
          -- The reindexed matrix is `fromBlocks A Bu Cu (const m)`.
          have hmat :
              (fromBlocks A B C D).submatrix
                  (Equiv.sumCongr (Equiv.refl _) e).symm
                  (Equiv.sumCongr (Equiv.refl _) e).symm =
                fromBlocks A Bu Cu (fun _ _ => m) := by
            ext i j
            cases i with
            | inl i =>
              cases j with
              | inl j =>
                simp [A, Bu, Cu, fromBlocks, Equiv.sumCongr]
              | inr u =>
                simp [A, Bu, Cu, B, D, fromBlocks, Equiv.sumCongr, hD]
            | inr u =>
              cases j with
              | inl j =>
                simp [A, Bu, Cu, C, fromBlocks, Equiv.sumCongr]
              | inr v =>
                simp [A, Bu, Cu, D, fromBlocks, Equiv.sumCongr, hD]
          simpa [hmat] using this.symm
        have hCu : Cu = Buᵀ := by
          ext i j
          simp [Bu, Cu, hC, submatrix, transpose_apply]
        have hsplit := det_split_last A Bu Cu m b
        have hzero := det_fromBlocks_last_zero A Bu (m - b)
        have hA : A.PosDef :=
          hG.submatrix (e := (fun i : { x // p x } => i.1)) Subtype.val_injective
        have hAdiag : ∀ i, A i i = m := fun i => hdiag _
        have hAoff : ∀ i j, i ≠ j → b ≤ |A i j| := by
          intro i j hij
          have : i.1 ≠ j.1 := mt Subtype.ext hij
          simpa [A, toBlock] using hoff i.1 j.1 this
        have hcardA : Fintype.card { x : n // p x } = Fintype.card n - 1 :=
          card_subtype_ne last
        have hcardA' : 1 ≤ Fintype.card { x : n // p x } := by
          have : Fintype.card n = k' + 2 := by simp
          omega
        have hAih :
            A.det ≤ (m + (Fintype.card { x : n // p x }) * b - b) *
              (m - b) ^ (Fintype.card { x : n // p x } - 1) :=
          ih (Fintype.card { x : n // p x }) (by omega) rfl A hA hAdiag hb hAoff hcardA'
        have hmb : b < m := by
          obtain ⟨i, j, hij⟩ :=
            Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card n)
          exact diag_gt_off hG hdiag hb hoff hij
        have hmb0 : 0 ≤ m - b := le_of_lt (sub_pos.2 hmb)
        have hBu : ∀ i, b ≤ |Bu i ()| := by
          intro i
          have : i.1 ≠ last := i.2
          simpa [Bu, B, toBlock, submatrix] using hoff i.1 last this
        -- Split and bound the second summand.
        have hsecond :
            (fromBlocks A Bu Cu (fun _ _ => b)).det ≤
              b * (m - b) ^ Fintype.card { x : n // p x } := by
          by_cases hpos : 0 < (fromBlocks A Bu Cu (fun _ _ => b)).det
          · have hPD : (fromBlocks A Bu Buᵀ (fun _ _ => b)).PosDef := by
              simpa [hCu] using posDef_of_pos_det_border (A := A) (B := Bu) hA (by simpa [hCu] using hpos)
            have := wojtas_border A Bu m b (by simpa [hCu] using hPD) hAdiag hb hBu
            simpa [hCu] using this
          · have : (fromBlocks A Bu Cu (fun _ _ => b)).det ≤ 0 := le_of_not_gt hpos
            have : 0 ≤ (m - b) ^ Fintype.card { x : n // p x } :=
              pow_nonneg hmb0 _
            nlinarith [hb.le]
        have hGle :
            G.det ≤ (m - b) * A.det + b * (m - b) ^ Fintype.card { x : n // p x } := by
          calc
            G.det = (fromBlocks A Bu Cu (fun _ _ => m)).det := by
              rw [hdetG, hre]
            _ = (fromBlocks A Bu Cu (fun _ _ => b)).det +
                  (fromBlocks A Bu 0 (fun _ _ => m - b)).det := hsplit
            _ = (fromBlocks A Bu Cu (fun _ _ => b)).det + A.det * (m - b) := by
              rw [hzero]
            _ ≤ b * (m - b) ^ Fintype.card { x : n // p x } + A.det * (m - b) := by
              linarith [hsecond]
            _ = (m - b) * A.det + b * (m - b) ^ Fintype.card { x : n // p x } := by
              ring
        have hpow : (m - b) * (m - b) ^ (Fintype.card { x : n // p x } - 1) =
            (m - b) ^ Fintype.card { x : n // p x } := by
          have : Fintype.card { x : n // p x } =
              Fintype.card { x : n // p x } - 1 + 1 := by omega
          nth_rw 2 [this]
          rw [pow_succ, mul_comm]
        have hAbound :
            (m - b) * A.det ≤
              (m - b) * (m + (Fintype.card { x : n // p x }) * b - b) *
                (m - b) ^ (Fintype.card { x : n // p x } - 1) := by
          have : 0 ≤ A.det := hA.posSemidef.det_nonneg
          nlinarith [hAih, hmb0]
        have : G.det ≤
            (m + Fintype.card n * b - b) * (m - b) ^ (Fintype.card n - 1) := by
          have hcard' : Fintype.card { x : n // p x } = Fintype.card n - 1 := hcardA
          calc
            G.det ≤ (m - b) * A.det +
                b * (m - b) ^ Fintype.card { x : n // p x } := hGle
            _ ≤ (m - b) * (m + (Fintype.card { x : n // p x }) * b - b) *
                  (m - b) ^ (Fintype.card { x : n // p x } - 1) +
                b * (m - b) ^ Fintype.card { x : n // p x } := by
              linarith [hAbound]
            _ = (m + (Fintype.card { x : n // p x }) * b - b + b) *
                  (m - b) ^ Fintype.card { x : n // p x } := by
              rw [← hpow]
              ring
            _ = (m + Fintype.card n * b - b) *
                  (m - b) ^ (Fintype.card n - 1) := by
              simp [hcard']
              ring
        exact this

end EhlichWojtas
