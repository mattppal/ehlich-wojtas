import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Integer Gram-matrix facts for `{±1}`-matrices, including Wojtas’s 4-cycle
congruence that splits the index set when `n ≡ 2 (mod 4)`.
-/

namespace EhlichWojtas

open Matrix Int

variable {ι : Type*} [Fintype ι]

/-- Row Gram matrix over `ℤ`. -/
def gram (M : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  M * M.transpose

lemma gram_apply (M : Matrix ι ι ℤ) (i j : ι) :
    gram M i j = ∑ k, M i k * M j k := by
  simp [gram, Matrix.mul_apply, Matrix.transpose_apply]

lemma gram_symm (M : Matrix ι ι ℤ) (i j : ι) : gram M i j = gram M j i := by
  simp [gram_apply, mul_comm]

lemma sq_plus_minus_one {a : ℤ} (h : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases h with h | h <;> simp [h]

lemma gram_diag (M : Matrix ι ι ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) (i : ι) :
    gram M i i = Fintype.card ι := by
  simp only [gram_apply]
  simp [sq_plus_minus_one (hM i _), Finset.card_univ]

lemma gram_det [DecidableEq ι] (M : Matrix ι ι ℤ) : (gram M).det = M.det ^ 2 := by
  rw [gram, det_mul, det_transpose, ← pow_two]

lemma plus_minus_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

lemma plus_minus_add {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a + b = 2 ∨ a + b = 0 ∨ a + b = -2 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

lemma plus_minus_add_mul_four {a b c : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    (4 : ℤ) ∣ (a + b) * (a + c) := by
  have hab := plus_minus_add ha hb
  have hac := plus_minus_add ha hc
  rcases hab with hab | hab | hab <;> rcases hac with hac | hac | hac <;> simp [hab, hac]

lemma gram_quad_sum (M : Matrix ι ι ℤ) (_hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : ι) :
    gram M r r + gram M r s + gram M s t + gram M t r =
      ∑ k, (M r k + M s k) * (M r k + M t k) := by
  simp only [gram_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma gram_quad_sum_mod4 (M : Matrix ι ι ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : ι) :
    gram M r r + gram M r s + gram M s t + gram M t r ≡ 0 [ZMOD 4] := by
  rw [gram_quad_sum M hM r s t]
  refine Int.modEq_zero_iff_dvd.2 ?_
  exact Finset.dvd_sum fun k _ => plus_minus_add_mul_four (hM r k) (hM s k) (hM t k)

lemma card_mod4_of_n {n : ℕ} (hn : n % 4 = 2) :
    (Fintype.card (Fin n) : ℤ) ≡ 2 [ZMOD 4] := by
  simp [Fintype.card_fin, Int.ModEq]
  omega

lemma gram_diag_mod4 {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) (i : Fin n) :
    gram M i i ≡ 2 [ZMOD 4] := by
  rw [gram_diag M hM i]
  exact card_mod4_of_n hn

omit [Fintype ι] in
lemma gram_term_mod2 (M : Matrix ι ι ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (i j k : ι) : M i k * M j k ≡ 1 [ZMOD 2] := by
  rcases plus_minus_mul (hM i k) (hM j k) with h | h
  · simp [h]
  · rw [h]
    decide

lemma gram_mod2 (M : Matrix ι ι ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1) (i j : ι) :
    gram M i j ≡ (Fintype.card ι : ℤ) [ZMOD 2] := by
  rw [gram_apply]
  have hsum : ∑ k : ι, M i k * M j k ≡ ∑ _k : ι, (1 : ℤ) [ZMOD 2] :=
    Int.ModEq.sum fun k _ => gram_term_mod2 M hM i j k
  simpa [Finset.card_univ] using hsum

lemma gram_even_of_even_card (M : Matrix ι ι ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (hι : Even (Fintype.card ι)) (i j : ι) : Even (gram M i j) := by
  rw [even_iff_two_dvd, ← Int.modEq_zero_iff_dvd]
  have h := gram_mod2 M hM i j
  have h0 : (Fintype.card ι : ℤ) ≡ 0 [ZMOD 2] := by
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.1 hι
    simp [hk, Int.ModEq]
  exact h.trans h0

lemma n_even_of_mod4 {n : ℕ} (hn : n % 4 = 2) : Even n :=
  even_iff_exists_two_mul.2 ⟨n / 2, by omega⟩

lemma gram_even {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (i j : Fin n) : Even (gram M i j) := by
  have : Even (Fintype.card (Fin n)) := by
    simpa [Fintype.card_fin] using n_even_of_mod4 hn
  exact gram_even_of_even_card M hM this i j

lemma even_emod4 {a : ℤ} (h : Even a) : a % 4 = 0 ∨ a % 4 = 2 := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.1 h
  subst hk
  omega

lemma abs_even_ne_zero {a : ℤ} (h : Even a) (hne : a ≠ 0) : (2 : ℤ) ≤ |a| := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.1 h
  have hk0 : k ≠ 0 := by
    intro hk0
    exact hne (by simp [hk, hk0])
  have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
  have : (2 : ℤ) ≤ 2 * |k| := by linarith
  calc
    (2 : ℤ) ≤ 2 * |k| := this
    _ = |2| * |k| := by norm_num
    _ = |2 * k| := (abs_mul _ _).symm
    _ = |a| := by rw [hk]

/-- Nonzero even Gram entries have magnitude at least 2. -/
lemma abs_gram_ge_two_of_ne {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    {i j : Fin n} (hne : gram M i j ≠ 0) :
    (2 : ℤ) ≤ |gram M i j| :=
  abs_even_ne_zero (gram_even hn M hM i j) hne

lemma abs_gram_ge_two_of_mod2 {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    {i j : Fin n} (h : gram M i j ≡ 2 [ZMOD 4]) :
    (2 : ℤ) ≤ |gram M i j| := by
  apply abs_even_ne_zero (gram_even hn M hM i j)
  intro hz
  have : (0 : ℤ) ≡ 2 [ZMOD 4] := hz ▸ h
  exact (by decide : ¬ (0 : ℤ) ≡ 2 [ZMOD 4]) this

lemma gram_triple_mod4 {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : Fin n) :
    gram M r s + gram M s t + gram M t r ≡ 2 [ZMOD 4] := by
  have hquad := gram_quad_sum_mod4 M hM r s t
  have hdiag := gram_diag_mod4 hn M hM r
  have : gram M r s + gram M s t + gram M t r =
      (gram M r r + gram M r s + gram M s t + gram M t r) - gram M r r := by
    ring
  rw [this]
  exact (hquad.sub hdiag).trans (by decide)

/-- Inner product with a fixed row is `2 (mod 4)`. -/
def class2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r i : Fin n) : Prop :=
  gram M r i ≡ 2 [ZMOD 4]

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r i : Fin n) :
    Decidable (class2 M r i) :=
  inferInstanceAs (Decidable (gram M r i ≡ 2 [ZMOD 4]))

lemma class2_self {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r : Fin n) : class2 M r r :=
  gram_diag_mod4 hn M hM r

lemma even_not_class2_modEq0 {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    {r i : Fin n} (h : ¬ class2 M r i) :
    gram M r i ≡ 0 [ZMOD 4] := by
  have he := even_emod4 (gram_even hn M hM r i)
  unfold class2 Int.ModEq at h
  rcases he with h0 | h2
  · exact Int.ModEq.symm (by simp [Int.ModEq, h0])
  · exact (h h2).elim

/-- Two indices in the `2 (mod 4)` class have inner product `2 (mod 4)`. -/
lemma gram_mem_class2 {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : Fin n) (hs : class2 M r s) (ht : class2 M r t) :
    gram M s t ≡ 2 [ZMOD 4] := by
  have h3 := gram_triple_mod4 hn M hM s t r
  unfold class2 Int.ModEq at hs ht h3
  have htr : gram M t r % 4 = 2 := by simpa [gram_symm M t r] using ht
  unfold Int.ModEq
  omega

/-- A class-2 index and a complementary index have inner product `0 (mod 4)`. -/
lemma gram_cross_class {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : Fin n) (hs : class2 M r s) (ht : ¬ class2 M r t) :
    gram M s t ≡ 0 [ZMOD 4] := by
  have h3 := gram_triple_mod4 hn M hM s t r
  have hrt := even_not_class2_modEq0 hn M hM ht
  unfold class2 Int.ModEq at hs h3 hrt
  have htr : gram M t r % 4 = 0 := by simpa [gram_symm M t r] using hrt
  unfold Int.ModEq
  omega

/-- Two complementary-class indices have inner product `2 (mod 4)`. -/
lemma gram_mem_compl {n : ℕ} (hn : n % 4 = 2)
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i j, M i j = 1 ∨ M i j = -1)
    (r s t : Fin n) (hs : ¬ class2 M r s) (ht : ¬ class2 M r t) :
    gram M s t ≡ 2 [ZMOD 4] := by
  have h3 := gram_triple_mod4 hn M hM s t r
  have hrs := even_not_class2_modEq0 hn M hM hs
  have hrt := even_not_class2_modEq0 hn M hM ht
  unfold Int.ModEq at hrs hrt h3 ⊢
  have htr : gram M t r % 4 = 0 := by simpa [gram_symm M t r] using hrt
  omega

end EhlichWojtas
