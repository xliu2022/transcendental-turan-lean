module

public import TranscendentalTuran.Optimization.ElementaryBounds
public import TranscendentalTuran.Optimization.QuadraticDirections
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The missing-pair matrix interface for root completion

Formalization author and responsible maintainer: Xizhi Liu.

With data weights fixed, `M i j` is the data mass missing the root pair
`{i,j}`, and `Q i` is the one-root data-link value. The graph bridge must
prove this exact decomposition. Symmetry, nonnegative entries and row
sums at most `t` encode the matching property of the missing root pairs.
The root-transfer inequality is then derived from an actual maximum of
this polynomial; no derivative inequality is assumed.
-/

namespace TranscendentalTuran.Optimization.RootTransfer

open Set Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def basePolynomial (t : ℝ) (r : I → ℝ) : ℝ :=
  elementary r 3 + t * elementary r 2

noncomputable def completePolynomial (t : ℝ) (M : Matrix I I ℝ)
    (Q r : I → ℝ) : ℝ :=
  basePolynomial t r - QuadraticBudget.quad M.toBilin' r + QuadraticBudget.linear Q r

theorem completePolynomial_eq (t : ℝ) (M : Matrix I I ℝ) (Q r : I → ℝ) :
    completePolynomial t M Q r = elementary r 3 + t * elementary r 2 -
      M.toBilin' r r / 2 + ∑ i, r i * Q i := by
  simp only [completePolynomial, basePolynomial, QuadraticBudget.quad, QuadraticBudget.linear]
  simp only [mul_comm]

theorem six_mul_elementary_three (r : I → ℝ) :
    6 * elementary r 3 = (∑ i, r i) ^ 3 -
      3 * (∑ i, r i) * (∑ i, r i ^ 2) + 2 * ∑ i, r i ^ 3 := by
  have h2 := two_mul_elementary_two r
  have h3 := three_mul_elementary_three r
  linear_combination 2 * h3 + (∑ i, r i) * h2

theorem sum_transfer (f : ℝ → ℝ) (r : I → ℝ) (i j : I) (hij : i ≠ j) (h : ℝ) :
    (∑ k, f ((r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) k)) =
      (∑ k, f (r k)) + (f (r i + h) - f (r i)) + (f (r j - h) - f (r j)) := by
  have he (k : I) : f ((r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) k) = f (r k) +
      (if k = i then f (r i + h) - f (r i) else 0) +
      (if k = j then f (r j - h) - f (r j) else 0) := by
    by_cases hki : k = i
    · subst k
      simp [Pi.single_apply, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [Pi.single_apply, hij, Ne.symm hij, sub_eq_add_neg]
      · simp [Pi.single_apply, hki, hkj, Ne.symm hki, Ne.symm hkj]
  simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_transfer_preserves (r : I → ℝ) (i j : I) (hij : i ≠ j) (h : ℝ) :
    (∑ k, (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) k) = ∑ k, r k := by
  rw [sum_transfer (fun x => x) r i j hij h]
  ring

theorem basePolynomial_transfer (t : ℝ) (r : I → ℝ) (i j : I) (hij : i ≠ j) (h : ℝ) :
    basePolynomial t (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) =
      basePolynomial t r + h * (r j - r i) * ((∑ k, r k) + t - r i - r j) -
        h ^ 2 * ((∑ k, r k) + t - r i - r j) := by
  have h2 := two_mul_elementary_two r
  have h3 := six_mul_elementary_three r
  have h2' := two_mul_elementary_two (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ))
  have h3' := six_mul_elementary_three (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ))
  rw [sum_transfer_preserves r i j hij h,
    sum_transfer (fun x : ℝ => x ^ 2) r i j hij h] at h2'
  rw [sum_transfer_preserves r i j hij h,
    sum_transfer (fun x : ℝ => x ^ 2) r i j hij h,
    sum_transfer (fun x : ℝ => x ^ 3) r i j hij h] at h3'
  unfold basePolynomial
  linear_combination (1 / 6 : ℝ) * h3' - (1 / 6 : ℝ) * h3 + (t / 2) * h2' - (t / 2) * h2

theorem matrix_form_symmetric (M : Matrix I I ℝ) (hM : ∀ i j, M i j = M j i) :
    ∀ x y, M.toBilin' x y = M.toBilin' y x := by
  apply LinearMap.BilinForm.IsSymm.eq
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  ext i j
  exact hM j i

theorem linear_transfer_direction (Q : I → ℝ) (i j : I) :
    QuadraticBudget.linear Q ((Pi.single i 1 - Pi.single j 1) : I → ℝ) = Q i - Q j := by
  simp [QuadraticBudget.linear, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem completePolynomial_transfer (t : ℝ) (M : Matrix I I ℝ)
    (hM : ∀ i j, M i j = M j i) (Q r : I → ℝ)
    (i j : I) (hij : i ≠ j) (h : ℝ) :
    completePolynomial t M Q (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) =
      completePolynomial t M Q r + h *
        ((r j - r i) * ((∑ k, r k) + t - r i - r j) -
          M.toBilin' r ((Pi.single i 1 - Pi.single j 1) : I → ℝ) + (Q i - Q j)) +
      h ^ 2 * (-((∑ k, r k) + t - r i - r j) -
        QuadraticBudget.quad M.toBilin' ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) := by
  unfold completePolynomial
  rw [basePolynomial_transfer t r i j hij h,
    QuadraticBudget.quad_line M.toBilin' (matrix_form_symmetric M hM),
    QuadraticBudget.linear_line, linear_transfer_direction]
  ring

private theorem hasDerivAt_quadratic (a b c : ℝ) :
    HasDerivAt (fun h : ℝ => a + h * b + h ^ 2 * c) b 0 := by
  simpa only [mul_zero, add_zero, one_pow, div_one, mul_one, sub_zero] using
    hasDerivAt_quadratic_over_cube a b c 1 0 (by norm_num)

theorem completePolynomial_hasDerivAt_transfer (t : ℝ) (M : Matrix I I ℝ)
    (hM : ∀ i j, M i j = M j i) (Q r : I → ℝ) (i j : I) (hij : i ≠ j) :
    HasDerivAt (fun h : ℝ => completePolynomial t M Q
      (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)))
      ((r j - r i) * ((∑ k, r k) + t - r i - r j) -
        M.toBilin' r ((Pi.single i 1 - Pi.single j 1) : I → ℝ) + (Q i - Q j)) 0 := by
  have he := funext (completePolynomial_transfer t M hM Q r i j hij)
  rw [he]
  exact hasDerivAt_quadratic _ _ _

theorem matrix_form_single (M : Matrix I I ℝ) (hM : ∀ i j, M i j = M j i)
    (r : I → ℝ) (i : I) :
    M.toBilin' r (Pi.single i 1) = ∑ k, M i k * r k := by
  simp only [Matrix.toBilin'_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro k _
  rw [hM k i]
  ring

theorem transfer_nonneg {r : I → ℝ} (hr : ∀ k, 0 ≤ r k)
    (i j : I) (hij : i ≠ j) {h : ℝ} (hh : 0 ≤ h) (hhj : h ≤ r j) :
    ∀ k, 0 ≤ (r + h • ((Pi.single i 1 - Pi.single j 1) : I → ℝ)) k := by
  intro k
  by_cases hki : k = i
  · subst k
    simp [Pi.single_apply, hij, Ne.symm hij]
    exact add_nonneg (hr i) hh
  · by_cases hkj : k = j
    · subst k
      simp [Pi.single_apply, hij, Ne.symm hij]
      linarith
    · simpa [Pi.single_apply, hki, hkj, Ne.symm hki, Ne.symm hkj] using hr k

/-- The root-transfer loss bound follows from the missing-pair and
one-root-link coefficients and from genuine maximality of the complete
polynomial on the fixed-root-mass simplex. -/
theorem root_transfer_bound (t : ℝ) (M : Matrix I I ℝ) (Q r : I → ℝ)
    (ht : 0 ≤ t) (hr : ∀ k, 0 ≤ r k) (htotal : (∑ k, r k) + t = 1)
    (hM : ∀ i j, M i j = M j i) (hMpos : ∀ i j, 0 ≤ M i j)
    (hrows : ∀ i, (∑ k, M i k) ≤ t)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ t ^ 2 / 2)
    (hmax : ∀ r' : I → ℝ, (∀ k, 0 ≤ r' k) → (∑ k, r' k) = (∑ k, r k) →
      completePolynomial t M Q r' ≤ completePolynomial t M Q r)
    (i j : I) (hj : 0 < r j) (hheaviest : ∀ k, r k ≤ r j) :
    (r j - r i) * (1 - r i - r j) ≤ t * r j + t ^ 2 / 2 := by
  by_cases hij : i = j
  · subst j
    simp only [sub_self, zero_mul]
    exact add_nonneg (mul_nonneg ht (hr i)) (div_nonneg (sq_nonneg t) (by norm_num))
  have hd := completePolynomial_hasDerivAt_transfer t M hM Q r i j hij
  have hder := deriv_nonpos_of_right_max hd hj (by
    intro h hh
    simpa using hmax _ (transfer_nonneg hr i j hij hh.1 hh.2)
      (sum_transfer_preserves r i j hij h))
  rw [htotal, map_sub, matrix_form_single M hM, matrix_form_single M hM] at hder
  have hsender : 0 ≤ ∑ k, M j k * r k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hMpos j k) (hr k))
  have hreceiver : (∑ k, M i k * r k) ≤ t * r j := by
    calc
      _ ≤ ∑ k, M i k * r j :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hheaviest k) (hMpos i k))
      _ = (∑ k, M i k) * r j := by rw [Finset.sum_mul]
      _ ≤ t * r j := mul_le_mul_of_nonneg_right (hrows i) hj.le
  linarith [(hQ i).1, (hQ j).2]

end TranscendentalTuran.Optimization.RootTransfer
