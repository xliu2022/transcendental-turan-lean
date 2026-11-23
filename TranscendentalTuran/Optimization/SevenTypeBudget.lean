module

public import TranscendentalTuran.Optimization.QuadraticDirections
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The seven-type budget argument

Formalization author and responsible maintainer: Xizhi Liu.

This module proves the optimization argument from the actual quadratic
objective. Its coefficient hypotheses are numerical inequalities. The
directional derivative is computed in `QuadraticDirections`, rather than
being included as an assumption.
-/

namespace TranscendentalTuran.Optimization.QuadraticBudget

open Set Finset

noncomputable def coordinateVector (j : Fin 7) : Fin 7 → ℝ := Pi.single j 1

@[simp] theorem mass_coordinateVector (j : Fin 7) :
    mass (coordinateVector j) = 1 := by
  simp [mass, coordinateVector, Pi.single_apply]

@[simp] theorem linear_coordinateVector (L : Fin 7 → ℝ) (j : Fin 7) :
    linear L (coordinateVector j) = L j := by
  simp [linear, coordinateVector, Pi.single_apply]

theorem mass_sub (u v : Fin 7 → ℝ) : mass (u - v) = mass u - mass v := by
  simp [mass, Finset.sum_sub_distrib]

theorem linear_sub (L u v : Fin 7 → ℝ) :
    linear L (u - v) = linear L u - linear L v := by
  simp [linear, mul_sub, Finset.sum_sub_distrib]

def feasible (q : ℝ) : Set (Fin 7 → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ mass y ≤ 2 / q}

theorem mass_nonneg {y : Fin 7 → ℝ} (hy : ∀ i, 0 ≤ y i) : 0 ≤ mass y :=
  Finset.sum_nonneg (fun i _ => hy i)

theorem coordinate_le_mass {y : Fin 7 → ℝ} (hy : ∀ i, 0 ≤ y i) (j : Fin 7) :
    y j ≤ mass y :=
  Finset.single_le_sum (fun i _ => hy i) (Finset.mem_univ j)

theorem add_coordinate_feasible {q : ℝ} {y : Fin 7 → ℝ}
    (hy : y ∈ feasible q) (j : Fin 7) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 2 / q - mass y) :
    y + t • coordinateVector j ∈ feasible q := by
  constructor
  · intro k
    change 0 ≤ y k + t * coordinateVector j k
    have he : 0 ≤ coordinateVector j k := by
      simp only [coordinateVector, Pi.single_apply]
      split_ifs <;> norm_num
    exact add_nonneg (hy.1 k) (mul_nonneg ht he)
  · rw [mass_line, mass_coordinateVector]
    linarith

theorem transfer_coordinate_feasible {q : ℝ} {y : Fin 7 → ℝ}
    (hy : y ∈ feasible q) (i j : Fin 7) (hij : i ≠ j) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ y i) :
    y + t • (coordinateVector j - coordinateVector i) ∈ feasible q := by
  constructor
  · intro k
    change 0 ≤ y k + t * (coordinateVector j k - coordinateVector i k)
    by_cases hki : k = i
    · subst k
      simp [coordinateVector, Pi.single_apply, hij, Ne.symm hij]
      linarith
    · by_cases hkj : k = j
      · subst k
        simp [coordinateVector, Pi.single_apply, hij, Ne.symm hij]
        exact add_nonneg (hy.1 j) ht
      · simpa [coordinateVector, Pi.single_apply, hki, hkj, Ne.symm hki,
          Ne.symm hkj] using hy.1 k
  · rw [mass_line, mass_sub, mass_coordinateVector, mass_coordinateVector]
    simpa using hy.2

/-- Every type has a strictly positive budget at a maximizer. All
hypotheses concern the coefficients or the actual value of its quadratic
form; no first-order optimality statement is assumed. -/
theorem seven_type_budget
    (q a ω Z : ℝ) (L : Fin 7 → ℝ)
    (B : LinearMap.BilinForm ℝ (Fin 7 → ℝ))
    (hB : ∀ y d, B y d = B d y)
    (hq : 7 ≤ q) (hω : 0 ≤ ω) (hZ : 0 ≤ Z)
    (hL : ∀ j, 1 / 4 ≤ L j ∧ L j ≤ 1 / 2)
    (hLdiff : ∀ i j, L i - L j ≤ 2 / q ^ 2)
    (hgap : ∀ j, 2 / (3 * q) < L j - 3 * a)
    (hseparation : 2 / q ^ 2 + Z * (2 / q) < ω / (32 * q))
    {y : Fin 7 → ℝ} (hy : y ∈ feasible q)
    (hgradient : ∀ j,
      ω * (mass y - y j) ≤ B y (coordinateVector j) ∧
      B y (coordinateVector j) ≤ ω * (mass y - y j) + Z * mass y)
    (hquad : quad B y ≤ (mass y) ^ 2 / 2)
    (hmax : ∀ z ∈ feasible q, objective a L B z ≤ objective a L B y) :
    ∀ j, 1 / (32 * q) < y j := by
  have hqpos : 0 < q := by linarith
  have hx := mass_nonneg hy.1
  have hx1 : 0 < 1 + mass y := by linarith
  have h1 : 0 < 1 / (32 * q) := by positivity
  have h2 : 1 / (32 * q) < 1 / (16 * q) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  intro j
  by_contra hj
  push_neg at hj
  by_cases hlarge : ∃ i, 1 / (16 * q) ≤ y i
  · obtain ⟨i, hi⟩ := hlarge
    have hij : i ≠ j := by intro he; subst i; linarith
    have hi0 : 0 < y i := lt_of_lt_of_le (lt_trans h1 h2) hi
    have hderiv := directional_necessary a L B hB y
      (coordinateVector j - coordinateVector i) hx1 hi0
      (fun t ht => hmax _ (transfer_coordinate_feasible hy i j hij ht.1 ht.2))
    rw [linear_sub, linear_coordinateVector, linear_coordinateVector,
      map_sub, mass_sub, mass_coordinateVector, mass_coordinateVector] at hderiv
    simp only [sub_self, mul_zero, sub_zero] at hderiv
    have hrate : L j - L i + (B y (coordinateVector j) - B y (coordinateVector i)) ≤ 0 := by
      apply le_of_not_gt
      intro hh
      have hp := mul_pos hh hx1
      linarith
    have hdy : 1 / (32 * q) ≤ y i - y j := by
      have hh : 1 / (16 * q) = 2 * (1 / (32 * q)) := by field_simp; ring
      rw [hh] at hi
      linarith
    have hwdy := mul_le_mul_of_nonneg_left hdy hω
    have hZx := mul_le_mul_of_nonneg_left hy.2 hZ
    have hdj := (hgradient j).1
    have hdi := (hgradient i).2
    have hLij := hLdiff i j
    have hw : ω * (1 / (32 * q)) = ω / (32 * q) := by ring
    rw [hw] at hwdy
    nlinarith
  · push_neg at hlarge
    have hxsmall : mass y < 7 / (16 * q) := by
      calc
        mass y < ∑ _i : Fin 7, (1 / (16 * q)) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun i _ => hlarge i)
        _ = 7 / (16 * q) := by simp; ring
    have hxcap : mass y < 2 / q := by
      have hh : 7 / (16 * q) < 2 / q := by
        apply (div_lt_div_iff₀ (by positivity) hqpos).2
        nlinarith
      exact hxsmall.trans hh
    have hδ : 0 < 2 / q - mass y := sub_pos.mpr hxcap
    have hderiv := directional_necessary a L B hB y (coordinateVector j) hx1 hδ
      (fun t ht => hmax _ (add_coordinate_feasible hy j ht.1 ht.2))
    rw [linear_coordinateVector, mass_coordinateVector, mul_one] at hderiv
    have hDj : 0 ≤ B y (coordinateVector j) :=
      le_trans (mul_nonneg hω (sub_nonneg.mpr (coordinate_le_mass hy.1 j)))
        (hgradient j).1
    have hlin : linear L y ≤ mass y / 2 := by
      calc
        linear L y ≤ ∑ i : Fin 7, (1 / 2 : ℝ) * y i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hL i).2 (hy.1 i))
        _ = mass y / 2 := by rw [← Finset.mul_sum]; unfold mass; ring
    have hLlow := (hL j).1
    have hgapj := hgap j
    have hprod : 0 ≤ (1 + mass y) * B y (coordinateVector j) :=
      mul_nonneg hx1.le hDj
    have hLx := mul_le_mul_of_nonneg_right hLlow hx
    have hx16 : mass y < 1 / 16 := by
      have hh : 7 / (16 * q) ≤ 1 / 16 := by
        apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
        nlinarith
      exact hxsmall.trans_le hh
    have hxx : (mass y) ^ 2 ≤ mass y / 16 := by nlinarith
    have hfinal : 0 < 2 / (3 * q) - 5 * mass y / 4 - 3 * (mass y) ^ 2 / 2 := by
      have hstrict : (43 : ℝ) / 32 * (7 / (16 * q)) < 2 / (3 * q) := by
        have he : (43 : ℝ) / 32 * (7 / (16 * q)) = 301 / (512 * q) := by ring
        rw [he]
        apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      nlinarith
    nlinarith

end TranscendentalTuran.Optimization.QuadraticBudget
