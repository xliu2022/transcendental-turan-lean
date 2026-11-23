module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Low-degree elementary symmetric identities

Formalization author and responsible maintainer: Xizhi Liu.

The identities are specialized from Newton's identities at degrees two
and three. The variable type stays abstract throughout; in particular no
enumeration of the paper's enormous finite root set takes place.
-/

namespace TranscendentalTuran.Optimization

open Finset MvPolynomial
open scoped BigOperators

variable {I : Type*} [Fintype I]

noncomputable def elementary (r : I → ℝ) (k : ℕ) : ℝ :=
  aeval r (MvPolynomial.esymm I ℝ k)

theorem elementary_eq_sum (r : I → ℝ) (k : ℕ) :
    elementary r k = ∑ e ∈ (univ : Finset I).powersetCard k, ∏ i ∈ e, r i := by
  simp [elementary, MvPolynomial.esymm]

@[simp] theorem elementary_zero (r : I → ℝ) : elementary r 0 = 1 := by
  simp [elementary]

@[simp] theorem elementary_one (r : I → ℝ) : elementary r 1 = ∑ i, r i := by
  simp [elementary, MvPolynomial.esymm_one]

theorem two_mul_elementary_two (r : I → ℝ) :
    2 * elementary r 2 = (∑ i, r i) ^ 2 - ∑ i, (r i) ^ 2 := by
  classical
  have ha : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  have h := congrArg (aeval r) (MvPolynomial.mul_esymm_eq_sum I ℝ 2)
  rw [ha] at h
  norm_num [MvPolynomial.esymm_zero, MvPolynomial.esymm_one,
    MvPolynomial.psum, Finset.filter_insert, Finset.filter_singleton] at h
  simp only [elementary, MvPolynomial.aeval_eq_eval]
  nlinarith

theorem three_mul_elementary_three (r : I → ℝ) :
    3 * elementary r 3 = elementary r 2 * (∑ i, r i) -
      (∑ i, r i) * (∑ i, (r i) ^ 2) + ∑ i, (r i) ^ 3 := by
  classical
  have ha : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
  have h := congrArg (aeval r) (MvPolynomial.mul_esymm_eq_sum I ℝ 3)
  rw [ha] at h
  norm_num [MvPolynomial.esymm_zero, MvPolynomial.esymm_one,
    MvPolynomial.psum, Finset.filter_insert, Finset.filter_singleton] at h
  simp only [elementary, MvPolynomial.aeval_eq_eval]
  nlinarith

theorem elementary_two_sub_three {r : I → ℝ} (hr : ∑ i, r i = 1) :
    elementary r 2 - 3 * elementary r 3 =
      ∑ i, (r i) ^ 2 - ∑ i, (r i) ^ 3 := by
  have h := three_mul_elementary_three r
  rw [hr] at h
  linarith

end TranscendentalTuran.Optimization
