module

public import TranscendentalTuran.Algebra.Legacy.RationalPolynomialFamilies

@[expose] public section

/-! # Division with parameter-dependent degree drops

Polynomial long division is unrolled to a fixed input degree bound. Every
exceptional vanishing leading coefficient is resolved using a finite degree
partition; the resulting remainder coefficients stay piecewise rational.
-/

namespace TuranUniversality.Algebraicity

open Polynomial Set

universe u

noncomputable def boundedRemainder : ℕ → ℝ[X] → ℝ[X] → ℝ[X]
  | 0, p, _ => p
  | n + 1, p, q => by
      classical
      exact if q = 0 ∨ n < q.natDegree then p else
        boundedRemainder n
          (p - C (p.coeff n / q.leadingCoeff) * q * X ^ (n - q.natDegree)) q

theorem remainder_step_degree (p q : ℝ[X]) (n : ℕ) (hq : q ≠ 0)
    (hqn : q.natDegree ≤ n) (hp : p.degree < (n + 1 : ℕ)) :
    (p - C (p.coeff n / q.leadingCoeff) * q * X ^ (n - q.natDegree)).degree < (n : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro k hnk
  rw [coeff_sub, coeff_mul_X_pow', if_pos ((Nat.sub_le _ _).trans hnk), coeff_C_mul]
  by_cases hkn : k = n
  · subst k
    rw [Nat.sub_sub_self hqn, ← leadingCoeff, div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hq), sub_self]
  · have hnk' : n + 1 ≤ k := by omega
    have hpk := (degree_lt_iff_coeff_zero p (n + 1)).mp hp k hnk'
    have hqk : q.coeff (k - (n - q.natDegree)) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hpk, hqk, mul_zero, sub_zero]

theorem remainder_step_mod (p q : ℝ[X]) (n : ℕ) :
    (p - C (p.coeff n / q.leadingCoeff) * q * X ^ (n - q.natDegree)) % q = p % q := by
  apply Polynomial.mod_eq_of_dvd_sub
  refine ⟨-(C (p.coeff n / q.leadingCoeff) * X ^ (n - q.natDegree)), ?_⟩
  ring

theorem boundedRemainder_eq_mod (n : ℕ) (p q : ℝ[X]) (hp : p.degree < n) :
    boundedRemainder n p q = p % q := by
  classical
  induction n generalizing p with
  | zero =>
      have hp0 : p = 0 := by
        ext k
        exact (degree_lt_iff_coeff_zero p 0).mp hp k (Nat.zero_le _)
      simp [hp0, boundedRemainder]
  | succ n ih =>
      rw [boundedRemainder]
      split_ifs with h
      · by_cases hq : q = 0
        · simp [hq]
        · have hnq : n < q.natDegree := h.resolve_left hq
          apply ((mod_eq_self_iff hq).mpr ?_).symm
          apply hp.trans_le
          rw [degree_eq_natDegree hq]
          exact_mod_cast hnq
      · have hq : q ≠ 0 := (not_or.mp h).1
        have hnq : q.natDegree ≤ n := Nat.le_of_not_gt (not_or.mp h).2
        rw [ih _ (remainder_step_degree p q n hq hnq hp), remainder_step_mod]

namespace RationalPolynomialFamily

variable {σ : Type u} {p q : (σ → ℝ) → ℝ[X]}

theorem natDegree_choice (hp : RationalPolynomialFamily p)
    (f : ℕ → (σ → ℝ) → ℝ[X]) (hf : ∀ n, RationalPolynomialFamily (f n)) :
    RationalPolynomialFamily (fun x => f (p x).natDegree x) := by
  classical
  obtain ⟨N, hN⟩ := hp.bounded
  let i : (σ → ℝ) → Fin (N + 1) := fun x => ⟨(p x).natDegree, by have := hN x; omega⟩
  refine (finite_choice i ?_ (fun j => f j) (fun j => hf j)).congr (fun _ => rfl)
  intro j
  simpa only [i, Fin.ext_iff] using hp.natDegree_eq j.val

theorem boundedRemainder (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q)
    (n : ℕ) : RationalPolynomialFamily (fun x => Algebraicity.boundedRemainder n (p x) (q x)) := by
  classical
  induction n generalizing p with
  | zero => exact hp
  | succ n ih =>
      have hx : RationalPolynomialFamily (fun x => (Polynomial.X : ℝ[X]) ^ (n - (q x).natDegree)) :=
        hq.natDegree_choice _ (fun k => X.pow (n - k))
      have hstep := hp.sub (((C ((hp.coefficient n).div hq.leadingCoeff)).mul hq).mul hx)
      have hrec := ih hstep
      have hs : QSemialgebraic {x | q x = 0 ∨ n < (q x).natDegree} := by
        apply (hq.zeroSet.union (hq.natDegree_le n).compl).congr
        ext x
        simp
      apply (piecewise {x | q x = 0 ∨ n < (q x).natDegree} hs hp hrec).congr
      intro x
      rfl

theorem mod (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    RationalPolynomialFamily (fun x => p x % q x) := by
  obtain ⟨N, hN⟩ := hp.bounded
  refine (hp.boundedRemainder hq (N + 1)).congr ?_
  intro x
  apply boundedRemainder_eq_mod
  exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (hN x))

end RationalPolynomialFamily

end TuranUniversality.Algebraicity
