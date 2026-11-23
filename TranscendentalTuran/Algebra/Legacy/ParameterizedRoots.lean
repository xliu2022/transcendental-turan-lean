module

public import TranscendentalTuran.Algebra.Legacy.ParameterizedTarski

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set Polynomial Finset TauCeti.SignDetermination
open scoped Matrix

universe u v

namespace RationalPolynomialFamily

variable {σ : Type u}

theorem prod {I : Type*} (F : Finset I) (p : I → (σ → ℝ) → ℝ[X])
    (hp : ∀ i ∈ F, RationalPolynomialFamily (p i)) :
    RationalPolynomialFamily (fun x => ∏ i ∈ F, p i x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (one (σ := σ))
  | @insert i F hi ih =>
      simpa only [Finset.prod_insert hi] using
        (hp i (Finset.mem_insert_self _ _)).mul
          (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

/-- The parameter set on which a prescribed sign condition occurs at a
distinct real root is rational semialgebraic, including zero-polynomial
parameters (whose finite root list is empty). -/
theorem root_sign_condition {J : Type v} [Fintype J] [DecidableEq J]
    {p : (σ → ℝ) → ℝ[X]} (hp : RationalPolynomialFamily p)
    (Q : J → (σ → ℝ) → ℝ[X]) (hQ : ∀ j, RationalPolynomialFamily (Q j))
    (s : J → SignType) :
    QSemialgebraic {x | ∃ z ∈ (p x).roots.toFinset,
      ∀ j, SignType.sign ((Q j x).eval z) = s j} := by
  classical
  let val : (σ → ℝ) → ℝ := fun x =>
    ∑ e : J → Fin 3, (fullInverse J s e : ℝ) *
      (Polynomial.tarskiQuery (p x) (∏ j, Q j x ^ (e j).val) : ℝ)
  have hv : PiecewiseRational val :=
    PiecewiseRational.sum univ _ (fun e _ =>
      (PiecewiseRational.const (fullInverse J s e)).mul
        (hp.tarskiQuery (prod univ _ (fun j _ => (hQ j).pow (e j).val))))
  have heq (x : σ → ℝ) : val x =
      (signCount (p x).roots.toFinset (fun j => Q j x) s : ℝ) := by
    have h := congrFun (Polynomial.fullInverse_mulVec_tarskiQuery (p x) (fun j => Q j x)) s
    simp only [Matrix.mulVec, dotProduct] at h
    dsimp only [val]
    exact_mod_cast h
  apply hv.positiveSet.congr
  ext x
  simp only [Set.mem_setOf_eq, heq, Nat.cast_pos, Finset.signCount_pos]

end RationalPolynomialFamily

end TuranUniversality.Algebraicity
