module

public import TranscendentalTuran.Algebra.Legacy.RationalRemainder
public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.RingTheory.Polynomial.Subresultant.CauchyIndex
public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots
public import TranscendentalTuran.Algebra.Legacy.Upstream.TauCeti.FieldTheory.IsRealClosed.Real
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # Parameterized Sturm–Tarski queries over ℚ

Fixed-bound signed principal subresultants are determinants of coefficient
matrices. Finite degree partitions and the proved remainder algorithm make
their sign statistics piecewise rational functions of the parameters.
-/

namespace TuranUniversality.Algebraicity

open Set Polynomial Finset

universe u v

namespace PiecewiseRational

variable {σ : Type u}

theorem int_const (z : ℤ) : PiecewiseRational (fun _ : σ → ℝ => (z : ℝ)) := by
  simpa using const (σ := σ) (z : ℚ)

theorem det {I : Type v} [Fintype I] [DecidableEq I]
    (M : (σ → ℝ) → Matrix I I ℝ)
    (hM : ∀ i j, PiecewiseRational (fun x => M x i j)) :
    PiecewiseRational (fun x => (M x).det) := by
  refine (sum univ (fun e x => ((Equiv.Perm.sign e : ℤ) : ℝ) * ∏ i, M x (e i) i)
    (fun e _ => (int_const _).mul (prod univ _ (fun i _ => hM _ _)))).congr ?_
  intro x
  exact (Matrix.det_apply' (M x)).symm

theorem permanencesMinusVariations {n : ℕ} (f : Fin n → (σ → ℝ) → ℝ)
    (hf : ∀ i, PiecewiseRational (f i)) :
    PiecewiseRational (fun x => ((List.ofFn (fun i => f i x)).permanencesMinusVariations : ℝ)) := by
  classical
  let s : (σ → ℝ) → (Fin n → SignType) := fun x i => SignType.sign (f i x)
  have hs : ∀ a, QSemialgebraic {x | s x = a} := by
    intro a
    apply (QSemialgebraic.iInter (fun i => {x | SignType.sign (f i x) = a i})
      (fun i => (hf i).sign_fiber (a i))).congr
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, s, funext_iff]
  refine (finite_choice s hs
    (fun a (_ : σ → ℝ) => ((List.ofFn a).permanencesMinusVariations : ℝ))
    (fun a => int_const _)).congr ?_
  intro x
  congr 1
  have h : List.ofFn (s x) = (List.ofFn (fun i => f i x)).map SignType.sign := by
    simp only [List.map_ofFn, Function.comp_def, s]
  rw [h, List.permanencesMinusVariations_map_sign]

theorem permanencesMinusVariations_list {I : Type*} (l : List I)
    (f : I → (σ → ℝ) → ℝ) (hf : ∀ i, PiecewiseRational (f i)) :
    PiecewiseRational (fun x => ((l.map (fun i => f i x)).permanencesMinusVariations : ℝ)) := by
  have h := permanencesMinusVariations (fun i : Fin l.length => f l[i]) (fun i => hf l[i])
  apply h.congr
  intro x
  exact congrArg (fun xs : List ℝ => (xs.permanencesMinusVariations : ℝ))
    (List.ofFn_getElem_eq_map l (fun i => f i x))

end PiecewiseRational

namespace RationalPolynomialFamily

variable {σ : Type u} {p q : (σ → ℝ) → ℝ[X]}

theorem natDegree_scalar_choice (hp : RationalPolynomialFamily p)
    (f : ℕ → (σ → ℝ) → ℝ) (hf : ∀ n, PiecewiseRational (f n)) :
    PiecewiseRational (fun x => f (p x).natDegree x) := by
  classical
  obtain ⟨N, hN⟩ := hp.bounded
  let i : (σ → ℝ) → Fin (N + 1) := fun x => ⟨(p x).natDegree, by have := hN x; omega⟩
  refine (PiecewiseRational.finite_choice i ?_ (fun j => f j) (fun j => hf j)).congr (fun _ => rfl)
  intro j
  simpa only [i, Fin.ext_iff] using hp.natDegree_eq j.val

theorem psc (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q)
    (m n j : ℕ) : PiecewiseRational (fun x => Polynomial.psc (p x) (q x) m n j) := by
  classical
  apply PiecewiseRational.det
  intro i k
  induction k using Fin.addCases with
  | left k =>
      by_cases h : (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + n
      · simpa [subresultantMatrix_castAdd, h] using hq.coefficient (i.val + j - k.val)
      · simpa only [subresultantMatrix_castAdd, h, ite_false, Rat.cast_zero] using
          PiecewiseRational.const (σ := σ) 0
  | right k =>
      by_cases h : (k : ℕ) ≤ i.val + j ∧ i.val + j ≤ k.val + m
      · simpa [subresultantMatrix_natAdd, h] using hp.coefficient (i.val + j - k.val)
      · simpa only [subresultantMatrix_natAdd, h, ite_false, Rat.cast_zero] using
          PiecewiseRational.const (σ := σ) 0

theorem signedPsc (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q)
    (m n j : ℕ) : PiecewiseRational (fun x => Polynomial.signedPsc (p x) (q x) m n j) := by
  classical
  by_cases hj : j ≤ min m n
  · have h := (PiecewiseRational.const (σ := σ) ((-1 : ℚ) ^ (m - j).choose 2)).mul (hp.psc hq m n j)
    apply h.congr
    intro x
    simp [Polynomial.signedPsc, hj]
  · by_cases hm : j = m
    · apply (hp.coefficient m).congr
      intro x
      rw [Polynomial.signedPsc, if_neg hj, if_pos hm]
    · by_cases hn : j = n
      · apply (hq.coefficient n).congr
        intro x
        rw [Polynomial.signedPsc, if_neg hj, if_neg hm, if_pos hn]
      · simpa only [Polynomial.signedPsc, hj, hm, hn, ite_false, Rat.cast_zero] using
          PiecewiseRational.const (σ := σ) 0

/-- The actual integer sum of signs over distinct real roots has a finite
piecewise rational description in all coefficient parameters. -/
theorem tarskiQuery (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    PiecewiseRational (fun x => (Polynomial.tarskiQuery (p x) (q x) : ℝ)) := by
  let u : (σ → ℝ) → ℝ[X] := fun x => ((p x).derivative * q x) % p x
  have hu : RationalPolynomialFamily u := (hp.derivative.mul hq).mod hp
  have h := hp.natDegree_scalar_choice (fun m x =>
    (((List.range (m + 1)).reverse.map
      (Polynomial.signedPsc (p x) (u x) m (u x).natDegree)).permanencesMinusVariations : ℝ))
    (fun m => hu.natDegree_scalar_choice (fun n x =>
      (((List.range (m + 1)).reverse.map
        (Polynomial.signedPsc (p x) (u x) m n)).permanencesMinusVariations : ℝ))
      (fun n => PiecewiseRational.permanencesMinusVariations_list _ _
        (fun j => hp.signedPsc hu m n j)))
  apply h.congr
  intro x
  rw [Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc]

end RationalPolynomialFamily

end TuranUniversality.Algebraicity
