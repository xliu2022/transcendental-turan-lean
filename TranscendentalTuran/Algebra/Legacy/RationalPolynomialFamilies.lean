module

public import TranscendentalTuran.Algebra.Legacy.PiecewiseRational
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Basic.Sign.Basic

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set Polynomial

universe u v

/-- A uniformly degree-bounded polynomial family whose scalar coefficient
functions are piecewise rational over the parameter field ℚ. -/
structure RationalPolynomialFamily {σ : Type u} (p : (σ → ℝ) → ℝ[X]) : Prop where
  bounded : ∃ N : ℕ, ∀ x, (p x).natDegree ≤ N
  coefficient : ∀ i, PiecewiseRational (fun x => (p x).coeff i)

namespace RationalPolynomialFamily

variable {σ : Type u} {p q : (σ → ℝ) → ℝ[X]}

theorem congr (hp : RationalPolynomialFamily p) (hpq : ∀ x, p x = q x) :
    RationalPolynomialFamily q := (funext hpq) ▸ hp

theorem const (p : ℚ[X]) : RationalPolynomialFamily (fun _ : σ → ℝ => p.map (algebraMap ℚ ℝ)) := by
  refine ⟨⟨p.natDegree, fun _ => natDegree_map_le⟩, ?_⟩
  intro i
  apply (PiecewiseRational.const (σ := σ) (p.coeff i)).congr
  intro x
  simp

theorem C {f : (σ → ℝ) → ℝ} (hf : PiecewiseRational f) :
    RationalPolynomialFamily (fun x => Polynomial.C (f x)) := by
  refine ⟨⟨0, by simp⟩, ?_⟩
  intro i
  by_cases hi : i = 0
  · simpa only [hi, coeff_C_zero] using hf
  · simpa only [coeff_C, hi, ite_false, Rat.cast_zero] using PiecewiseRational.const (σ := σ) 0

theorem zero : RationalPolynomialFamily (fun _ : σ → ℝ => (0 : ℝ[X])) := by
  simpa using const (σ := σ) 0

theorem one : RationalPolynomialFamily (fun _ : σ → ℝ => (1 : ℝ[X])) := by
  simpa using const (σ := σ) 1

theorem X : RationalPolynomialFamily (fun _ : σ → ℝ => (Polynomial.X : ℝ[X])) := by
  simpa using const (σ := σ) Polynomial.X

theorem add (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    RationalPolynomialFamily (fun x => p x + q x) := by
  obtain ⟨N, hN⟩ := hp.bounded
  obtain ⟨M, hM⟩ := hq.bounded
  refine ⟨⟨max N M, fun x => (natDegree_add_le _ _).trans (max_le_max (hN x) (hM x))⟩, ?_⟩
  intro i
  simpa only [coeff_add] using (hp.coefficient i).add (hq.coefficient i)

theorem neg (hp : RationalPolynomialFamily p) : RationalPolynomialFamily (fun x => -p x) := by
  refine ⟨?_, ?_⟩
  · simpa only [natDegree_neg] using hp.bounded
  · intro i
    simpa only [coeff_neg] using (hp.coefficient i).neg

theorem sub (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    RationalPolynomialFamily (fun x => p x - q x) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem mul (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    RationalPolynomialFamily (fun x => p x * q x) := by
  obtain ⟨N, hN⟩ := hp.bounded
  obtain ⟨M, hM⟩ := hq.bounded
  refine ⟨⟨N + M, fun x => natDegree_mul_le.trans (Nat.add_le_add (hN x) (hM x))⟩, ?_⟩
  intro i
  simpa only [coeff_mul] using PiecewiseRational.sum (Finset.antidiagonal i)
    (fun k x => (p x).coeff k.1 * (q x).coeff k.2)
    (fun k _ => (hp.coefficient _).mul (hq.coefficient _))

theorem pow (hp : RationalPolynomialFamily p) (n : ℕ) :
    RationalPolynomialFamily (fun x => p x ^ n) := by
  induction n with
  | zero => simpa using (one (σ := σ))
  | succ n ih => simpa only [pow_succ] using ih.mul hp

theorem derivative (hp : RationalPolynomialFamily p) :
    RationalPolynomialFamily (fun x => (p x).derivative) := by
  obtain ⟨N, hN⟩ := hp.bounded
  refine ⟨⟨N, fun x => (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hN x))⟩, ?_⟩
  intro i
  apply ((hp.coefficient (i + 1)).mul (PiecewiseRational.const (i + 1 : ℕ))).congr
  intro x
  simp [coeff_derivative]

theorem zeroSet (hp : RationalPolynomialFamily p) : QSemialgebraic {x | p x = 0} := by
  classical
  obtain ⟨N, hN⟩ := hp.bounded
  have heq : {x | p x = 0} = ⋂ i : Fin (N + 1), {x | (p x).coeff i = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx i
      simp [hx]
    · intro hx
      ext i
      by_cases hi : i ≤ N
      · exact hx ⟨i, by omega⟩
      · exact coeff_eq_zero_of_natDegree_lt ((hN x).trans_lt (by omega))
  rw [heq]
  exact QSemialgebraic.iInter _ (fun i => (hp.coefficient i).zeroSet)

theorem natDegree_le (hp : RationalPolynomialFamily p) (d : ℕ) :
    QSemialgebraic {x | (p x).natDegree ≤ d} := by
  classical
  obtain ⟨N, hN⟩ := hp.bounded
  have heq : {x | (p x).natDegree ≤ d} =
      ⋂ i : Fin (N + 1), {x | d < i.val → (p x).coeff i = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, natDegree_le_iff_coeff_eq_zero]
    constructor
    · intro hx i hi
      exact hx i hi
    · intro hx i hi
      by_cases hiN : i ≤ N
      · exact hx ⟨i, by omega⟩ hi
      · exact coeff_eq_zero_of_natDegree_lt ((hN x).trans_lt (by omega))
  rw [heq]
  apply QSemialgebraic.iInter
  intro i
  by_cases hi : d < i.val
  · simpa only [hi, true_implies] using (hp.coefficient i).zeroSet
  · simpa only [hi, false_implies, Set.setOf_true] using (QSemialgebraic.univ (σ := σ))

theorem natDegree_eq (hp : RationalPolynomialFamily p) (d : ℕ) :
    QSemialgebraic {x | (p x).natDegree = d} := by
  cases d with
  | zero => simpa only [Nat.le_zero] using hp.natDegree_le 0
  | succ d =>
      apply ((hp.natDegree_le (d + 1)).inter (hp.natDegree_le d).compl).congr
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      omega

theorem leadingCoeff (hp : RationalPolynomialFamily p) :
    PiecewiseRational (fun x => (p x).leadingCoeff) := by
  classical
  obtain ⟨N, hN⟩ := hp.bounded
  let i : (σ → ℝ) → Fin (N + 1) := fun x => ⟨(p x).natDegree, by have := hN x; omega⟩
  refine (PiecewiseRational.finite_choice i ?_ (fun j x => (p x).coeff j)
    (fun j => hp.coefficient j)).congr (fun _ => rfl)
  intro j
  simpa only [i, Fin.ext_iff] using hp.natDegree_eq j.val

theorem eval (hp : RationalPolynomialFamily p) {f : (σ → ℝ) → ℝ}
    (hf : PiecewiseRational f) : PiecewiseRational (fun x => (p x).eval (f x)) := by
  obtain ⟨N, hN⟩ := hp.bounded
  refine (PiecewiseRational.sum (Finset.range (N + 1))
    (fun i x => (p x).coeff i * f x ^ i)
    (fun i _ => (hp.coefficient i).mul (hf.pow i))).congr ?_
  intro x
  exact (Polynomial.eval_eq_sum_range' (by have := hN x; omega) (f x)).symm

theorem piecewise (s : Set (σ → ℝ)) [DecidablePred (· ∈ s)] (hs : QSemialgebraic s)
    (hp : RationalPolynomialFamily p) (hq : RationalPolynomialFamily q) :
    RationalPolynomialFamily (s.piecewise p q) := by
  obtain ⟨N, hN⟩ := hp.bounded
  obtain ⟨M, hM⟩ := hq.bounded
  refine ⟨⟨max N M, ?_⟩, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · simpa only [Set.piecewise_eq_of_mem s _ _ hx] using (hN x).trans (Nat.le_max_left _ _)
    · simpa only [Set.piecewise_eq_of_notMem s _ _ hx] using (hM x).trans (Nat.le_max_right _ _)
  · intro i
    apply (PiecewiseRational.piecewise s hs (hp.coefficient i) (hq.coefficient i)).congr
    intro x
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx]

theorem finite_choice {I : Type v} [Fintype I] (i : (σ → ℝ) → I)
    (hi : ∀ a, QSemialgebraic {x | i x = a})
    (p : I → (σ → ℝ) → ℝ[X]) (hp : ∀ a, RationalPolynomialFamily (p a)) :
    RationalPolynomialFamily (fun x => p (i x) x) := by
  classical
  choose N hN using fun a => (hp a).bounded
  refine ⟨⟨Finset.univ.sup N, fun x => (hN _ x).trans (Finset.le_sup (by simp))⟩, ?_⟩
  intro k
  exact PiecewiseRational.finite_choice i hi _ (fun a => (hp a).coefficient k)

end RationalPolynomialFamily

namespace PiecewiseRational

variable {σ : Type u} {f : (σ → ℝ) → ℝ}

theorem sign_fiber (hf : PiecewiseRational f) (a : SignType) :
    QSemialgebraic {x | SignType.sign (f x) = a} := by
  cases a with
  | zero => simpa only [SignType.zero_eq_zero, sign_eq_zero_iff] using hf.zeroSet
  | pos => simpa only [SignType.pos_eq_one, sign_eq_one_iff] using hf.positiveSet
  | neg =>
      simpa only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, Rat.cast_zero] using hf.lt (const 0)

theorem sign (hf : PiecewiseRational f) : PiecewiseRational (fun x => (SignType.sign (f x) : ℝ)) := by
  have h := finite_choice (fun x => SignType.sign (f x)) (sign_fiber hf)
    (fun a (_ : σ → ℝ) => (a : ℚ)) (fun a => const (a : ℚ))
  apply h.congr
  intro x
  cases SignType.sign (f x) <;> simp

end PiecewiseRational

end TuranUniversality.Algebraicity
