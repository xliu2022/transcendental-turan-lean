module

public import TranscendentalTuran.Algebra.Legacy.ParameterizedRoots
public import TranscendentalTuran.Algebra.Legacy.WholeLineSigns
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set Polynomial Finset TauCeti.SignDetermination

universe u v

namespace RationalPolynomialFamily

variable {σ : Type u} {J : Type v} [Fintype J]

theorem sampleProduct (Q : J → (σ → ℝ) → ℝ[X])
    (hQ : ∀ j, RationalPolynomialFamily (Q j)) :
    RationalPolynomialFamily (fun x => TauCeti.SignDetermination.sampleProduct (fun j => Q j x)) := by
  classical
  have hf (j : J) : RationalPolynomialFamily (fun x => if Q j x = 0 then 1 else Q j x) := by
    exact piecewise {x | Q j x = 0} (hQ j).zeroSet (one (σ := σ)) (hQ j)
  refine (prod univ _ (fun j _ => hf j)).congr ?_
  intro x
  simp [sampleProduct_def, Finset.prod_ite]

/-- Genuine elimination of a real variable from a complete finite sign
condition, with coefficients remaining rational semialgebraic functions
of the other real variables. -/
theorem exists_sign_condition [DecidableEq J]
    (Q : J → (σ → ℝ) → ℝ[X]) (hQ : ∀ j, RationalPolynomialFamily (Q j))
    (s : J → SignType) :
    QSemialgebraic {x | ∃ z : ℝ, ∀ j, SignType.sign ((Q j x).eval z) = s j} := by
  classical
  have hp := sampleProduct Q hQ
  have htop : QSemialgebraic {x | ∀ j, SignType.sign (Q j x).leadingCoeff = s j} := by
    simpa only [Set.iInter_setOf] using QSemialgebraic.iInter _
      (fun j => (hQ j).leadingCoeff.sign_fiber (s j))
  have hbot : QSemialgebraic {x | ∀ j,
      SignType.sign ((Q j x).leadingCoeff * (-1) ^ (Q j x).natDegree) = s j} := by
    have hf (j : J) : PiecewiseRational (fun x =>
        (Q j x).leadingCoeff * (-1) ^ (Q j x).natDegree) :=
      (hQ j).natDegree_scalar_choice
        (fun n x => (Q j x).leadingCoeff * (-1) ^ n) (fun n =>
        ((hQ j).leadingCoeff.mul (PiecewiseRational.const ((-1 : ℚ) ^ n))).congr
          (fun x => by simp))
    simpa only [Set.iInter_setOf] using QSemialgebraic.iInter _
      (fun j => (hf j).sign_fiber (s j))
  have h := (hp.root_sign_condition Q hQ s).union
    ((hp.derivative.root_sign_condition Q hQ s).union (hbot.union htop))
  apply h.congr
  ext x
  exact (wholeLine_sign_iff (fun j => Q j x) s).symm

end RationalPolynomialFamily

/-- Curry the distinguished variable `none`; all other variables are real
parameters, and all symbolic coefficients remain polynomials over ℚ. -/
noncomputable def curryPolynomial {σ : Type u} (p : MvPolynomial (Option σ) ℚ)
    (x : σ → ℝ) : ℝ[X] :=
  (MvPolynomial.optionEquivLeft ℚ σ p).map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x)

theorem curryPolynomial_family {σ : Type u} (p : MvPolynomial (Option σ) ℚ) :
    RationalPolynomialFamily (curryPolynomial p) := by
  refine ⟨⟨(MvPolynomial.optionEquivLeft ℚ σ p).natDegree, fun _ => natDegree_map_le⟩, ?_⟩
  intro i
  exact (PiecewiseRational.polynomial ((MvPolynomial.optionEquivLeft ℚ σ p).coeff i)).congr
    (fun _ => (Polynomial.coeff_map _ _).symm)

theorem curryPolynomial_eval {σ : Type u} (p : MvPolynomial (Option σ) ℚ)
    (x : σ → ℝ) (y : ℝ) :
    (curryPolynomial p x).eval y = qeval p (fun i => i.elim y x) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [curryPolynomial, qeval]
  | add p q hp hq => simp only [curryPolynomial, map_add, Polynomial.eval_add] at *; simp [hp, hq]
  | mul_X p i hp =>
      cases i <;> simp_all [curryPolynomial, qeval]

namespace QSemialgebraic

variable {σ : Type u}

/-- Every literal finite Boolean description depends on finitely many
rational polynomial signs. The acceptance table is finite because the
sign tuple has a finite type. -/
theorem finite_sign_description {S : Set (σ → ℝ)} (hS : QSemialgebraic S) :
    ∃ n : ℕ, ∃ P : Fin n → MvPolynomial σ ℚ,
      ∃ accept : (Fin n → SignType) → Prop,
        ∀ x, x ∈ S ↔ accept (fun i => SignType.sign (qeval (P i) x)) := by
  induction hS with
  | zero p =>
      refine ⟨1, fun _ => p, fun s => s 0 = 0, ?_⟩
      intro x
      simp only [Set.mem_setOf_eq, sign_eq_zero_iff]
  | positive p =>
      refine ⟨1, fun _ => p, fun s => s 0 = 1, ?_⟩
      intro x
      simp only [Set.mem_setOf_eq, sign_eq_one_iff]
  | compl h ih =>
      obtain ⟨n, P, a, ha⟩ := ih
      exact ⟨n, P, fun s => ¬a s, fun x => not_congr (ha x)⟩
  | inter hs ht ihs iht =>
      obtain ⟨n, P, a, ha⟩ := ihs
      obtain ⟨m, Q, b, hb⟩ := iht
      refine ⟨n + m, Fin.addCases P Q,
        fun s => a (fun i => s (Fin.castAdd m i)) ∧ b (fun j => s (Fin.natAdd n j)), ?_⟩
      intro x
      simpa only [Set.mem_inter_iff, Fin.addCases_left, Fin.addCases_right] using and_congr (ha x) (hb x)

/-- Tarski–Seidenberg projection with the coefficient field explicitly
preserved: eliminating one arbitrary real coordinate from a rational
semialgebraic set again yields a rational semialgebraic set. -/
theorem exists_one {S : Set (Option σ → ℝ)} (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∃ y : ℝ, (fun i => i.elim y x) ∈ S} := by
  classical
  obtain ⟨n, P, accept, hP⟩ := hS.finite_sign_description
  let T (s : Fin n → SignType) : Set (σ → ℝ) :=
    if accept s then {x | ∃ y : ℝ, ∀ i, SignType.sign (qeval (P i) (fun j => j.elim y x)) = s i}
    else ∅
  have hT : ∀ s, QSemialgebraic (T s) := by
    intro s
    by_cases hs : accept s
    · have h := RationalPolynomialFamily.exists_sign_condition (fun i => curryPolynomial (P i))
        (fun i => curryPolynomial_family (P i)) s
      simpa only [T, hs, ite_true, curryPolynomial_eval] using h
    · simpa only [T, hs, ite_false] using (empty (σ := σ))
  apply (iUnion T hT).congr
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs⟩
    by_cases ha : accept s
    · obtain ⟨y, hy⟩ : ∃ y : ℝ, ∀ i,
          SignType.sign (qeval (P i) (fun j => j.elim y x)) = s i := by simpa [T, ha] using hs
      refine ⟨y, (hP _).mpr ?_⟩
      have heq := funext hy
      exact heq.symm ▸ ha
    · simp [T, ha] at hs
  · rintro ⟨y, hy⟩
    let s : Fin n → SignType := fun i => SignType.sign (qeval (P i) (fun j => j.elim y x))
    have hs : accept s := (hP _).mp hy
    refine ⟨s, ?_⟩
    simpa only [T, hs, ite_true, Set.mem_setOf_eq] using
      (show ∃ z : ℝ, ∀ i, SignType.sign (qeval (P i) (fun j => j.elim z x)) = s i from
        ⟨y, fun _ => rfl⟩)

theorem forall_one {S : Set (Option σ → ℝ)} (hS : QSemialgebraic S) :
    QSemialgebraic {x : σ → ℝ | ∀ y : ℝ, (fun i => i.elim y x) ∈ S} := by
  apply hS.compl.exists_one.compl.congr
  ext x
  simp

end QSemialgebraic

end TuranUniversality.Algebraicity
