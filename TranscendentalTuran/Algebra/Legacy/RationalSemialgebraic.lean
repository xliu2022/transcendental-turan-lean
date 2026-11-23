module

public import TranscendentalTuran.Algebra.Legacy.Univariate
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Semialgebraic sets with coefficients explicitly restricted to ℚ

The constructors are precisely finite Boolean operations on rational
polynomial sign conditions. Projection is deliberately not a constructor.
Thus a later projection theorem must preserve the coefficient field rather
than merely return an arbitrary real-coefficient description.
-/

namespace TuranUniversality.Algebraicity

open Set MvPolynomial

universe u v

noncomputable def qeval {σ : Type u} (p : MvPolynomial σ ℚ) (x : σ → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x p

@[simp] theorem qeval_C {σ : Type u} (q : ℚ) (x : σ → ℝ) : qeval (C q) x = q := by
  simp [qeval]

@[simp] theorem qeval_X {σ : Type u} (i : σ) (x : σ → ℝ) : qeval (X i) x = x i := by
  simp [qeval]

@[simp] theorem qeval_zero {σ : Type u} (x : σ → ℝ) : qeval (0 : MvPolynomial σ ℚ) x = 0 := by
  simp [qeval]

@[simp] theorem qeval_one {σ : Type u} (x : σ → ℝ) : qeval (1 : MvPolynomial σ ℚ) x = 1 := by
  simp [qeval]

@[simp] theorem qeval_add {σ : Type u} (p q : MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (p + q) x = qeval p x + qeval q x := by simp [qeval]

@[simp] theorem qeval_neg {σ : Type u} (p : MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (-p) x = -qeval p x := by simp [qeval]

@[simp] theorem qeval_sub {σ : Type u} (p q : MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (p - q) x = qeval p x - qeval q x := by simp [qeval]

@[simp] theorem qeval_mul {σ : Type u} (p q : MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (p * q) x = qeval p x * qeval q x := by simp [qeval]

@[simp] theorem qeval_pow {σ : Type u} (p : MvPolynomial σ ℚ) (n : ℕ) (x : σ → ℝ) :
    qeval (p ^ n) x = qeval p x ^ n := by simp [qeval]

/-- Literal finite Boolean closure of rational polynomial equalities and
strict inequalities; no quantifier or image constructor is included. -/
inductive QSemialgebraic {σ : Type u} : Set (σ → ℝ) → Prop
  | zero (p : MvPolynomial σ ℚ) : QSemialgebraic {x | qeval p x = 0}
  | positive (p : MvPolynomial σ ℚ) : QSemialgebraic {x | 0 < qeval p x}
  | compl {s} : QSemialgebraic s → QSemialgebraic sᶜ
  | inter {s t} : QSemialgebraic s → QSemialgebraic t → QSemialgebraic (s ∩ t)

namespace QSemialgebraic

variable {σ : Type u} {τ : Type v}

theorem congr {s t : Set (σ → ℝ)} (hs : QSemialgebraic s) (hst : s = t) :
    QSemialgebraic t := hst ▸ hs

theorem univ : QSemialgebraic (Set.univ : Set (σ → ℝ)) := by
  convert QSemialgebraic.zero (0 : MvPolynomial σ ℚ) using 1 <;> simp

theorem empty : QSemialgebraic (∅ : Set (σ → ℝ)) := by
  simpa only [Set.compl_univ] using (univ (σ := σ)).compl

theorem union {s t : Set (σ → ℝ)} (hs : QSemialgebraic s) (ht : QSemialgebraic t) :
    QSemialgebraic (s ∪ t) := by
  simpa only [Set.compl_inter, compl_compl] using (hs.compl.inter ht.compl).compl

theorem diff {s t : Set (σ → ℝ)} (hs : QSemialgebraic s) (ht : QSemialgebraic t) :
    QSemialgebraic (s \ t) := hs.inter ht.compl

theorem finite_iUnion {I : Type*} (F : Finset I) (s : I → Set (σ → ℝ))
    (hs : ∀ i ∈ F, QSemialgebraic (s i)) : QSemialgebraic (⋃ i ∈ F, s i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (empty (σ := σ))
  | @insert i F hi ih =>
      simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
        (hs i (Finset.mem_insert_self _ _)).union
          (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)))

theorem iUnion {I : Type*} [Fintype I] (s : I → Set (σ → ℝ))
    (hs : ∀ i, QSemialgebraic (s i)) : QSemialgebraic (⋃ i, s i) := by
  simpa only [Finset.mem_univ, Set.iUnion_true] using
    finite_iUnion Finset.univ s (fun i _ => hs i)

theorem iInter {I : Type*} [Fintype I] (s : I → Set (σ → ℝ))
    (hs : ∀ i, QSemialgebraic (s i)) : QSemialgebraic (⋂ i, s i) := by
  simpa only [Set.compl_iUnion, compl_compl] using
    (iUnion (fun i => (s i)ᶜ) (fun i => (hs i).compl)).compl

theorem eq (p q : MvPolynomial σ ℚ) : QSemialgebraic {x | qeval p x = qeval q x} := by
  simpa only [qeval_sub, sub_eq_zero] using zero (p - q)

theorem lt (p q : MvPolynomial σ ℚ) : QSemialgebraic {x | qeval p x < qeval q x} := by
  simpa only [qeval_sub, sub_pos] using positive (q - p)

theorem le (p q : MvPolynomial σ ℚ) : QSemialgebraic {x | qeval p x ≤ qeval q x} := by
  simpa only [Set.compl_setOf, not_lt] using (lt q p).compl

theorem ne (p q : MvPolynomial σ ℚ) : QSemialgebraic {x | qeval p x ≠ qeval q x} :=
  (eq p q).compl

theorem preimage_rename {s : Set (σ → ℝ)} (hs : QSemialgebraic s) (f : σ → τ) :
    QSemialgebraic ((fun x : τ → ℝ => x ∘ f) ⁻¹' s) := by
  induction hs with
  | zero p =>
      simpa only [Set.preimage_setOf_eq, qeval, MvPolynomial.eval₂Hom_rename] using
        QSemialgebraic.zero (MvPolynomial.rename f p)
  | positive p =>
      simpa only [Set.preimage_setOf_eq, qeval, MvPolynomial.eval₂Hom_rename] using
        QSemialgebraic.positive (MvPolynomial.rename f p)
  | compl hs ih => exact ih.compl
  | inter hs ht ihs iht => exact ihs.inter iht

end QSemialgebraic

end TuranUniversality.Algebraicity
