module

public import TranscendentalTuran.Algebra.Legacy.RationalSemialgebraic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! # Finite pieces of rational functions

Every piece has a literal rational semialgebraic domain, rational polynomial
numerator and denominator, and a denominator proved nonzero on that domain.
The pieces cover the whole parameter space. They need not be disjoint.
-/

namespace TuranUniversality.Algebraicity

open Set MvPolynomial

universe u v

/-- A finite rational description, with all exceptional zero-denominator
cases accounted for by separate pieces. -/
def PiecewiseRational {σ : Type u} (f : (σ → ℝ) → ℝ) : Prop :=
  ∃ n : ℕ, ∃ D : Fin n → Set (σ → ℝ),
    ∃ p q : Fin n → MvPolynomial σ ℚ,
      (∀ i, QSemialgebraic (D i)) ∧
      (∀ i x, x ∈ D i → qeval (q i) x ≠ 0 ∧ f x = qeval (p i) x / qeval (q i) x) ∧
      ∀ x, ∃ i, x ∈ D i

namespace PiecewiseRational

variable {σ : Type u} {f g : (σ → ℝ) → ℝ}

theorem of_finite {I : Type v} [Fintype I]
    (D : I → Set (σ → ℝ)) (p q : I → MvPolynomial σ ℚ)
    (hD : ∀ i, QSemialgebraic (D i))
    (hval : ∀ i x, x ∈ D i → qeval (q i) x ≠ 0 ∧ f x = qeval (p i) x / qeval (q i) x)
    (hcover : ∀ x, ∃ i, x ∈ D i) : PiecewiseRational f := by
  classical
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => D (e.symm i), fun i => p (e.symm i),
    fun i => q (e.symm i), fun i => hD _, fun i => hval _, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨e i, by simpa using hi⟩

theorem congr (hf : PiecewiseRational f) (hfg : ∀ x, f x = g x) : PiecewiseRational g := by
  have : f = g := funext hfg
  exact this ▸ hf

theorem polynomial (p : MvPolynomial σ ℚ) : PiecewiseRational (qeval p) := by
  refine of_finite (I := Unit) (fun _ => Set.univ) (fun _ => p) (fun _ => 1)
    (fun _ => QSemialgebraic.univ) ?_ (fun _ => ⟨(), Set.mem_univ _⟩)
  intro i x hx
  simp

theorem const (q : ℚ) : PiecewiseRational (fun _ : σ → ℝ => (q : ℝ)) := by
  exact (polynomial (σ := σ) (C q)).congr (fun x => qeval_C q x)

theorem add (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    PiecewiseRational (fun x => f x + g x) := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  obtain ⟨m, E, a, b, hE, hw, hd⟩ := hg
  refine of_finite (I := Fin n × Fin m) (fun i => D i.1 ∩ E i.2)
    (fun i => p i.1 * b i.2 + a i.2 * q i.1)
    (fun i => q i.1 * b i.2) (fun i => (hD _).inter (hE _)) ?_ ?_
  · intro i x hx
    obtain ⟨hq, hf⟩ := hv i.1 x hx.1
    obtain ⟨hb, hg⟩ := hw i.2 x hx.2
    refine ⟨by simpa using mul_ne_zero hq hb, ?_⟩
    simp only [qeval_add, qeval_mul, hf, hg]
    field_simp
  · intro x
    obtain ⟨i, hi⟩ := hc x
    obtain ⟨j, hj⟩ := hd x
    exact ⟨(i, j), hi, hj⟩

theorem neg (hf : PiecewiseRational f) : PiecewiseRational (fun x => -f x) := by
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  refine ⟨n, D, fun i => -p i, q, hD, ?_, hc⟩
  intro i x hx
  obtain ⟨hq, hf⟩ := hv i x hx
  exact ⟨hq, by simp only [hf, qeval_neg, neg_div]⟩

theorem sub (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    PiecewiseRational (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    PiecewiseRational (fun x => f x * g x) := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  obtain ⟨m, E, a, b, hE, hw, hd⟩ := hg
  refine of_finite (I := Fin n × Fin m) (fun i => D i.1 ∩ E i.2)
    (fun i => p i.1 * a i.2) (fun i => q i.1 * b i.2)
    (fun i => (hD _).inter (hE _)) ?_ ?_
  · intro i x hx
    obtain ⟨hq, hf⟩ := hv i.1 x hx.1
    obtain ⟨hb, hg⟩ := hw i.2 x hx.2
    exact ⟨by simpa using mul_ne_zero hq hb,
      by simp only [qeval_mul, hf, hg, div_mul_div_comm]⟩
  · intro x
    obtain ⟨i, hi⟩ := hc x
    obtain ⟨j, hj⟩ := hd x
    exact ⟨(i, j), hi, hj⟩

theorem inv (hf : PiecewiseRational f) : PiecewiseRational (fun x => (f x)⁻¹) := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  let E : Fin n ⊕ Fin n → Set (σ → ℝ) := Sum.elim
    (fun i => D i ∩ {x | qeval (p i) x = 0})
    (fun i => D i ∩ {x | qeval (p i) x ≠ 0})
  refine of_finite E (Sum.elim (fun _ => 0) q) (Sum.elim (fun _ => 1) p) ?_ ?_ ?_
  · intro i
    cases i with
    | inl i => exact (hD i).inter (QSemialgebraic.zero (p i))
    | inr i => exact (hD i).inter (QSemialgebraic.zero (p i)).compl
  · intro i x hx
    cases i with
    | inl i =>
        obtain ⟨hD', hp⟩ := hx
        obtain ⟨hq, hf⟩ := hv i x hD'
        change qeval (p i) x = 0 at hp
        refine ⟨by simp, ?_⟩
        simp only [hf, hp, zero_div, inv_zero, Sum.elim_inl, qeval_zero, qeval_one]
    | inr i =>
        obtain ⟨hD', hp⟩ := hx
        obtain ⟨hq, hf⟩ := hv i x hD'
        exact ⟨hp, by simp only [Sum.elim_inr, hf, inv_div]⟩
  · intro x
    obtain ⟨i, hi⟩ := hc x
    by_cases hp : qeval (p i) x = 0
    · exact ⟨Sum.inl i, hi, hp⟩
    · exact ⟨Sum.inr i, hi, hp⟩

theorem div (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    PiecewiseRational (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem pow (hf : PiecewiseRational f) (n : ℕ) : PiecewiseRational (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using (const (σ := σ) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem sum {I : Type*} (F : Finset I) (h : I → (σ → ℝ) → ℝ)
    (hh : ∀ i ∈ F, PiecewiseRational (h i)) : PiecewiseRational (fun x => ∑ i ∈ F, h i x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (const (σ := σ) 0)
  | @insert i F hi ih =>
      simpa only [Finset.sum_insert hi] using (hh i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj)))

theorem prod {I : Type*} (F : Finset I) (h : I → (σ → ℝ) → ℝ)
    (hh : ∀ i ∈ F, PiecewiseRational (h i)) : PiecewiseRational (fun x => ∏ i ∈ F, h i x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (const (σ := σ) 1)
  | @insert i F hi ih =>
      simpa only [Finset.prod_insert hi] using (hh i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj)))

theorem zeroSet (hf : PiecewiseRational f) : QSemialgebraic {x | f x = 0} := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  have heq : {x | f x = 0} = ⋃ i, D i ∩ {x | qeval (p i) x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hc x
      obtain ⟨hq, hf⟩ := hv i x hi
      exact ⟨i, hi, (div_eq_zero_iff.mp (hf ▸ hx)).resolve_right hq⟩
    · rintro ⟨i, hi, hp⟩
      obtain ⟨hq, hf⟩ := hv i x hi
      simp only [hf, hp, zero_div]
  rw [heq]
  exact QSemialgebraic.iUnion _ (fun i => (hD i).inter (QSemialgebraic.zero (p i)))

theorem positiveSet (hf : PiecewiseRational f) : QSemialgebraic {x | 0 < f x} := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  have heq : {x | 0 < f x} = ⋃ i, D i ∩ {x | 0 < qeval (p i * q i) x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hc x
      obtain ⟨hq, hf⟩ := hv i x hi
      exact ⟨i, hi, by simpa only [qeval_mul, mul_pos_iff] using (div_pos_iff.mp (hf ▸ hx))⟩
    · rintro ⟨i, hi, hp⟩
      obtain ⟨hq, hf⟩ := hv i x hi
      rw [hf, div_pos_iff]
      simpa only [qeval_mul, mul_pos_iff] using hp
  rw [heq]
  exact QSemialgebraic.iUnion _ (fun i => (hD i).inter (QSemialgebraic.positive (p i * q i)))

theorem eq (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    QSemialgebraic {x | f x = g x} := by
  simpa only [sub_eq_zero] using (hf.sub hg).zeroSet

theorem ne (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    QSemialgebraic {x | f x ≠ g x} := (hf.eq hg).compl

theorem lt (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    QSemialgebraic {x | f x < g x} := by
  simpa only [sub_pos] using (hg.sub hf).positiveSet

theorem le (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    QSemialgebraic {x | f x ≤ g x} := by
  simpa only [Set.compl_setOf, not_lt] using (hg.lt hf).compl

theorem piecewise (s : Set (σ → ℝ)) [DecidablePred (· ∈ s)] (hs : QSemialgebraic s)
    (hf : PiecewiseRational f) (hg : PiecewiseRational g) :
    PiecewiseRational (s.piecewise f g) := by
  classical
  obtain ⟨n, D, p, q, hD, hv, hc⟩ := hf
  obtain ⟨m, E, a, b, hE, hw, hd⟩ := hg
  refine of_finite (I := Fin n ⊕ Fin m)
    (Sum.elim (fun i => D i ∩ s) (fun i => E i ∩ sᶜ))
    (Sum.elim p a) (Sum.elim q b) ?_ ?_ ?_
  · intro i
    cases i with
    | inl i => exact (hD _).inter hs
    | inr i => exact (hE _).inter hs.compl
  · intro i x hx
    cases i with
    | inl i => simpa only [Sum.elim_inl, Set.piecewise_eq_of_mem s _ _ hx.2] using hv i x hx.1
    | inr i =>
        simpa only [Sum.elim_inr, Set.piecewise_eq_of_notMem s _ _ hx.2] using hw i x hx.1
  · intro x
    by_cases hx : x ∈ s
    · obtain ⟨i, hi⟩ := hc x
      exact ⟨Sum.inl i, hi, hx⟩
    · obtain ⟨i, hi⟩ := hd x
      exact ⟨Sum.inr i, hi, hx⟩

/-- A finite choice between rational functions stays piecewise rational,
provided every parameter fiber of the choice is rational semialgebraic. -/
theorem finite_choice {I : Type v} [Fintype I] (i : (σ → ℝ) → I)
    (hi : ∀ a, QSemialgebraic {x | i x = a})
    (f : I → (σ → ℝ) → ℝ) (hf : ∀ a, PiecewiseRational (f a)) :
    PiecewiseRational (fun x => f (i x) x) := by
  classical
  have hp : PiecewiseRational (fun x => ∑ a : I, if i x = a then f a x else 0) :=
    sum Finset.univ _ (fun a _ => by
      apply (piecewise {x | i x = a} (hi a) (hf a) (const 0)).congr
      intro x
      simp only [Set.piecewise, Set.mem_setOf_eq, Rat.cast_zero])
  simpa using hp

end PiecewiseRational

end TuranUniversality.Algebraicity
