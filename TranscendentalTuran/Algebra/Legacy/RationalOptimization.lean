module

public import TranscendentalTuran.Algebra.Legacy.RationalConsequences

@[expose] public section

namespace TuranUniversality.Algebraicity

open Set MvPolynomial Finset

universe u v

@[simp] theorem qeval_sum {σ : Type u} {I : Type v} (s : Finset I)
    (p : I → MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (∑ i ∈ s, p i) x = ∑ i ∈ s, qeval (p i) x := by simp [qeval]

@[simp] theorem qeval_prod {σ : Type u} {I : Type v} (s : Finset I)
    (p : I → MvPolynomial σ ℚ) (x : σ → ℝ) :
    qeval (∏ i ∈ s, p i) x = ∏ i ∈ s, qeval (p i) x := by simp [qeval]

@[simp] theorem qeval_rename {σ : Type u} {τ : Type v} (f : σ → τ)
    (p : MvPolynomial σ ℚ) (x : τ → ℝ) :
    qeval (MvPolynomial.rename f p) x = qeval p (x ∘ f) := by
  simp only [qeval, MvPolynomial.eval₂Hom_rename]

theorem continuous_qeval {σ : Type u} (p : MvPolynomial σ ℚ) : Continuous (qeval p) := by
  change Continuous (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p)
  simpa only [MvPolynomial.eval₂_eq_eval_map] using
    MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) p)

def unitBox {I : Type u} : Set (I → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

def probabilitySimplex (I : Type u) [Fintype I] : Set (I → ℝ) :=
  {x | x ∈ unitBox ∧ ∑ i, x i = 1}

namespace QSemialgebraic

variable {σ : Type u} {I : Type v} [Fintype I]

theorem unitBox : QSemialgebraic (Algebraicity.unitBox : Set (I → ℝ)) := by
  have h (i : I) : QSemialgebraic {x : I → ℝ | 0 ≤ x i ∧ x i ≤ 1} := by
    have h₁ := QSemialgebraic.le (0 : MvPolynomial I ℚ) (X i)
    have h₂ := QSemialgebraic.le (X i) (1 : MvPolynomial I ℚ)
    apply (h₁.inter h₂).congr
    ext x
    simp
  simpa only [Set.iInter_setOf, Algebraicity.unitBox] using QSemialgebraic.iInter _ h

theorem probabilitySimplex : QSemialgebraic (Algebraicity.probabilitySimplex I) := by
  have hsum : QSemialgebraic {x : I → ℝ | ∑ i, x i = 1} := by
    simpa only [qeval_sum, qeval_X, qeval_one] using
      QSemialgebraic.eq (∑ i : I, X i) (1 : MvPolynomial I ℚ)
  exact unitBox.inter hsum

theorem forall_mem_polynomial_le {K : Set (I → ℝ)} (hK : QSemialgebraic K)
    (p q : MvPolynomial (I ⊕ σ) ℚ) :
    QSemialgebraic {z : σ → ℝ | ∀ x ∈ K, qeval p (Sum.elim x z) ≤ qeval q (Sum.elim x z)} := by
  have h := ((hK.preimage_rename Sum.inl).compl.union (QSemialgebraic.le p q)).forall_finite
  apply h.congr
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Function.comp_def,
    Sum.elim_inl, ← imp_iff_not_or]

theorem exists_mem_polynomial_eq {K : Set (I → ℝ)} (hK : QSemialgebraic K)
    (p q : MvPolynomial (I ⊕ σ) ℚ) :
    QSemialgebraic {z : σ → ℝ | ∃ x ∈ K, qeval p (Sum.elim x z) = qeval q (Sum.elim x z)} := by
  have h := ((hK.preimage_rename Sum.inl).inter (QSemialgebraic.eq p q)).exists_finite
  apply h.congr
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_def, Sum.elim_inl]

end QSemialgebraic

end TuranUniversality.Algebraicity
