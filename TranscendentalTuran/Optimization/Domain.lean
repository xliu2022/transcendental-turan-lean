/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Algebra.Legacy.RationalOptimization
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The normalized root and seven-type domain

This is the domain `𝒫` used in the paper, before the particular rational
objective is supplied. Root coordinates have sum one and lie within
`16 / q²` of `1 / q`; the seven nonnegative type masses sum to at most
`2 / q`. The absolute-value bounds are written as two linear inequalities.
-/

namespace TranscendentalTuran.Optimization

open Set MvPolynomial
open TuranUniversality.Algebraicity

abbrev RootTypeCoordinates (q : ℕ) := Fin q ⊕ Fin 7

def rootTypeDomain (q : ℕ) : Set (RootTypeCoordinates q → ℝ) := {z |
  (∀ i : Fin q,
    1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z (Sum.inl i) ∧
    z (Sum.inl i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2) ∧
  (∑ i : Fin q, z (Sum.inl i)) = 1 ∧
  (∀ ν : Fin 7, 0 ≤ z (Sum.inr ν)) ∧
  (∑ ν : Fin 7, z (Sum.inr ν)) ≤ 2 / (q : ℝ)}

/-- The domain has a rational polynomial sign description; projection
closure is not needed for this lemma. -/
theorem rootTypeDomain_qSemialgebraic (q : ℕ) :
    QSemialgebraic (rootTypeDomain q) := by
  have hr (i : Fin q) : QSemialgebraic {z : RootTypeCoordinates q → ℝ |
      1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z (Sum.inl i) ∧
      z (Sum.inl i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2} := by
    have hlo := QSemialgebraic.le
      (C ((1 : ℚ) / q - 16 / (q : ℚ) ^ 2))
      (X (Sum.inl i) : MvPolynomial (RootTypeCoordinates q) ℚ)
    have hhi := QSemialgebraic.le
      (X (Sum.inl i) : MvPolynomial (RootTypeCoordinates q) ℚ)
      (C ((1 : ℚ) / q + 16 / (q : ℚ) ^ 2))
    apply (hlo.inter hhi).congr
    ext z
    simp [qeval_C, qeval_X]
  have hrall : QSemialgebraic {z : RootTypeCoordinates q → ℝ | ∀ i : Fin q,
      1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z (Sum.inl i) ∧
      z (Sum.inl i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2} := by
    simpa only [Set.iInter_setOf] using QSemialgebraic.iInter _ hr
  have hsum : QSemialgebraic {z : RootTypeCoordinates q → ℝ |
      (∑ i : Fin q, z (Sum.inl i)) = 1} := by
    simpa only [qeval_sum, qeval_X, qeval_one] using
      QSemialgebraic.eq (∑ i : Fin q, X (Sum.inl i)) (1 : MvPolynomial _ ℚ)
  have hy (ν : Fin 7) : QSemialgebraic {z : RootTypeCoordinates q → ℝ |
      0 ≤ z (Sum.inr ν)} := by
    simpa only [qeval_zero, qeval_X] using
      QSemialgebraic.le (0 : MvPolynomial _ ℚ) (X (Sum.inr ν))
  have hyall : QSemialgebraic {z : RootTypeCoordinates q → ℝ |
      ∀ ν : Fin 7, 0 ≤ z (Sum.inr ν)} := by
    simpa only [Set.iInter_setOf] using QSemialgebraic.iInter _ hy
  have hycap : QSemialgebraic {z : RootTypeCoordinates q → ℝ |
      (∑ ν : Fin 7, z (Sum.inr ν)) ≤ 2 / (q : ℝ)} := by
    simpa [qeval_sum, qeval_X, qeval_C] using
      QSemialgebraic.le (∑ ν : Fin 7, X (Sum.inr ν))
        (C ((2 : ℚ) / q) : MvPolynomial (RootTypeCoordinates q) ℚ)
  exact hrall.inter (hsum.inter (hyall.inter hycap))

theorem rootTypeDomain_isClosed (q : ℕ) : IsClosed (rootTypeDomain q) := by
  have hr (i : Fin q) : IsClosed {z : RootTypeCoordinates q → ℝ |
      1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z (Sum.inl i) ∧
      z (Sum.inl i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2} :=
    (isClosed_le continuous_const (continuous_apply (Sum.inl i))).inter
      (isClosed_le (continuous_apply (Sum.inl i)) continuous_const)
  have hrall : IsClosed {z : RootTypeCoordinates q → ℝ | ∀ i : Fin q,
      1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z (Sum.inl i) ∧
      z (Sum.inl i) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2} := by
    simpa only [Set.iInter_setOf] using isClosed_iInter hr
  have hsum : Continuous (fun z : RootTypeCoordinates q → ℝ =>
      ∑ i : Fin q, z (Sum.inl i)) :=
    continuous_finset_sum _ (fun i _ => continuous_apply (Sum.inl i))
  have hyall : IsClosed {z : RootTypeCoordinates q → ℝ |
      ∀ ν : Fin 7, 0 ≤ z (Sum.inr ν)} := by
    simpa only [Set.iInter_setOf] using
      isClosed_iInter (fun ν : Fin 7 =>
        isClosed_le continuous_const (continuous_apply (Sum.inr ν)))
  have hysum : Continuous (fun z : RootTypeCoordinates q → ℝ =>
      ∑ ν : Fin 7, z (Sum.inr ν)) :=
    continuous_finset_sum _ (fun ν _ => continuous_apply (Sum.inr ν))
  exact hrall.inter ((isClosed_eq hsum continuous_const).inter
    (hyall.inter (isClosed_le hysum continuous_const)))

theorem rootTypeDomain_coordinate_bounds {q : ℕ} (hq : 64 ≤ q)
    {z : RootTypeCoordinates q → ℝ} (hz : z ∈ rootTypeDomain q)
    (i : RootTypeCoordinates q) : 0 ≤ z i ∧ z i ≤ 2 / (q : ℝ) := by
  have hqr : (64 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hrad : 16 / (q : ℝ) ^ 2 ≤ 1 / (q : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqpos) hqpos).2
    nlinarith
  rcases i with i | ν
  · have hi := hz.1 i
    have htwice : (1 : ℝ) / q + 1 / q = 2 / q := by ring
    constructor <;> linarith
  · refine ⟨hz.2.2.1 ν, ?_⟩
    exact le_trans (Finset.single_le_sum (fun j _ => hz.2.2.1 j)
      (Finset.mem_univ ν)) hz.2.2.2

theorem rootTypeDomain_isCompact {q : ℕ} (hq : 64 ≤ q) :
    IsCompact (rootTypeDomain q) := by
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : RootTypeCoordinates q => (0 : ℝ))
      (fun _ : RootTypeCoordinates q => 2 / (q : ℝ)))).of_isClosed_subset
      (rootTypeDomain_isClosed q)
  intro z hz
  exact ⟨fun i => (rootTypeDomain_coordinate_bounds hq hz i).1,
    fun i => (rootTypeDomain_coordinate_bounds hq hz i).2⟩

theorem rootTypeDomain_nonempty {q : ℕ} (hq : 0 < q) :
    (rootTypeDomain q).Nonempty := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  let z : RootTypeCoordinates q → ℝ :=
    Sum.elim (fun _ => 1 / (q : ℝ)) (fun _ => 0)
  refine ⟨z, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hrad : (0 : ℝ) ≤ 16 / (q : ℝ) ^ 2 := by positivity
    change 1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ 1 / (q : ℝ) ∧
      1 / (q : ℝ) ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2
    constructor <;> linarith
  · simp only [z, Sum.elim_inl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro ν
    exact le_rfl
  · simp only [z, Sum.elim_inr, Finset.sum_const_zero]
    positivity

end TranscendentalTuran.Optimization
