module

public import TranscendentalTuran.Optimization.RationalEnvelope
public import TranscendentalTuran.Optimization.Domain
public import TranscendentalTuran.Encoding.RootPairs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The paper's explicit finite rational optimization

Formalization author and responsible maintainer: Xizhi Liu.

The seven coordinates are ordered as
`B, P₀₁, P₂₃, C₁₃, C₀₂, Oₕ, Oᵥ`.
All roots remain free optimization variables. Matching block weights are
sums of their actual root coordinates; no equal-root-weight hypothesis is
imposed. The inverse conductances are cleared by the polynomials `U` and
`V`, so the rational-envelope theorem applies literally.

The theorem at the end proves transcendence of the explicitly defined
finite optimization. Identifying it with the source class Lagrangian is a
separate combinatorial theorem and is not assumed or claimed here.
-/

namespace TranscendentalTuran.Optimization.Paper

open Set Finset MvPolynomial
open Parameters Encoding
open TuranUniversality.Algebraicity

abbrev Coord := RootTypeCoordinates q
abbrev Poly := MvPolynomial Coord ℚ

noncomputable def rootVar (r : Root) : Poly := X (Sum.inl r)
noncomputable def typeVar (ν : Fin 7) : Poly := X (Sum.inr ν)

def matchingRoot (b : Fin 4) (j : Fin M) : Root :=
  ⟨b.val * M + j.val, by
    have hb := b.isLt
    have hj := j.isLt
    have hq : 4 * M ≤ q := by unfold q K; omega
    simp only [M] at *
    omega⟩

def ownershipRoot (b : Fin 2) (j : Fin κ) : Root :=
  ⟨4 * M + b.val * κ + j.val, by
    have hb := b.isLt
    have hj := j.isLt
    have hq : 4 * M + 2 * κ ≤ q := by unfold q K; omega
    simp only [κ, M] at *
    omega⟩

def genericRoot (j : Fin N) : Root :=
  ⟨K + j.val, by have hj := j.isLt; unfold q; omega⟩

noncomputable def rootElementary (k : ℕ) : Poly :=
  ∑ e ∈ (Finset.univ : Finset Root).powersetCard k, ∏ r ∈ e, rootVar r

noncomputable def typeElementary (k : ℕ) : Poly :=
  ∑ e ∈ (Finset.univ : Finset (Fin 7)).powersetCard k, ∏ ν ∈ e, typeVar ν

noncomputable def declaringWeight (ν : Fin 7) : Poly :=
  ∑ j : Fin N, rootVar (declaringRoot ((ν, j), 0)) *
    rootVar (declaringRoot ((ν, j), 1))

noncomputable def markerWeight : Poly := rootVar markerLeft * rootVar markerRight

noncomputable def linearWeight (ν : Fin 7) : Poly :=
  rootElementary 2 - markerWeight - ∑ μ ∈ Finset.univ.erase ν, declaringWeight μ

noncomputable def genericWeight : Poly := ∑ j : Fin N, rootVar (genericRoot j)
noncomputable def matchingWeight (b : Fin 4) : Poly :=
  ∑ j : Fin M, rootVar (matchingRoot b j)
noncomputable def ownershipWeight (b : Fin 2) : Poly :=
  ∑ j : Fin κ, rootVar (ownershipRoot b j)

noncomputable def matchingPositive : Fin 4 → Poly :=
  ![typeVar 0 + typeVar 4, typeVar 0 + typeVar 3,
    typeVar 0 + typeVar 4, typeVar 0 + typeVar 3]
noncomputable def matchingNegative : Fin 4 → Poly := ![typeVar 1, typeVar 1, typeVar 2, typeVar 2]
noncomputable def ownershipPositive : Fin 2 → Poly := ![typeVar 5, typeVar 6]

noncomputable def quadraticWeight : Poly :=
  genericWeight * typeElementary 2 + C (1 / 2 : ℚ) *
    ((∑ b : Fin 4, matchingWeight b *
      ((matchingPositive b) ^ 2 + (matchingNegative b) ^ 2)) +
    ∑ b : Fin 2, ownershipWeight b *
      ((ownershipPositive b) ^ 2 + (typeVar 0) ^ 2))

noncomputable def dataMass : Poly := ∑ ν : Fin 7, typeVar ν
noncomputable def normalization : Poly := (1 + dataMass) ^ 3
noncomputable def numeratorA : Poly :=
  rootElementary 3 + (∑ ν : Fin 7, linearWeight ν * typeVar ν) + quadraticWeight

noncomputable def U : Poly := ∏ b : Fin 4, matchingWeight b
noncomputable def V : Poly :=
  ∑ b : Fin 4, ∏ c ∈ Finset.univ.erase b, matchingWeight c

noncomputable def A : QRationalFunction Coord := ⟨numeratorA, normalization⟩
noncomputable def B : QRationalFunction Coord :=
  ⟨markerWeight ^ 2 * V, C 2 * normalization * U⟩

theorem q_ge_64 : 64 ≤ q := by
  have h := q_large
  norm_num at h
  omega

theorem root_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) (r : Root) :
    0 < z (Sum.inl r) := by
  have hqr : (64 : ℝ) ≤ q := by exact_mod_cast q_ge_64
  have hqpos : (0 : ℝ) < q := by linarith
  have hrad : 16 / (q : ℝ) ^ 2 < 1 / (q : ℝ) := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hqpos) hqpos).2
    nlinarith
  have hr := (hz.1 r).1
  linarith

theorem normalization_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    0 < qeval normalization z := by
  have hy : 0 ≤ ∑ ν : Fin 7, z (Sum.inr ν) :=
    Finset.sum_nonneg (fun ν _ => hz.2.2.1 ν)
  simp only [normalization, dataMass, qeval_pow, qeval_add, qeval_one,
    qeval_sum, typeVar, qeval_X]
  positivity

theorem matchingWeight_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) (b : Fin 4) :
    0 < qeval (matchingWeight b) z := by
  simp only [matchingWeight, qeval_sum, rootVar, qeval_X]
  exact Finset.sum_pos (fun j _ => root_pos hz (matchingRoot b j))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, M_pos⟩⟩)

theorem markerWeight_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    0 < qeval markerWeight z := by
  simp only [markerWeight, qeval_mul, rootVar, qeval_X]
  exact mul_pos (root_pos hz markerLeft) (root_pos hz markerRight)

theorem U_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) : 0 < qeval U z := by
  simp only [U, qeval_prod]
  exact Finset.prod_pos (fun b _ => matchingWeight_pos hz b)

theorem V_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) : 0 < qeval V z := by
  simp only [V, qeval_sum, qeval_prod]
  exact Finset.sum_pos (fun b _ =>
    Finset.prod_pos (fun c _ => matchingWeight_pos hz c)) Finset.univ_nonempty

theorem A_regular : A.RegularOn (rootTypeDomain q) := by
  intro z hz
  exact ne_of_gt (normalization_pos hz)

theorem B_denominator_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    0 < qeval B.denominator z := by
  change 0 < qeval (C 2 * normalization * U) z
  simp only [qeval_mul, qeval_C, Rat.cast_ofNat]
  exact mul_pos (mul_pos (by norm_num) (normalization_pos hz)) (U_pos hz)

theorem B_regular : B.RegularOn (rootTypeDomain q) := by
  intro z hz
  exact ne_of_gt (B_denominator_pos hz)

theorem B_pos {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) : 0 < B.eval z := by
  apply div_pos _ (B_denominator_pos hz)
  change 0 < qeval (markerWeight ^ 2 * V) z
  simp only [qeval_mul, qeval_pow]
  exact mul_pos (sq_pos_of_pos (markerWeight_pos hz)) (V_pos hz)

/-- Clearing the reciprocal conductances does not change the resistance. -/
theorem sum_prod_erase_div_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∑ i : ι, ∏ j ∈ Finset.univ.erase i, w j) / (∏ i : ι, w i) =
      ∑ i : ι, (w i)⁻¹ := by
  have hp : (∏ i : ι, w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply (div_eq_iff hp).2
  rw [← Finset.mul_prod_erase Finset.univ w hi]
  field_simp [hw i]

noncomputable def resistance (z : Coord → ℝ) : ℝ :=
  ∑ b : Fin 4, (qeval (matchingWeight b) z)⁻¹

theorem resistance_eq {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    qeval V z / qeval U z = resistance z := by
  simp only [V, U, resistance, qeval_sum, qeval_prod]
  exact sum_prod_erase_div_prod _ (fun b => ne_of_gt (matchingWeight_pos hz b))

/-- The rational polynomial definition is exactly the source coefficient
`J² R / (2 (1+x)³)` from the manuscript. -/
theorem B_eval_eq_source_coefficient {z : Coord → ℝ} (hz : z ∈ rootTypeDomain q) :
    B.eval z = qeval markerWeight z ^ 2 * resistance z /
      (2 * (1 + ∑ ν : Fin 7, z (Sum.inr ν)) ^ 3) := by
  have hd : qeval normalization z =
      (1 + ∑ ν : Fin 7, z (Sum.inr ν)) ^ 3 := by
    simp only [normalization, dataMass, qeval_pow, qeval_add,
      qeval_one, qeval_sum, typeVar, qeval_X]
  rw [← hd, ← resistance_eq hz]
  change qeval (markerWeight ^ 2 * V) z / qeval (C 2 * normalization * U) z = _
  simp only [qeval_mul, qeval_pow, qeval_C, Rat.cast_ofNat]
  field_simp [ne_of_gt (normalization_pos hz), ne_of_gt (U_pos hz)]

/-- The exact finite optimization `Ψ` from the manuscript. -/
noncomputable def Ψ (g : ℝ) : ℝ := rationalAffineMaximum (rootTypeDomain q) A B g

/-- A concrete, unconditional instance of the arithmetic-envelope theorem.
The only parameter assumption is precisely that its Green input is
transcendental. -/
theorem Ψ_transcendental {g : ℝ} (hg : Transcendental ℚ g) :
    Transcendental ℚ (Ψ g) :=
  rationalAffineMaximum_transcendental (rootTypeDomain_qSemialgebraic q)
    (rootTypeDomain_isCompact q_ge_64) (rootTypeDomain_nonempty q_pos)
    A B A_regular B_regular (fun _ hz => B_pos hz) hg

end TranscendentalTuran.Optimization.Paper
