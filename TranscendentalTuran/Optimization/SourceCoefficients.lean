module

public import TranscendentalTuran.Optimization.PaperQuadratic
public import TranscendentalTuran.Construction.RootPairWeights

@[expose] public section

/-!
# Exact correspondence between ordinary source coefficients and the paper

Formalization author and responsible maintainer: Xizhi Liu.

The seven physical types are reindexed by the explicit equivalence already
used in the ordinary construction. Root coefficients retain the actual
individual root weights; no equal-weight condition is imposed.
-/

namespace TranscendentalTuran.Optimization.Paper

open Finset MvPolynomial Parameters Encoding Network
open TuranUniversality.Algebraicity
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

def sourceCoordinates (z : Root → ℝ) (y : PhysicalType → ℝ) : Coord → ℝ :=
  Sum.elim z (fun i => y (physicalOfIndex i))

theorem sum_physical_index (f : PhysicalType → ℝ) :
    (∑ i : Fin 7, f (physicalOfIndex i)) = ∑ ν : PhysicalType, f ν := by
  symm
  apply Fintype.sum_equiv physicalEquiv
  intro ν
  simp [physicalEquiv]

theorem sum_physical_explicit (f : PhysicalType → ℝ) :
    (∑ ν : PhysicalType, f ν) = f .base + f .port01 + f .port23 + f .center13 +
      f .center02 + f .ownerH + f .ownerV := by
  change f .base + (f .port01 + (f .port23 + (f .center13 +
    (f .center02 + (f .ownerH + (f .ownerV + 0)))))) = _
  ring

theorem sum_block_explicit (f : Block → ℝ) :
    (∑ b : Block, f b) = f .match0 + f .match1 + f .match2 + f .match3 +
      f .ownerH + f .ownerV := by
  change f .match0 + (f .match1 + (f .match2 + (f .match3 +
    (f .ownerH + (f .ownerV + 0))))) = _
  ring

theorem dataMass_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval dataMass (sourceCoordinates z y) = ∑ ν, y ν := by
  simp only [dataMass, qeval_sum, typeVar, qeval_X, sourceCoordinates, Sum.elim_inr]
  exact sum_physical_index y

theorem rootElementary_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (k : ℕ) :
    qeval (rootElementary k) (sourceCoordinates z y) =
      TuranUniversality.Weighted.elementary Finset.univ z k := by
  simp only [rootElementary, TuranUniversality.Weighted.elementary,
    qeval_sum, qeval_prod, rootVar, qeval_X, sourceCoordinates, Sum.elim_inl]

theorem typeElementary_two_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval (typeElementary 2) (sourceCoordinates z y) =
      TuranUniversality.Weighted.elementary Finset.univ y 2 := by
  rw [typeElementary_eval]
  change elementary (fun i : Fin 7 => y (physicalOfIndex i)) 2 = _
  have h₁ := two_mul_elementary_two (fun i : Fin 7 => y (physicalOfIndex i))
  have h₂ := TuranUniversality.Weighted.elementary_second_identity Finset.univ y
  rw [sum_physical_index y, sum_physical_index (fun ν => y ν ^ 2)] at h₁
  linarith

theorem declaringWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (ν : Fin 7) :
    qeval (declaringWeight ν) (sourceCoordinates z y) = Encoding.declaringWeight z ν := by
  simp only [declaringWeight, Encoding.declaringWeight, qeval_sum, qeval_mul,
    rootVar, qeval_X, sourceCoordinates, Sum.elim_inl]

theorem markerWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval markerWeight (sourceCoordinates z y) = Encoding.markerWeight z := by
  simp only [markerWeight, Encoding.markerWeight, qeval_mul, rootVar, qeval_X,
    sourceCoordinates, Sum.elim_inl]

theorem linearWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (ν : PhysicalType) :
    qeval (linearWeight (physicalIndex ν)) (sourceCoordinates z y) =
      pairWeight (allowedPairs ν) z := by
  rw [allowedPairs_weight]
  simp only [linearWeight, qeval_sub, qeval_sum, rootElementary_source_eval,
    markerWeight_source_eval, declaringWeight_source_eval]

theorem linearSum_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval (∑ i : Fin 7, linearWeight i * typeVar i) (sourceCoordinates z y) =
      ∑ ν : PhysicalType, y ν * pairWeight (allowedPairs ν) z := by
  simp only [qeval_sum, qeval_mul, typeVar, qeval_X, sourceCoordinates, Sum.elim_inr]
  symm
  apply Fintype.sum_equiv physicalEquiv
  intro ν
  change y ν * pairWeight (allowedPairs ν) z =
    qeval (linearWeight (physicalIndex ν)) (sourceCoordinates z y) *
      y (physicalOfIndex (physicalIndex ν))
  rw [linearWeight_source_eval, physicalOfIndex_physicalIndex, mul_comm]

theorem genericWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval genericWeight (sourceCoordinates z y) = ∑ j : Fin N, z (Encoding.genericRoot j) := by
  simp only [genericWeight, qeval_sum, rootVar, qeval_X, sourceCoordinates, Sum.elim_inl]
  rfl

theorem matchingWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (b : Fin 4) :
    qeval (matchingWeight b) (sourceCoordinates z y) =
      ∑ j : Fin M, z (Encoding.matchingRoot b j) := by
  simp only [matchingWeight, qeval_sum, rootVar, qeval_X, sourceCoordinates, Sum.elim_inl]
  rfl

theorem ownershipWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (b : Fin 2) :
    qeval (ownershipWeight b) (sourceCoordinates z y) =
      ∑ j : Fin κ, z (Encoding.ownershipRoot b j) := by
  simp only [ownershipWeight, qeval_sum, rootVar, qeval_X, sourceCoordinates, Sum.elim_inl]
  rfl

def physicalSignMass (b : Block) (s : ℤ) (y : PhysicalType → ℝ) : ℝ :=
  ∑ ν, if sign b ν = s then y ν else 0

def ownershipBlock : Fin 2 → Block := ![.ownerH, .ownerV]

theorem matchingPositive_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (b : Fin 4) :
    qeval (matchingPositive b) (sourceCoordinates z y) =
      physicalSignMass (matchingBlock b) 1 y := by
  fin_cases b <;> simp [matchingPositive, qeval_add, typeVar, qeval_X, sourceCoordinates,
    physicalOfIndex, physicalSignMass, sum_physical_explicit, matchingBlock, sign]

theorem matchingNegative_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (b : Fin 4) :
    qeval (matchingNegative b) (sourceCoordinates z y) =
      physicalSignMass (matchingBlock b) (-1) y := by
  fin_cases b <;> simp [matchingNegative, typeVar, qeval_X, sourceCoordinates,
    physicalOfIndex, physicalSignMass, sum_physical_explicit, matchingBlock, sign]

theorem ownershipPositive_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) (b : Fin 2) :
    qeval (ownershipPositive b) (sourceCoordinates z y) =
      physicalSignMass (ownershipBlock b) 1 y := by
  fin_cases b <;> simp [ownershipPositive, typeVar, qeval_X, sourceCoordinates,
    physicalOfIndex, physicalSignMass, sum_physical_explicit, ownershipBlock, sign]

theorem ownershipNegative_source_eval (y : PhysicalType → ℝ) (b : Fin 2) :
    y .base = physicalSignMass (ownershipBlock b) (-1) y := by
  fin_cases b <;> simp [physicalSignMass, sum_physical_explicit, ownershipBlock, sign]

theorem layer_sum_eq_blocks (z : Root → ℝ) (f : Block → ℝ) :
    (∑ r : Layer, z (layerRoot r) * f r.1) =
      (∑ b : Fin 4, (∑ j : Fin M, z (Encoding.matchingRoot b j)) * f (matchingBlock b)) +
      ∑ b : Fin 2, (∑ j : Fin κ, z (Encoding.ownershipRoot b j)) * f (ownershipBlock b) := by
  rw [Fintype.sum_sigma, sum_block_explicit, Fin.sum_univ_four, Fin.sum_univ_two]
  change (∑ j : Fin M, z (Encoding.matchingRoot 0 j) * f .match0) +
      (∑ j : Fin M, z (Encoding.matchingRoot 1 j) * f .match1) +
      (∑ j : Fin M, z (Encoding.matchingRoot 2 j) * f .match2) +
      (∑ j : Fin M, z (Encoding.matchingRoot 3 j) * f .match3) +
      (∑ j : Fin κ, z (Encoding.ownershipRoot 0 j) * f .ownerH) +
      (∑ j : Fin κ, z (Encoding.ownershipRoot 1 j) * f .ownerV) = _
  simp only [← Finset.sum_mul]
  change _ = ((∑ j : Fin M, z (Encoding.matchingRoot 0 j)) * f .match0 +
      (∑ j : Fin M, z (Encoding.matchingRoot 1 j)) * f .match1 +
      (∑ j : Fin M, z (Encoding.matchingRoot 2 j)) * f .match2 +
      (∑ j : Fin M, z (Encoding.matchingRoot 3 j)) * f .match3) +
      ((∑ j : Fin κ, z (Encoding.ownershipRoot 0 j)) * f .ownerH +
      (∑ j : Fin κ, z (Encoding.ownershipRoot 1 j)) * f .ownerV)
  ring

theorem quadraticWeight_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval quadraticWeight (sourceCoordinates z y) =
      (∑ j : Fin N, z (Encoding.genericRoot j)) *
        TuranUniversality.Weighted.elementary Finset.univ y 2 +
      (∑ r : Layer, z (layerRoot r) *
        (physicalSignMass r.1 1 y ^ 2 + physicalSignMass r.1 (-1) y ^ 2)) / 2 := by
  rw [layer_sum_eq_blocks z (fun b => physicalSignMass b 1 y ^ 2 +
    physicalSignMass b (-1) y ^ 2)]
  simp only [quadraticWeight, qeval_add, qeval_mul, qeval_sum, qeval_pow, qeval_C,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, genericWeight_source_eval,
    typeElementary_two_source_eval, matchingWeight_source_eval, ownershipWeight_source_eval,
    matchingPositive_source_eval, matchingNegative_source_eval, ownershipPositive_source_eval]
  have hb : qeval (typeVar 0) (sourceCoordinates z y) = y .base := by
    simp [typeVar, qeval_X, sourceCoordinates, physicalOfIndex]
  rw [hb]
  simp_rw [← ownershipNegative_source_eval y]
  ring

theorem resistance_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    resistance (sourceCoordinates z y) =
      ∑ b : Fin 4, (∑ j : Fin M, z (Encoding.matchingRoot b j))⁻¹ := by
  simp only [resistance, matchingWeight_source_eval]

theorem normalization_source_eval (z : Root → ℝ) (y : PhysicalType → ℝ) :
    qeval normalization (sourceCoordinates z y) = (1 + ∑ ν, y ν) ^ 3 := by
  simp only [normalization, qeval_pow, qeval_add, qeval_one, dataMass_source_eval]

theorem sourceCoordinates_mem {z : Root → ℝ} {y : PhysicalType → ℝ}
    (hroot : ∀ r, 1 / (q : ℝ) - 16 / (q : ℝ) ^ 2 ≤ z r ∧
      z r ≤ 1 / (q : ℝ) + 16 / (q : ℝ) ^ 2)
    (hsum : ∑ r, z r = 1) (hy : ∀ ν, 0 ≤ y ν) (hmass : (∑ ν, y ν) ≤ 2 / (q : ℝ)) :
    sourceCoordinates z y ∈ rootTypeDomain q := by
  refine ⟨hroot, hsum, ?_, ?_⟩
  · intro i
    exact hy (physicalOfIndex i)
  · change (∑ i : Fin 7, y (physicalOfIndex i)) ≤ 2 / (q : ℝ)
    rwa [sum_physical_index]

theorem affine_source_le_Ψ (g : ℝ) {z : Root → ℝ} {y : PhysicalType → ℝ}
    (hz : sourceCoordinates z y ∈ rootTypeDomain q) :
    A.eval (sourceCoordinates z y) + g * B.eval (sourceCoordinates z y) ≤ Ψ g :=
  (isGreatest_rationalAffineMaximum (rootTypeDomain_isCompact q_ge_64)
    (rootTypeDomain_nonempty q_pos) A B A_regular B_regular g).2 ⟨_, hz, rfl⟩

end TranscendentalTuran.Optimization.Paper
