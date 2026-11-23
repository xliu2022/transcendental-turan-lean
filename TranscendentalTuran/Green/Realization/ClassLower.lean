/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.TemplateClassBound
public import TranscendentalTuran.Green.Realization.BoxSource
public import TranscendentalTuran.Optimization.SourceObjective
public import TranscendentalTuran.Optimization.PaperBudget

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters FiniteNetwork TuranUniversality Source Optimization

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- The lower source coefficient is attained as a supremum by actual finite
ordinary graphs with exactly the prescribed type masses. -/
theorem source_budget_lower (z : Root → ℝ) (y : PhysicalType → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hzsum : ∑ r, z r = 1)
    (hW : ∀ b, 0 < matchingConductance z b)
    (hbudget : ∀ ν, markerWeight z * totalResistance (matchingConductance z) ≤ y ν) :
    (TypedData.targetConstant z y +
      (markerWeight z ^ 2 * totalResistance (matchingConductance z) / 2) * cornerGreen) /
      (1 + ∑ ν, y ν) ^ 3 ≤ classLambda finiteClass := by
  let J := markerWeight z
  have hJ : 0 ≤ J := mul_nonneg (hz markerLeft) (hz markerRight)
  let K := TypedData.targetConstant z y
  let s : ℝ := 1 + ∑ ν, y ν
  let gain : ℕ → ℝ := fun n =>
    J * boxSourceWeight J (matchingConductance z) n (boxData n).mark -
      (∑ r : Layer, z (layerRoot r) *
        (boxData n).layerEnergy r.1 (boxSourceWeight J (matchingConductance z) n)) / 2
  have hpoint : ∀ n, (K + gain n) / s ^ 3 ≤ classLambda finiteClass := by
    intro n
    have hb : ∀ ν, RootData.typeMass (boxData n).type
        (boxSourceWeight J (matchingConductance z) n) ν ≤ y ν :=
      fun ν => (boxSource_typeMass_le hJ hW n ν).trans (hbudget ν)
    have hh := (boxData n).target_bound_classLambda (boxData_legal n) z
      (boxSourceWeight J (matchingConductance z) n) y hz hzsum
      (boxSourceWeight_nonneg hJ hW n) hb
    dsimp [K, gain, s, J] at hh ⊢
    convert hh using 1 <;> ring
  have hg : Tendsto gain atTop
      (𝓝 ((J ^ 2 * totalResistance (matchingConductance z) / 2) * cornerGreen)) :=
    tendsto_boxSource_gain J z hW
  have hlim := ((tendsto_const_nhds (x := K)).add hg).div_const (s ^ 3)
  exact le_of_tendsto hlim (Eventually.of_forall hpoint)

/-- At any feasible root/type point whose budgets contain the source mass, the
exact rational objective is bounded by the actual ordinary-class supremum. -/
theorem affine_source_le_classLambda {z : Root → ℝ} {y : PhysicalType → ℝ}
    (hz : Paper.sourceCoordinates z y ∈ rootTypeDomain q)
    (hbudget : ∀ ν, markerWeight z * totalResistance (matchingConductance z) ≤ y ν) :
    Paper.A.eval (Paper.sourceCoordinates z y) + cornerGreen * Paper.B.eval (Paper.sourceCoordinates z y) ≤
      classLambda finiteClass := by
  have hroot : ∀ r, 0 ≤ z r := fun r => (Paper.root_pos hz r).le
  have hsum : ∑ r, z r = 1 := hz.2.1
  have hW : ∀ b, 0 < matchingConductance z b := by
    intro b
    simpa only [Paper.matchingWeight_source_eval, matchingConductance] using
      Paper.matchingWeight_pos hz b
  have hb := source_budget_lower z y hroot hsum hW hbudget
  rw [Paper.affine_source_eval cornerGreen hz]
  unfold TypedData.targetConstant totalResistance matchingConductance at hb
  convert hb using 1 <;> ring

/-- The exact maximizer has enough mass in every physical type for the finite
source construction and its isolated slack fillers. -/
theorem Ψ_cornerGreen_le_classLambda : Paper.Ψ cornerGreen ≤ classLambda finiteClass := by
  obtain ⟨p, hp, he⟩ := Paper.Ψ_maximizer_exists cornerGreen
  let z : Root → ℝ := fun r => p (Sum.inl r)
  let y : PhysicalType → ℝ := fun ν => p (Sum.inr (physicalIndex ν))
  have hcoord : Paper.sourceCoordinates z y = p := by
    funext i
    cases i with
    | inl r => rfl
    | inr ν => simp [Paper.sourceCoordinates, z, y]
  have hz : Paper.sourceCoordinates z y ∈ rootTypeDomain q := hcoord.symm ▸ hp
  have hmass : markerWeight z * totalResistance (matchingConductance z) < 1 / (32 * (q : ℝ)) := by
    have h := Paper.source_mass_lt_budget hz
    simpa only [Paper.markerWeight_source_eval, Paper.resistance_source_eval,
      totalResistance, matchingConductance] using h
  have htypes := Paper.Ψ_maximizer_type_budget cornerGreen_le_half hp he
  have hbudget : ∀ ν, markerWeight z * totalResistance (matchingConductance z) ≤ y ν := by
    intro ν
    exact (hmass.trans (htypes (physicalIndex ν))).le
  rw [← he, ← hcoord]
  exact affine_source_le_classLambda hz hbudget

end TranscendentalTuran.Green.Realization
