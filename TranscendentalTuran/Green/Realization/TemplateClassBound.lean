/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.TemplateLegal
public import TranscendentalTuran.Green.Realization.TemplatePolynomial
public import TranscendentalTuran.Green.Realization.FillerWeights
public import TranscendentalTuran.Green.Realization.ClassLowerTools
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace TranscendentalTuran.Green.Realization.TypedData

open Network Encoding Parameters TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [Fintype D] [DecidableEq D] (H : TypedData D)

/-- The fixed target-type contribution, independent of the chosen source network. -/
def targetConstant (z : Root → ℝ) (y : PhysicalType → ℝ) : ℝ :=
  Weighted.elementary Finset.univ z 3 +
    (∑ ν, y ν * pairWeight (allowedPairs ν) z) + RootData.typedQuadratic z y

/-- Filling every type deficit by increasingly many isolated vertices removes the
extra quadratic energy in the limit. The conclusion is a lower bound for the
actual supremum of ordinary finite admissible graphs. -/
theorem target_bound_classLambda (hL : H.Legal) (z : Root → ℝ) (w : D → ℝ)
    (y : PhysicalType → ℝ) (hz : ∀ r, 0 ≤ z r) (hzsum : ∑ r, z r = 1)
    (hw : ∀ d, 0 ≤ w d) (hbudget : ∀ ν, RootData.typeMass H.type w ν ≤ y ν) :
    (targetConstant z y + markerWeight z * w H.mark -
      (∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w) / 2) /
      (1 + ∑ ν, y ν) ^ 3 ≤ classLambda finiteClass := by
  let a : PhysicalType → ℝ := fun ν => y ν - RootData.typeMass H.type w ν
  let C : ℝ := fillerEnergyCost z a
  let E : ℝ := ∑ r : Layer, z (layerRoot r) * H.layerEnergy r.1 w
  let K : ℝ := targetConstant z y + markerWeight z * w H.mark
  let s : ℝ := 1 + ∑ ν, y ν
  have ha : ∀ ν, 0 ≤ a ν := fun ν => sub_nonneg.mpr (hbudget ν)
  have hy : ∀ ν, 0 ≤ y ν := fun ν =>
    (RootData.typeMass_nonneg H.type w hw ν).trans (hbudget ν)
  have hs : 0 < s := by
    have hys := Finset.sum_nonneg (fun ν (_ : ν ∈ Finset.univ) => hy ν)
    dsimp [s]
    linarith
  have hpoint : ∀ n : ℕ, 0 < n →
      (K - (E + C / (n : ℝ)) / 2) / s ^ 3 ≤ classLambda finiteClass := by
    intro n hn
    let Hn := H.withUniformFillers n
    let wn := H.uniformFillerWeight n w a
    have hLn : Hn.Legal := H.withFillers_legal (Prod.fst : UniformFiller n → PhysicalType) hL
    have hgn := Hn.graph_rootedLegal hLn
    have hwn : ∀ d, 0 ≤ wn d := H.uniformFillerWeight_nonneg n hw ha
    have hm : ∀ ν, RootData.typeMass Hn.type wn ν = y ν :=
      fun ν => H.uniformFiller_typeMass_target hn w y ν
    have hmf : RootData.typeMass Hn.type wn = y := funext hm
    have hsum : (∑ v, Sum.elim z wn v) = s := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hzsum, ← RootData.sum_typeMass Hn.type wn]
      simp_rw [hm]
      rfl
    have hnonneg : ∀ v, 0 ≤ Sum.elim z wn v := by
      intro v
      cases v with
      | inl r => exact hz r
      | inr d => exact hwn d
    have hb := normalized_polynomial_le_source_classLambda Hn.graph
      ⟨sumRooting _, hgn⟩ (Sum.elim z wn) hnonneg hs hsum
    have hp := Hn.graph_edgePolynomial_eq_layerEnergy hgn z wn
    rw [hmf] at hp
    have hmark : wn Hn.mark = w H.mark := rfl
    rw [hmark, H.uniformFiller_energy_sum hn z w a] at hp
    rw [hp] at hb
    exact hb
  have hC : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hlim : Tendsto (fun n : ℕ => (K - (E + C / (n : ℝ)) / 2) / s ^ 3)
      atTop (𝓝 ((K - E / 2) / s ^ 3)) := by
    simpa using ((tendsto_const_nhds (x := K)).sub
      (((tendsto_const_nhds (x := E)).add hC).div_const 2)).div_const (s ^ 3)
  exact le_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun n hn => hpoint n (by omega)⟩)

end TranscendentalTuran.Green.Realization.TypedData
