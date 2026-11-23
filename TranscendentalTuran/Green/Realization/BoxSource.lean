/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxEnergy
public import TranscendentalTuran.Green.FiniteNetwork.BoxSourceGain
public import TranscendentalTuran.Construction.TypedPolynomial

@[expose] public section

noncomputable section

open scoped BigOperators Topology
open Filter

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters FiniteNetwork TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

theorem box_typeMass_eq_fiber {n : ℕ} (w : Vertex n → ℝ) (τ : PhysicalType) :
    RootData.typeMass type w τ = ∑ v : Fiber n τ, w ⟨τ, v⟩ := by
  classical
  unfold RootData.typeMass RootData.typedPartition Weighted.TypePartition.mass
  rw [Finset.sum_filter, sum_vertex]
  cases τ <;>
    simp [type, base, port01E, port01D, port23E, port23D, center13, center02,
      ownerH, ownerV, Fiber, Fintype.sum_sum_type] <;> rfl

/-- The finite full Green vector scaled to the desired source strength. -/
def scaledBoxBase (J : ℝ) (W : Fin 4 → ℝ) (n : ℕ) (v : Box n) : ℝ :=
  (J * totalResistance W) * (boxNetwork n).green (boxRoot n) v

/-- Actual nonnegative weights on every base, port, center, and owner. -/
def boxSourceWeight (J : ℝ) (W : Fin 4 → ℝ) (n : ℕ) : Vertex n → ℝ :=
  boxWeight (scaledBoxBase J W n) (resistanceInterpolation W)

theorem scaledBoxBase_nonneg {J : ℝ} {W : Fin 4 → ℝ}
    (hJ : 0 ≤ J) (hW : ∀ b, 0 < W b) (n : ℕ) (v : Box n) :
    0 ≤ scaledBoxBase J W n v :=
  (boxNetwork n).scaled_green_nonneg (boxRoot n) hJ (totalResistance_pos hW).le v

theorem boxSourceWeight_nonneg {J : ℝ} {W : Fin 4 → ℝ}
    (hJ : 0 ≤ J) (hW : ∀ b, 0 < W b) (n : ℕ) (v : Vertex n) :
    0 ≤ boxSourceWeight J W n v :=
  boxWeight_nonneg (scaledBoxBase_nonneg hJ hW n) (resistanceInterpolation_bounds hW) v

/-- Every one of the seven actual type masses fits the common `JR` budget. -/
theorem boxSource_typeMass_le {J : ℝ} {W : Fin 4 → ℝ}
    (hJ : 0 ≤ J) (hW : ∀ b, 0 < W b) (n : ℕ) (τ : PhysicalType) :
    RootData.typeMass (boxData n).type (boxSourceWeight J W n) τ ≤ J * totalResistance W := by
  rw [show (boxData n).type = type from rfl, box_typeMass_eq_fiber]
  change typeMass (scaledBoxBase J W n) (resistanceInterpolation W) τ ≤ _
  apply typeMass_le _ (scaledBoxBase_nonneg hJ hW n)
  exact (boxNetwork n).twice_scaled_green_mass_le (boxProjection n) hJ
    (totalResistance_pos hW).le

@[simp] theorem boxSource_mark (J : ℝ) (W : Fin 4 → ℝ) (n : ℕ) :
    boxSourceWeight J W n (boxData n).mark =
      (J * totalResistance W) * boxGreenValue n := rfl

/-- The actual layer energy of the ordinary source host, in the form consumed by
the exact template polynomial. -/
theorem boxSource_energy (J : ℝ) (z : Root → ℝ)
    (hW : ∀ b, 0 < matchingConductance z b) (n : ℕ) :
    (∑ r : Layer, z (layerRoot r) *
      (boxData n).layerEnergy r.1 (boxSourceWeight J (matchingConductance z) n)) =
      (boxNetwork n).energy (scaledBoxBase J (matchingConductance z) n) /
        totalResistance (matchingConductance z) := by
  have he := actualBoxEnergy_eq z (scaledBoxBase J (matchingConductance z) n) hW
  unfold actualBoxEnergy actualEnergy boxGraph at he
  simp_rw [(boxData n).actualLayerEnergy_eq_layerEnergy (boxGraph_rootedLegal n)] at he
  exact he

/-- The exact source gain of the ordinary finite box realization. -/
theorem boxSource_gain (J : ℝ) (z : Root → ℝ)
    (hW : ∀ b, 0 < matchingConductance z b) (n : ℕ) :
    J * boxSourceWeight J (matchingConductance z) n (boxData n).mark -
      (∑ r : Layer, z (layerRoot r) *
        (boxData n).layerEnergy r.1 (boxSourceWeight J (matchingConductance z) n)) / 2 =
      (J ^ 2 * totalResistance (matchingConductance z) / 2) * boxGreenValue n := by
  rw [boxSource_mark, boxSource_energy J z hW]
  have h := (boxNetwork n).scaled_green_gain (boxProjection n) J
    (totalResistance (matchingConductance z)) (totalResistance_pos hW).ne'
  unfold boxGreenValue scaledBoxBase
  convert h using 1 <;> ring

/-- Finite legal ordinary hosts approach the exact quadrant source coefficient. -/
theorem tendsto_boxSource_gain (J : ℝ) (z : Root → ℝ)
    (hW : ∀ b, 0 < matchingConductance z b) :
    Tendsto (fun n => J * boxSourceWeight J (matchingConductance z) n (boxData n).mark -
      (∑ r : Layer, z (layerRoot r) *
        (boxData n).layerEnergy r.1 (boxSourceWeight J (matchingConductance z) n)) / 2)
      atTop (𝓝 ((J ^ 2 * totalResistance (matchingConductance z) / 2) * cornerGreen)) := by
  have h := (tendsto_const_nhds (x := J ^ 2 * totalResistance (matchingConductance z) / 2)).mul
    tendsto_boxGreenValue
  exact Filter.Tendsto.congr (fun n => (boxSource_gain J z hW n).symm) h

theorem boxGreenValue_le_half (n : ℕ) : boxGreenValue n ≤ 1 / 2 := by
  have h : (boxNetwork n).green (boxRoot n) (boxRoot n) ≤
      ∑ v, (boxNetwork n).green (boxRoot n) v :=
    Finset.single_le_sum (fun v _ => boxGreen_nonneg n v) (Finset.mem_univ _)
  exact h.trans (boxGreen_mass_le_half n)

theorem cornerGreen_le_half : cornerGreen ≤ 1 / 2 :=
  le_of_tendsto tendsto_boxGreenValue (Eventually.of_forall boxGreenValue_le_half)

end TranscendentalTuran.Green.Realization
