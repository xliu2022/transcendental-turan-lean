/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxBlockEnergy
public import TranscendentalTuran.Green.Realization.BoxChainEnergy
public import TranscendentalTuran.Green.Realization.BoxLegal

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open Network Encoding Parameters FiniteNetwork TuranUniversality Source

attribute [local irreducible] Parameters.q Parameters.N Parameters.M Parameters.κ
set_option compiler.extract_closed false
set_option maxRecDepth 4000

def eColorSquare {n : ℕ} (b : Fin 4) (w : Vertex n → ℝ) (e : EAnchor n) : ℝ :=
  match b.val with
  | 0 => (pushWeight (eStart n) (fun v => w (base v)) e - w (port01E e)) ^ 2
  | 1 => (w (center13 e) - w (port01E e)) ^ 2
  | 2 => (pushWeight (eEnd n) (fun v => w (base v)) e - w (port23E e)) ^ 2
  | _ => (w (center13 e) - w (port23E e)) ^ 2

def dColorSquare {n : ℕ} (b : Fin 4) (w : Vertex n → ℝ) (e : DAnchor n) : ℝ :=
  match b.val with
  | 0 => (w (center02 e) - w (port01D e)) ^ 2
  | 1 => (pushWeight (dStart n) (fun v => w (base v)) e - w (port01D e)) ^ 2
  | 2 => (w (center02 e) - w (port23D e)) ^ 2
  | _ => (pushWeight (dEnd n) (fun v => w (base v)) e - w (port23D e)) ^ 2

theorem blockChainEnergy_eq_colors {n : ℕ} (b : Fin 4) (w : Vertex n → ℝ) :
    blockChainEnergy b w = (∑ e, eColorSquare b w e) + ∑ e, dColorSquare b w e := by
  fin_cases b <;> rfl

theorem eColor_resistance_sum {n : ℕ} (W : Fin 4 → ℝ) (X : Box n → ℝ) (e : EAnchor n) :
    (∑ b, W b * eColorSquare b (boxWeight X (resistanceInterpolation W)) e) =
      eChainEnergy W (pushWeight (eStart n) X e) (pushWeight (eEnd n) X e) := by
  simp [Fin.sum_univ_succ, eColorSquare, boxWeight, base, port01E, port23E, center13,
    eChainEnergy]
  ring

theorem dColor_resistance_sum {n : ℕ} (W : Fin 4 → ℝ) (X : Box n → ℝ) (e : DAnchor n) :
    (∑ b, W b * dColorSquare b (boxWeight X (resistanceInterpolation W)) e) =
      dChainEnergy W (pushWeight (dStart n) X e) (pushWeight (dEnd n) X e) := by
  simp [Fin.sum_univ_succ, dColorSquare, boxWeight, base, port01D, port23D, center02,
    dChainEnergy]
  ring

theorem weighted_blockChainEnergy_eq {n : ℕ} (W : Fin 4 → ℝ) (X : Box n → ℝ) :
    (∑ b, W b * blockChainEnergy b (boxWeight X (resistanceInterpolation W))) =
      chainEnergy W X := by
  simp_rw [blockChainEnergy_eq_colors, mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  unfold chainEnergy
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => eColor_resistance_sum W X e)
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => dColor_resistance_sum W X e)

/-- The total conductance of one matching repetition block. -/
def matchingConductance (z : Root → ℝ) (b : Fin 4) : ℝ :=
  ∑ j : Fin M, z (matchingRoot b j)

private theorem sum_block (f : Block → ℝ) :
    (∑ b, f b) = f .match0 + f .match1 + f .match2 + f .match3 + f .ownerH + f .ownerV := by
  change (∑ b ∈ ({.match0, .match1, .match2, .match3, .ownerH, .ownerV} : Finset Block), f b) = _
  simp
  ring

/-- The actual individual-layer energy of the ordinary box graph. -/
def actualBoxEnergy {n : ℕ} (z : Root → ℝ) (X : Box n → ℝ) (θ : Interpolation) : ℝ :=
  actualEnergy (G := boxGraph n) (μ := sumRooting (Vertex n)) z
    (Sum.elim (fun _ : Root => 0) (boxWeight X θ))

theorem actualBoxEnergy_eq_blocks {n : ℕ} (z : Root → ℝ) (X : Box n → ℝ) (θ : Interpolation) :
    actualBoxEnergy z X θ = ∑ b, matchingConductance z b * blockChainEnergy b (boxWeight X θ) := by
  unfold actualBoxEnergy actualEnergy boxGraph
  simp_rw [(boxData n).actualLayerEnergy_eq_layerEnergy (boxGraph_rootedLegal n)]
  rw [Fintype.sum_sigma]
  simp_rw [← Finset.sum_mul]
  rw [sum_block]
  rw [box_ownerH_layerEnergy, box_ownerV_layerEnergy]
  have h0 : (boxData n).layerEnergy .match0 (boxWeight X θ) =
      blockChainEnergy 0 (boxWeight X θ) := box_matching_layerEnergy 0 (boxWeight X θ)
  have h1 : (boxData n).layerEnergy .match1 (boxWeight X θ) =
      blockChainEnergy 1 (boxWeight X θ) := box_matching_layerEnergy 1 (boxWeight X θ)
  have h2 : (boxData n).layerEnergy .match2 (boxWeight X θ) =
      blockChainEnergy 2 (boxWeight X θ) := box_matching_layerEnergy 2 (boxWeight X θ)
  have h3 : (boxData n).layerEnergy .match3 (boxWeight X θ) =
      blockChainEnergy 3 (boxWeight X θ) := box_matching_layerEnergy 3 (boxWeight X θ)
  rw [h0, h1, h2, h3]
  simp only [mul_zero, add_zero]
  rw [Fin.sum_univ_four]
  rfl

/-- The exact lower-host energy equals the finite-box grounded energy divided by
the four-color series resistance; every ownership contribution vanishes. -/
theorem actualBoxEnergy_eq {n : ℕ} (z : Root → ℝ) (X : Box n → ℝ)
    (hW : ∀ b, 0 < matchingConductance z b) :
    actualBoxEnergy z X (resistanceInterpolation (matchingConductance z)) =
      (boxNetwork n).energy X / totalResistance (matchingConductance z) := by
  rw [actualBoxEnergy_eq_blocks, weighted_blockChainEnergy_eq, chainEnergy_eq_box_energy hW]

end TranscendentalTuran.Green.Realization
