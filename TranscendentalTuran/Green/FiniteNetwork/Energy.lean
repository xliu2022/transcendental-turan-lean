module

public import TranscendentalTuran.Green.FiniteNetwork.Basic
public import TranscendentalTuran.Optimization.MatrixEnergy

@[expose] public section

/-!
# Energy of an actual finite directional network

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork

open Finset Matrix
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pairing (N : DirectionalNetwork V) (x y : V → ℝ) : ℝ :=
  ∑ v, x v * (N.laplacian *ᵥ y) v

noncomputable def energy (N : DirectionalNetwork V) (x : V → ℝ) : ℝ :=
  ∑ v, x v * (N.laplacian *ᵥ x) v

theorem energy_eq_pairing (N : DirectionalNetwork V) (x : V → ℝ) :
    N.energy x = N.pairing x x := rfl

theorem energy_identity (N : DirectionalNetwork V) (x : V → ℝ) :
    N.energy x = (1 / 2 : ℝ) *
      (∑ v, ∑ w, N.adjacency v w * (x v - x w) ^ 2) +
      ∑ v, (4 - ∑ w, N.adjacency v w) * x v ^ 2 :=
  Optimization.MatrixEnergy.laplacian_energy_identity 4 N.adjacency N.adjacency_symm x

theorem energy_nonneg (N : DirectionalNetwork V) (x : V → ℝ) : 0 ≤ N.energy x :=
  Optimization.MatrixEnergy.laplacian_energy_nonneg 4 N.adjacency
    N.adjacency_symm N.adjacency_nonneg N.row_sum_le_four x

theorem pairing_symm (N : DirectionalNetwork V) (x y : V → ℝ) :
    N.pairing x y = N.pairing y x :=
  Optimization.MatrixEnergy.pairing_symm _
    (Optimization.MatrixEnergy.laplacian_symm 4 N.adjacency N.adjacency_symm) x y

theorem pairing_sq_le_energy_mul (N : DirectionalNetwork V) (x y : V → ℝ) :
    N.pairing x y ^ 2 ≤ N.energy x * N.energy y :=
  Optimization.MatrixEnergy.laplacian_pairing_sq_le 4 N.adjacency
    N.adjacency_symm N.adjacency_nonneg N.row_sum_le_four x y

theorem energy_const_mul (N : DirectionalNetwork V) (c : ℝ) (x : V → ℝ) :
    N.energy (fun v => c * x v) = c ^ 2 * N.energy x :=
  Optimization.MatrixEnergy.energy_const_mul N.laplacian c x

theorem energy_add_smul (N : DirectionalNetwork V) (x y : V → ℝ) (c : ℝ) :
    N.energy (x + c • y) = N.energy x + 2 * c * N.pairing x y + c ^ 2 * N.energy y :=
  Optimization.MatrixEnergy.energy_line _
    (Optimization.MatrixEnergy.laplacian_symm 4 N.adjacency N.adjacency_symm) x y c

end TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork
