module

public import TranscendentalTuran.Network.StageMaps
public import TranscendentalTuran.Network.BaseNetwork
public import TranscendentalTuran.Green.FiniteNetwork.Energy

@[expose] public section

/-!
# The endpoint defects are the actual base Laplacian energy

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Green.FiniteNetwork
open scoped BigOperators Matrix
attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem base_neighbor_east (h : RootedLegal G μ) (x : BaseVertex G μ) :
    (baseNetwork h).neighbor x 0 = (eastIso h).forward x := by
  apply Option.ext
  intro y
  rw [baseNetwork_neighbor_iff h, eastIso_forward h]
  rfl

theorem base_neighbor_west (h : RootedLegal G μ) (x : BaseVertex G μ) :
    (baseNetwork h).neighbor x 1 = (eastIso h).backward x := by
  apply Option.ext
  intro y
  rw [baseNetwork_neighbor_iff h, ← (eastIso h).reverse y x, eastIso_forward h]
  rfl

theorem base_neighbor_up (h : RootedLegal G μ) (x : BaseVertex G μ) :
    (baseNetwork h).neighbor x 2 = (diagonalIso h).backward x := by
  apply Option.ext
  intro y
  rw [baseNetwork_neighbor_iff h, ← (diagonalIso h).reverse y x, diagonalIso_forward h]
  rfl

theorem base_neighbor_down (h : RootedLegal G μ) (x : BaseVertex G μ) :
    (baseNetwork h).neighbor x 3 = (diagonalIso h).forward x := by
  apply Option.ext
  intro y
  rw [baseNetwork_neighbor_iff h, diagonalIso_forward h]
  rfl

theorem baseNetwork_energy_eq_defects (h : RootedLegal G μ) (x : BaseVertex G μ → ℝ) :
    (baseNetwork h).energy x = (eastIso h).defect x x + (diagonalIso h).defect x x := by
  change Optimization.MatrixEnergy.energy
    (Optimization.MatrixEnergy.laplacian 4 (baseNetwork h).adjacency) x = _
  rw [Optimization.MatrixEnergy.laplacian_energy_eq]
  simp only [DirectionalNetwork.adjacency_mulVec, Fin.sum_univ_four,
    base_neighbor_east h, base_neighbor_west h, base_neighbor_up h, base_neighbor_down h,
    mul_add, Finset.sum_add_distrib]
  change 4 * PartialIso.normSq x -
      (PartialIso.dot x ((eastIso h).push x) + PartialIso.dot x ((eastIso h).pull x) +
        PartialIso.dot x ((diagonalIso h).pull x) + PartialIso.dot x ((diagonalIso h).push x)) = _
  have hE : PartialIso.dot x ((eastIso h).pull x) = PartialIso.dot x ((eastIso h).push x) :=
    (PartialIso.dot_comm _ _).trans ((eastIso h).dot_push x x).symm
  have hD : PartialIso.dot x ((diagonalIso h).pull x) = PartialIso.dot x ((diagonalIso h).push x) :=
    (PartialIso.dot_comm _ _).trans ((diagonalIso h).dot_push x x).symm
  rw [hE, hD]
  unfold PartialIso.defect
  ring

end TranscendentalTuran.Source
