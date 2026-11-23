/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.PushWeight
public import TranscendentalTuran.Green.Realization.ResistanceWeights
public import TranscendentalTuran.Green.FiniteNetwork.Box
public import TranscendentalTuran.Green.FiniteNetwork.Energy

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace TranscendentalTuran.Green.Realization

open Network FiniteNetwork

@[simp] theorem box_neighbor_E {n : ℕ} (v : Box n) :
    (boxNetwork n).neighbor v 0 = partialInverse (eEnd n) (eStart n v) := by
  apply Option.ext
  intro w
  rw [show (boxNetwork n).neighbor v 0 = boxNeighbor n v 0 from rfl,
    boxNeighbor_some_iff, partialInverse_some_iff]
  simp [Walks.predecessor, boxCoord, eStart, eEnd, Prod.mk.injEq, Fin.ext_iff]
  omega

@[simp] theorem box_neighbor_W {n : ℕ} (v : Box n) :
    (boxNetwork n).neighbor v 1 = partialInverse (eStart n) (eEnd n v) := by
  apply Option.ext
  intro w
  rw [show (boxNetwork n).neighbor v 1 = boxNeighbor n v 1 from rfl,
    boxNeighbor_some_iff, partialInverse_some_iff]
  change (if v.1.val = 0 then none else some (v.1.val - 1, v.2.val)) =
    some (w.1.val, w.2.val) ↔ (w.1.succ, w.2) = (v.1.castSucc, v.2)
  by_cases hv : v.1.val = 0
  · rw [if_pos hv]
    simp only [reduceCtorEq, false_iff, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  · rw [if_neg hv]
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega

@[simp] theorem box_neighbor_U {n : ℕ} (v : Box n) :
    (boxNetwork n).neighbor v 2 = partialInverse (dStart n) (dEnd n v) := by
  apply Option.ext
  intro w
  rw [show (boxNetwork n).neighbor v 2 = boxNeighbor n v 2 from rfl,
    boxNeighbor_some_iff, partialInverse_some_iff]
  change (if v.1.val = 0 then none else some (v.1.val - 1, v.2.val + 1)) =
    some (w.1.val, w.2.val) ↔ (w.1.succ, w.2.castSucc) = (v.1.castSucc, v.2.succ)
  by_cases hv : v.1.val = 0
  · rw [if_pos hv]
    simp only [reduceCtorEq, false_iff, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  · rw [if_neg hv]
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega

@[simp] theorem box_neighbor_D {n : ℕ} (v : Box n) :
    (boxNetwork n).neighbor v 3 = partialInverse (dEnd n) (dStart n v) := by
  apply Option.ext
  intro w
  rw [show (boxNetwork n).neighbor v 3 = boxNeighbor n v 3 from rfl,
    boxNeighbor_some_iff, partialInverse_some_iff]
  change (if v.2.val = 0 then none else some (v.1.val + 1, v.2.val - 1)) =
    some (w.1.val, w.2.val) ↔ (w.1.castSucc, w.2.succ) = (v.1.succ, v.2.castSucc)
  by_cases hv : v.2.val = 0
  · rw [if_pos hv]
    simp only [reduceCtorEq, false_iff, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  · rw [if_neg hv]
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega

def eCross {n : ℕ} (X : Box n → ℝ) : ℝ :=
  ∑ e, pushWeight (eStart n) X e * pushWeight (eEnd n) X e

def dCross {n : ℕ} (X : Box n → ℝ) : ℝ :=
  ∑ e, pushWeight (dStart n) X e * pushWeight (dEnd n) X e

private theorem forward_cross {A B : Type*} [Fintype A] [Fintype B]
    (e f : A ↪ B) (X : A → ℝ) :
    (∑ v, X v * pushWeight f X (e v)) = ∑ a, pushWeight e X a * pushWeight f X a :=
  (sum_pushWeight_mul e X (pushWeight f X)).symm

private theorem backward_cross {A B : Type*} [Fintype A] [Fintype B]
    (e f : A ↪ B) (X : A → ℝ) :
    (∑ v, X v * pushWeight e X (f v)) = ∑ a, pushWeight e X a * pushWeight f X a := by
  rw [← sum_pushWeight_mul f X (pushWeight e X)]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The finite-box Laplacian sees the four actual neighboring endpoint weights. -/
theorem box_laplacian_mulVec {n : ℕ} (X : Box n → ℝ) (v : Box n) :
    ((boxNetwork n).laplacian *ᵥ X) v = 4 * X v -
      (pushWeight (eEnd n) X (eStart n v) + pushWeight (eStart n) X (eEnd n v) +
        pushWeight (dStart n) X (dEnd n v) + pushWeight (dEnd n) X (dStart n v)) := by
  rw [DirectionalNetwork.laplacian, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [DirectionalNetwork.adjacency_mulVec]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 4 * X v -
    (((boxNetwork n).neighbor v 0).elim 0 X +
      (((boxNetwork n).neighbor v 1).elim 0 X +
        (((boxNetwork n).neighbor v 2).elim 0 X + ((boxNetwork n).neighbor v 3).elim 0 X))) = _
  rw [box_neighbor_E, box_neighbor_W, box_neighbor_U, box_neighbor_D]
  change 4 * X v -
    (pushWeight (eEnd n) X (eStart n v) + (pushWeight (eStart n) X (eEnd n v) +
      (pushWeight (dStart n) X (dEnd n v) + pushWeight (dEnd n) X (dStart n v)))) = _
  ring

/-- The square expansion counts both orientations of each occupied logical edge. -/
theorem box_energy_expansion {n : ℕ} (X : Box n → ℝ) :
    (boxNetwork n).energy X = 4 * (∑ v, X v ^ 2) - 2 * eCross X - 2 * dCross X := by
  calc
    _ = 4 * (∑ v, X v ^ 2) -
        (∑ v, X v * pushWeight (eEnd n) X (eStart n v)) -
        (∑ v, X v * pushWeight (eStart n) X (eEnd n v)) -
        (∑ v, X v * pushWeight (dStart n) X (dEnd n v)) -
        (∑ v, X v * pushWeight (dEnd n) X (dStart n v)) := by
      unfold DirectionalNetwork.energy
      simp_rw [box_laplacian_mulVec]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      rw [forward_cross, backward_cross, backward_cross, forward_cross]
      change 4 * (∑ v, X v ^ 2) - eCross X - eCross X - dCross X - dCross X = _
      ring

/-- The sum of all full-chain endpoint squares is exactly the grounded box energy;
boundary chains supply the missing-port squares. -/
theorem endpoint_squares_eq_box_energy {n : ℕ} (X : Box n → ℝ) :
    (∑ e, (pushWeight (eStart n) X e - pushWeight (eEnd n) X e) ^ 2) +
      (∑ e, (pushWeight (dStart n) X e - pushWeight (dEnd n) X e) ^ 2) =
      (boxNetwork n).energy X := by
  rw [sum_endpoint_squares, sum_endpoint_squares, box_energy_expansion]
  unfold eCross dCross
  ring

/-- The actual sum of the four resistor squares on every private chain. -/
def chainEnergy {n : ℕ} (W : Fin 4 → ℝ) (X : Box n → ℝ) : ℝ :=
  (∑ e, eChainEnergy W (pushWeight (eStart n) X e) (pushWeight (eEnd n) X e)) +
    ∑ e, dChainEnergy W (pushWeight (dStart n) X e) (pushWeight (dEnd n) X e)

theorem chainEnergy_eq_box_energy {n : ℕ} {W : Fin 4 → ℝ}
    (hW : ∀ b, 0 < W b) (X : Box n → ℝ) :
    chainEnergy W X = (boxNetwork n).energy X / totalResistance W := by
  unfold chainEnergy
  simp_rw [eChainEnergy_eq hW, dChainEnergy_eq hW]
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, endpoint_squares_eq_box_energy]

end TranscendentalTuran.Green.Realization
