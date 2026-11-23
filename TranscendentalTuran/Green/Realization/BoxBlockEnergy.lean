/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.ActualMatchingEnergy
public import TranscendentalTuran.Green.Realization.BoxSums
public import TranscendentalTuran.Green.Realization.BoxWeights

@[expose] public section

noncomputable section

open scoped BigOperators

namespace TranscendentalTuran.Green.Realization

open Network Encoding FiniteNetwork

private theorem sum_difference_sq {A : Type*} [Fintype A] (f g : A → ℝ) :
    (∑ a, (f a - g a) ^ 2) = (∑ a, f a ^ 2) + (∑ a, g a ^ 2) - 2 * ∑ a, f a * g a := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual squares on the two chain positions of a matching color. -/
def blockChainEnergy {n : ℕ} (b : Fin 4) (w : Vertex n → ℝ) : ℝ :=
  let X := fun v => w (base v)
  match b.val with
  | 0 => (∑ e, (pushWeight (eStart n) X e - w (port01E e)) ^ 2) +
      ∑ e, (w (center02 e) - w (port01D e)) ^ 2
  | 1 => (∑ e, (w (center13 e) - w (port01E e)) ^ 2) +
      ∑ e, (pushWeight (dStart n) X e - w (port01D e)) ^ 2
  | 2 => (∑ e, (pushWeight (eEnd n) X e - w (port23E e)) ^ 2) +
      ∑ e, (w (center02 e) - w (port23D e)) ^ 2
  | _ => (∑ e, (w (center13 e) - w (port23E e)) ^ 2) +
      ∑ e, (pushWeight (dEnd n) X e - w (port23D e)) ^ 2

/-- Every finite-box matching layer has exactly the full-chain square sum, with
terminal singleton squares included by zero extension of the missing endpoints. -/
theorem box_matching_layerEnergy {n : ℕ} (b : Fin 4) (w : Vertex n → ℝ) :
    (boxData n).layerEnergy (matchingBlock b) w = blockChainEnergy b w := by
  rw [(boxData n).matching_layerEnergy_expansion (boxData_legal n)]
  rw [sum_vertex, sum_vertex]
  fin_cases b
  all_goals
    dsimp [matchingBlock, boxData, blockChainEnergy]
    simp only [type, Active, sign, center, base, port01E, port01D, port23E, port23D,
      center13, center02, ownerH, ownerV, ne_eq,
      not_false_eq_true, not_true_eq_false, ↓reduceIte, Option.elim_none, Option.elim_some,
      Finset.sum_const_zero, zero_add, add_zero, center_map_base_product,
      sum_difference_sq, sum_pushWeight_sq]
    norm_num
    ring

/-- Row owners have exactly the sum of their base leaves, so their signed mass is zero. -/
theorem box_ownerH_layerEnergy {n : ℕ} (X : Box n → ℝ) (θ : Interpolation) :
    (boxData n).layerEnergy .ownerH (boxWeight X θ) = 0 := by
  unfold TypedData.layerEnergy
  conv_lhs =>
    arg 1
    rw [sum_vertex]
  conv_lhs =>
    arg 2
    rw [sum_vertex]
  simp only [boxData, type, sign, center, base, port01E, port01D, port23E, port23D,
    center13, center02, ownerH, ownerV, ↓reduceIte,
    Option.some_ne_none, and_false, false_and, Finset.sum_const_zero, add_zero, zero_add]
  norm_num
  apply Finset.sum_eq_zero
  intro i _
  change (boxWeight X θ (ownerH i) -
    ∑ l : Vertex n, if center n .ownerH l = some (ownerH i) then boxWeight X θ l else 0) ^ 2 = 0
  rw [ownerH_fiberMass]
  change ((∑ j, X (i, j)) - (∑ j, X (i, j))) ^ 2 = 0
  simp

/-- Column owners have exactly the sum of their base leaves. -/
theorem box_ownerV_layerEnergy {n : ℕ} (X : Box n → ℝ) (θ : Interpolation) :
    (boxData n).layerEnergy .ownerV (boxWeight X θ) = 0 := by
  unfold TypedData.layerEnergy
  conv_lhs =>
    arg 1
    rw [sum_vertex]
  conv_lhs =>
    arg 2
    rw [sum_vertex]
  simp only [boxData, type, sign, center, base, port01E, port01D, port23E, port23D,
    center13, center02, ownerH, ownerV, ↓reduceIte,
    Option.some_ne_none, and_false, false_and, Finset.sum_const_zero, add_zero, zero_add]
  norm_num
  apply Finset.sum_eq_zero
  intro j _
  change (boxWeight X θ (ownerV j) -
    ∑ l : Vertex n, if center n .ownerV l = some (ownerV j) then boxWeight X θ l else 0) ^ 2 = 0
  rw [ownerV_fiberMass]
  change ((∑ i, X (i, j)) - (∑ i, X (i, j))) ^ 2 = 0
  simp

end TranscendentalTuran.Green.Realization
