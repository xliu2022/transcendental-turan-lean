module

public import TranscendentalTuran.Green.FiniteNetwork.Energy

@[expose] public section

/-!
# Nonnegative energy contributions of individual ports

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork

open Finset Matrix
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each occupied edge is counted by halves at its two ports. A missing
port contributes the full grounded square. -/
noncomputable def portEnergy (N : DirectionalNetwork V) (x : V → ℝ)
    (v : V) (d : Fin 4) : ℝ :=
  match N.neighbor v d with
  | none => x v ^ 2
  | some w => (x v - x w) ^ 2 / 2

theorem portEnergy_nonneg (N : DirectionalNetwork V) (x : V → ℝ) (v : V) (d : Fin 4) :
    0 ≤ N.portEnergy x v d := by
  unfold portEnergy
  split
  · exact sq_nonneg _
  · exact div_nonneg (sq_nonneg _) (by norm_num)

theorem energy_eq_sum_portEnergy (N : DirectionalNetwork V) (x : V → ℝ) :
    N.energy x = ∑ v, ∑ d : Fin 4, N.portEnergy x v d := by
  have hdiff (v : V) : (∑ w, N.adjacency v w * (x v - x w) ^ 2) =
      ∑ d : Fin 4, (N.neighbor v d).elim 0 (fun w => (x v - x w) ^ 2) :=
    N.adjacency_mulVec (fun w => (x v - x w) ^ 2) v
  have hrow (v : V) : (∑ w, N.adjacency v w) =
      ∑ d : Fin 4, (N.neighbor v d).elim (0 : ℝ) (fun _ => 1) := by
    simpa only [Matrix.mulVec, dotProduct, mul_one] using N.adjacency_mulVec (fun _ => 1) v
  have hport (v : V) : (∑ d : Fin 4, N.portEnergy x v d) =
      (1 / 2 : ℝ) * (∑ d : Fin 4, (N.neighbor v d).elim 0 (fun w => (x v - x w) ^ 2)) +
      (4 - ∑ d : Fin 4, (N.neighbor v d).elim (0 : ℝ) (fun _ => 1)) * x v ^ 2 := by
    have he (d : Fin 4) : N.portEnergy x v d =
        (1 / 2 : ℝ) * (N.neighbor v d).elim 0 (fun w => (x v - x w) ^ 2) +
          (1 - (N.neighbor v d).elim (0 : ℝ) (fun _ => 1)) * x v ^ 2 := by
      cases hn : N.neighbor v d <;> simp [portEnergy, hn] <;> ring
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  rw [N.energy_identity]
  simp_rw [hdiff, hrow]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => (hport v).symm)

end TranscendentalTuran.Green.FiniteNetwork.DirectionalNetwork
