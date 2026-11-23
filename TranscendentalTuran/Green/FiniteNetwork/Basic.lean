/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Occupation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace TranscendentalTuran.Green.FiniteNetwork

/-- Opposite ports: `0↔1` for horizontal moves, `2↔3` for diagonal moves. -/
def reverseDirection (d : Fin 4) : Fin 4 :=
  match d.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

@[simp] theorem reverseDirection_involutive (d : Fin 4) :
    reverseDirection (reverseDirection d) = d := by
  fin_cases d <;> rfl

/-- A finite host has one possible neighbor at each of its four ports.  The two ends
of an occupied port carry opposite directions.  An absent neighbor is grounded. -/
structure DirectionalNetwork (V : Type*) where
  neighbor : V → Fin 4 → Option V
  reverse_step : ∀ (v w : V) (d : Fin 4),
    neighbor v d = some w ↔ neighbor w (reverseDirection d) = some v

/-- A coordinate projection preserves every occupied port and sends the mark to the
quadrant corner.  No injectivity of the vertex map is assumed. -/
structure Projection {V : Type*} (N : DirectionalNetwork V) (o : V) where
  coord : V → Walks.Point
  root : coord o = (0, 0)
  step : ∀ (v w : V) (d : Fin 4), N.neighbor v d = some w →
    Walks.predecessor (coord v) d = some (coord w)

namespace DirectionalNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency entry counts occupied ports from `v` to `w`. -/
def adjacency (N : DirectionalNetwork V) : Matrix V V ℝ :=
  fun v w => ∑ d : Fin 4, if N.neighbor v d = some w then 1 else 0

/-- The substochastic transition matrix, one quarter for each occupied port. -/
def transitionMatrix (N : DirectionalNetwork V) : Matrix V V ℝ :=
  (1 / 4 : ℝ) • N.adjacency

/-- The finite grounded Laplacian. -/
def laplacian (N : DirectionalNetwork V) : Matrix V V ℝ :=
  (4 : ℝ) • (1 : Matrix V V ℝ) - N.adjacency

theorem adjacency_nonneg (N : DirectionalNetwork V) (v w : V) : 0 ≤ N.adjacency v w := by
  unfold adjacency
  exact Finset.sum_nonneg fun d _ => by split_ifs <;> norm_num

theorem adjacency_symm (N : DirectionalNetwork V) (v w : V) :
    N.adjacency v w = N.adjacency w v := by
  unfold adjacency
  apply Fintype.sum_equiv
    ({ toFun := reverseDirection, invFun := reverseDirection,
       left_inv := reverseDirection_involutive,
       right_inv := reverseDirection_involutive } : Fin 4 ≃ Fin 4)
  intro d
  change (if N.neighbor v d = some w then (1 : ℝ) else 0) =
    if N.neighbor w (reverseDirection d) = some v then 1 else 0
  simp only [N.reverse_step v w d]

theorem adjacency_mulVec (N : DirectionalNetwork V) (f : V → ℝ) (v : V) :
    (N.adjacency *ᵥ f) v = ∑ d : Fin 4, (N.neighbor v d).elim 0 f := by
  unfold Matrix.mulVec dotProduct adjacency
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  cases h : N.neighbor v d with
  | none => simp [h]
  | some w => simp [h, eq_comm]

theorem transition_mulVec (N : DirectionalNetwork V) (f : V → ℝ) (v : V) :
    (N.transitionMatrix *ᵥ f) v =
      (1 / 4 : ℝ) * ∑ d : Fin 4, (N.neighbor v d).elim 0 f := by
  simp only [transitionMatrix, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    N.adjacency_mulVec]

theorem row_sum_le_four (N : DirectionalNetwork V) (v : V) :
    (∑ w, N.adjacency v w) ≤ 4 := by
  have h := N.adjacency_mulVec (fun _ => (1 : ℝ)) v
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [h]
  calc
    _ ≤ ∑ _d : Fin 4, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      cases h : N.neighbor v d <;> norm_num
    _ = 4 := by norm_num

theorem transition_nonneg (N : DirectionalNetwork V) (v w : V) :
    0 ≤ N.transitionMatrix v w :=
  mul_nonneg (by norm_num) (N.adjacency_nonneg v w)

theorem transition_symm (N : DirectionalNetwork V) (v w : V) :
    N.transitionMatrix v w = N.transitionMatrix w v := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul, N.adjacency_symm v w]

theorem transition_mulVec_nonneg (N : DirectionalNetwork V) {f : V → ℝ}
    (hf : ∀ v, 0 ≤ f v) (v : V) : 0 ≤ (N.transitionMatrix *ᵥ f) v := by
  unfold Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun w _ => mul_nonneg (N.transition_nonneg v w) (hf w)

theorem transition_mulVec_mono (N : DirectionalNetwork V) {f g : V → ℝ}
    (hfg : ∀ v, f v ≤ g v) (v : V) :
    (N.transitionMatrix *ᵥ f) v ≤ (N.transitionMatrix *ᵥ g) v := by
  unfold Matrix.mulVec dotProduct
  exact Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_left (hfg w) (N.transition_nonneg v w)

/-- A coordinate projection intertwines occupied steps; missing host ports can only
remove nonnegative mass. -/
theorem transition_project_le (N : DirectionalNetwork V) {o : V} (φ : Projection N o)
    {f : Walks.Point → ℝ} (hf : ∀ p, 0 ≤ f p) (v : V) :
    (N.transitionMatrix *ᵥ (fun w => f (φ.coord w))) v ≤
      Walks.transition f (φ.coord v) := by
  rw [N.transition_mulVec]
  unfold Walks.transition
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro d _
  cases h : N.neighbor v d with
  | none =>
      simp only [Option.elim_none]
      cases hq : Walks.predecessor (φ.coord v) d with
      | none => simp
      | some q => exact hf q
  | some w =>
      rw [φ.step v w d h]
      rfl

end DirectionalNetwork
end TranscendentalTuran.Green.FiniteNetwork
