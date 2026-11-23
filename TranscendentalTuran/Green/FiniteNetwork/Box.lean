/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.FiniteNetwork.Kernel
public import TranscendentalTuran.Green.FiniteNetwork.BoxGeometry
public import TranscendentalTuran.Green.Walks.KernelBounds

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace TranscendentalTuran.Green.FiniteNetwork

/-- The quadrant transition has the advertised inverse direction on every occupied port. -/
theorem quadrant_reverse_step (p q : Walks.Point) (d : Fin 4) :
    Walks.predecessor p d = some q ↔
      Walks.predecessor q (reverseDirection d) = some p := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  fin_cases d <;>
    simp [Walks.predecessor, reverseDirection, Prod.mk.injEq] <;>
    omega

/-- The induced finite-box ports; an edge leaving the box is grounded. -/
def boxNeighbor (N : ℕ) (v : Box N) (d : Fin 4) : Option (Box N) :=
  (Walks.predecessor (boxCoord v) d).bind fun q =>
    if h : q.1 ≤ N ∧ q.2 ≤ N then some (packBox N q h) else none

theorem boxNeighbor_some_iff (N : ℕ) (v w : Box N) (d : Fin 4) :
    boxNeighbor N v d = some w ↔ Walks.predecessor (boxCoord v) d = some (boxCoord w) := by
  cases hp : Walks.predecessor (boxCoord v) d with
  | none => simp [boxNeighbor, hp]
  | some q =>
      by_cases hq : q.1 ≤ N ∧ q.2 ≤ N
      · simp only [boxNeighbor, hp, Option.bind_some, dite_eq_left hq, Option.some.injEq]
        constructor
        · intro h
          simpa using congrArg boxCoord h
        · intro h
          apply boxCoord_injective N
          simpa using h
      · constructor
        · intro h
          simp [boxNeighbor, hp, hq] at h
        · intro h
          have heq : q = boxCoord w := Option.some.inj h
          have hw : (boxCoord w).1 ≤ N ∧ (boxCoord w).2 ≤ N :=
            ⟨Nat.le_of_lt_succ w.1.isLt, Nat.le_of_lt_succ w.2.isLt⟩
          exact (hq (heq.symm ▸ hw)).elim

/-- The finite box is a genuine four-port network. -/
def boxNetwork (N : ℕ) : DirectionalNetwork (Box N) where
  neighbor := boxNeighbor N
  reverse_step v w d := by
    rw [boxNeighbor_some_iff, quadrant_reverse_step, ← boxNeighbor_some_iff]

/-- Its coordinate projection is the literal inclusion into the infinite quadrant. -/
def boxProjection (N : ℕ) : Projection (boxNetwork N) (boxRoot N) where
  coord := boxCoord
  root := rfl
  step v w d h := (boxNeighbor_some_iff N v w d).mp h

/-- Walks of length at most `N` from the corner never use a removed box edge. -/
theorem box_kernel_eq_quadrant {N k : ℕ} (hk : k ≤ N) (v : Box N) :
    (boxNetwork N).kernel (boxRoot N) k v = Walks.kernelProbability k (boxCoord v) := by
  induction k generalizing v with
  | zero =>
      rw [DirectionalNetwork.kernel_zero, Walks.kernelProbability_zero]
      by_cases hv : v = boxRoot N
      · simp [hv, boxRoot, boxCoord]
      · have hc : boxCoord v ≠ (0, 0) := by
          intro h
          apply hv
          apply boxCoord_injective N
          exact h
        simp [hv, hc]
  | succ k ih =>
      have hk' : k ≤ N := by omega
      rw [DirectionalNetwork.kernel_succ, Walks.kernelProbability_succ,
        DirectionalNetwork.transition_mulVec]
      unfold Walks.transition
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      cases hp : Walks.predecessor (boxCoord v) d with
      | none => simp [boxNetwork, boxNeighbor, hp]
      | some q =>
          by_cases hq : q.1 ≤ N ∧ q.2 ≤ N
          · let w := packBox N q hq
            have hn : (boxNetwork N).neighbor v d = some w := by
              simp [boxNetwork, boxNeighbor, hp, hq, w]
            rw [hn]
            simp only [Option.elim_some]
            rw [ih hk' w]
            simp [w]
          · have hn : (boxNetwork N).neighbor v d = none := by
              simp [boxNetwork, boxNeighbor, hp, hq]
            rw [hn]
            simp only [Option.elim_none, Option.elim_some]
            have hc : Walks.count k q = 0 := by
              by_cases hi : q.1 ≤ N
              · have hj : N < q.2 := by omega
                exact Walks.count_eq_zero_of_lt_second k q.1 q.2 (by omega)
              · exact Walks.count_eq_zero_of_lt_first k q.1 q.2 (by omega)
            simp [Walks.kernelProbability, hc]

end TranscendentalTuran.Green.FiniteNetwork
