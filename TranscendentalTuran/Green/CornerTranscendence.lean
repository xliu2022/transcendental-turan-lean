/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Constants
public import TranscendentalTuran.Green.CornerEvaluation
public import TranscendentalTuran.Green.Walks.GraphBridge

@[expose] public section

open scoped BigOperators

namespace TranscendentalTuran.Green

/-- Identification of the combinatorially defined Green value with the scalar used
in the finite rational optimization. -/
theorem cornerGreen_eq_value : cornerGreen = value := cornerGreen_eq

theorem cornerGreen_transcendental : Transcendental ℚ cornerGreen := by
  rw [cornerGreen_eq_value]
  exact value_transcendental

/-- The ordinary graph-walk formulation of the paper's Green evaluation. -/
theorem graphWalk_green_eq :
    (∑' k : ℕ,
      (Nat.card {w : Walks.quadrantGraph.Walk (0, 0) (0, 0) // w.length = k} : ℝ) /
        4 ^ (k + 1)) = value := by
  simp only [Walks.natCard_graphWalk]
  exact cornerGreen_eq_value

end TranscendentalTuran.Green
