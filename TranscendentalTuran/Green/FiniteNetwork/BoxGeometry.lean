/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Kernel

@[expose] public section

namespace TranscendentalTuran.Green.FiniteNetwork

/-- The finite quadrant box `[0,N]²`. -/
abbrev Box (N : ℕ) := Fin (N + 1) × Fin (N + 1)

def boxCoord {N : ℕ} (v : Box N) : Walks.Point := (v.1.val, v.2.val)

def boxRoot (N : ℕ) : Box N := (0, 0)

def packBox (N : ℕ) (q : Walks.Point) (h : q.1 ≤ N ∧ q.2 ≤ N) : Box N :=
  (⟨q.1, Nat.lt_succ_iff.mpr h.1⟩, ⟨q.2, Nat.lt_succ_iff.mpr h.2⟩)

@[simp] theorem boxCoord_pack (N : ℕ) (q : Walks.Point) (h : q.1 ≤ N ∧ q.2 ≤ N) :
    boxCoord (packBox N q h) = q := by cases q; rfl

theorem boxCoord_injective (N : ℕ) : Function.Injective (@boxCoord N) := by
  intro v w h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

end TranscendentalTuran.Green.FiniteNetwork
