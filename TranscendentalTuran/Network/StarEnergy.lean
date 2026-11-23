module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The signed-star square identity

Formalization author and responsible maintainer: Xizhi Liu.

A finite partial function from leaves to centers specifies actual stars and
unassigned singleton leaves. The formula below is proved by expanding finite
sums and includes every singleton square. No connectivity or energy identity
is assumed as an input.
-/

namespace TranscendentalTuran.Network.StarEnergy

open scoped BigOperators

variable {C B : Type*} [Fintype C] [Fintype B] [DecidableEq C]

def fiberMass (f : B → Option C) (y : B → ℝ) (c : C) : ℝ :=
  ∑ b, if f b = some c then y b else 0

def fiberSquareMass (f : B → Option C) (y : B → ℝ) (c : C) : ℝ :=
  ∑ b, if f b = some c then y b ^ 2 else 0

/-- The sum of products on unordered pairs of distinct leaves in one star. -/
noncomputable def fiberPairs (f : B → Option C) (y : B → ℝ) (c : C) : ℝ :=
  (fiberMass f y c ^ 2 - fiberSquareMass f y c) / 2

/-- A complete finite pair sum, written in the standard square formula. -/
noncomputable def completePairs {A : Type*} [Fintype A] (w : A → ℝ) : ℝ :=
  ((∑ a, w a) ^ 2 - ∑ a, w a ^ 2) / 2

def energy (f : B → Option C) (x : C → ℝ) (y : B → ℝ) : ℝ :=
  (∑ c, (x c - fiberMass f y c) ^ 2) +
    ∑ b, if f b = none then y b ^ 2 else 0

noncomputable def permittedPairWeight (f : B → Option C) (x : C → ℝ) (y : B → ℝ) : ℝ :=
  completePairs x + completePairs y - (∑ c, fiberPairs f y c) +
    ∑ c, x c * fiberMass f y c

theorem squares_partition (f : B → Option C) (y : B → ℝ) :
    (∑ c, fiberSquareMass f y c) +
      (∑ b, if f b = none then y b ^ 2 else 0) = ∑ b, y b ^ 2 := by
  unfold fiberSquareMass
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  cases hf : f b with
  | none => simp
  | some c => simp [eq_comm]

theorem energy_nonneg (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    0 ≤ energy f x y := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun c _ => sq_nonneg _
  · apply Finset.sum_nonneg
    intro b _
    split_ifs <;> first | exact sq_nonneg _ | exact le_rfl

theorem energy_expansion (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    energy f x y = (∑ c, x c ^ 2) + (∑ b, y b ^ 2) +
      2 * (∑ c, fiberPairs f y c) - 2 * (∑ c, x c * fiberMass f y c) := by
  have hfiber : (∑ c, fiberMass f y c ^ 2) =
      2 * (∑ c, fiberPairs f y c) + ∑ c, fiberSquareMass f y c := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    unfold fiberPairs
    ring
  have hexpand : (∑ c, (x c - fiberMass f y c) ^ 2) =
      (∑ c, x c ^ 2) + (∑ c, fiberMass f y c ^ 2) -
        2 * (∑ c, x c * fiberMass f y c) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hs := squares_partition f y
  unfold energy
  rw [hexpand, hfiber]
  linarith

/-- The exact factor one-half in the manuscript's signed-star identity. -/
theorem square_identity (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    permittedPairWeight f x y =
      ((∑ c, x c) ^ 2 + (∑ b, y b) ^ 2 - energy f x y) / 2 := by
  rw [energy_expansion]
  unfold permittedPairWeight completePairs
  ring

theorem unmatched_penalty (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    (∑ b, if f b = none then y b ^ 2 else 0) ≤ energy f x y := by
  have h : 0 ≤ ∑ c, (x c - fiberMass f y c) ^ 2 :=
    Finset.sum_nonneg fun c _ => sq_nonneg _
  unfold energy
  linarith

end TranscendentalTuran.Network.StarEnergy
