/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Kernel
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace TranscendentalTuran.Green.Walks

/-- The killed four-direction transition operator on functions on the quadrant. -/
def transition (f : Point → ℝ) (p : Point) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Fin 4, (predecessor p d).elim 0 f

theorem transition_nonneg {f : Point → ℝ} (hf : ∀ p, 0 ≤ f p) (p : Point) :
    0 ≤ transition f p := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro d _
  cases h : predecessor p d with
  | none => simp
  | some q => exact hf q

theorem transition_mono {f g : Point → ℝ} (hfg : ∀ p, f p ≤ g p) (p : Point) :
    transition f p ≤ transition g p := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro d _
  cases h : predecessor p d with
  | none => simp
  | some q => exact hfg q

theorem transition_const_mul (c : ℝ) (f : Point → ℝ) (p : Point) :
    transition (fun q => c * f q) p = c * transition f p := by
  unfold transition
  have h : ∀ d : Fin 4,
      (predecessor p d).elim 0 (fun q => c * f q) = c * (predecessor p d).elim 0 f := by
    intro d
    cases h : predecessor p d <;> simp
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

theorem transition_sum {ι : Type*} (s : Finset ι) (f : ι → Point → ℝ) (p : Point) :
    transition (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, transition (f i) p := by
  unfold transition
  have h : ∀ d : Fin 4,
      (predecessor p d).elim 0 (fun q => ∑ i ∈ s, f i q) =
        ∑ i ∈ s, (predecessor p d).elim 0 (f i) := by
    intro d
    cases h : predecessor p d <;> simp
  simp_rw [h]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The positive Lyapunov potential used in the paper. -/
def potential (p : Point) : ℝ := ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)

theorem potential_pos (p : Point) : 0 < potential p := by
  unfold potential
  positivity

@[simp] theorem potential_corner : potential (0, 0) = 1 := by norm_num [potential]

/-- The exact drift identity includes both killed boundary directions. -/
theorem transition_potential (p : Point) : transition potential p = potential p - 1 / 2 := by
  rcases p with ⟨i, j⟩
  cases i <;> cases j <;>
    simp [transition, predecessor, potential, Fin.sum_univ_succ, Nat.cast_add] <;> ring

/-- Survival mass of a length-`n` killed walk from `p`.  Each of four attempted
steps has weight `1/4`; a missing step contributes zero. -/
def survival : ℕ → Point → ℝ
  | 0, _ => 1
  | n + 1, p => transition (survival n) p

theorem survival_nonneg (n : ℕ) (p : Point) : 0 ≤ survival n p := by
  induction n generalizing p with
  | zero => norm_num [survival]
  | succ n ih => exact transition_nonneg ih p

/-- Finite total occupation mass before time `n`. -/
def occupation (n : ℕ) (p : Point) : ℝ := ∑ k ∈ range n, survival k p

theorem occupation_succ (n : ℕ) (p : Point) :
    occupation (n + 1) p = 1 + transition (occupation n) p := by
  unfold occupation
  rw [Finset.sum_range_succ']
  simp only [survival]
  rw [← transition_sum]
  ring

/-- Finite telescoping/induction using the exact potential drift. -/
theorem occupation_le (n : ℕ) (p : Point) : occupation n p ≤ 2 * potential p := by
  induction n generalizing p with
  | zero =>
      simp only [occupation, range_zero, sum_empty]
      exact mul_nonneg (by norm_num) (potential_pos p).le
  | succ n ih =>
      rw [occupation_succ]
      have h := transition_mono (fun q => ih q) p
      rw [transition_const_mul, transition_potential] at h
      linarith

theorem survival_summable (p : Point) : Summable (fun n => survival n p) := by
  apply summable_of_sum_range_le (fun n => survival_nonneg n p) (c := 2 * potential p)
  exact fun n => occupation_le n p

theorem tsum_survival_le (p : Point) : (∑' n, survival n p) ≤ 2 * potential p := by
  apply Real.tsum_le_of_sum_range_le (fun n => survival_nonneg n p)
  exact fun n => occupation_le n p

/-- The corner's normalized total occupation mass is at most `1/2`. -/
theorem quarter_tsum_survival_corner_le :
    (1 / 4 : ℝ) * (∑' n, survival n (0, 0)) ≤ 1 / 2 := by
  have h := tsum_survival_le (0, 0)
  rw [potential_corner] at h
  linarith

theorem survival_tendsto_zero (p : Point) :
    Tendsto (fun n => survival n p) atTop (𝓝 0) :=
  (survival_summable p).tendsto_atTop_zero

/-- The normalized endpoint kernel of the same killed transition operator. -/
def kernelProbability (n : ℕ) (p : Point) : ℝ := (count n p : ℝ) / 4 ^ n

theorem kernelProbability_nonneg (n : ℕ) (p : Point) : 0 ≤ kernelProbability n p := by
  unfold kernelProbability
  positivity

@[simp] theorem kernelProbability_zero (p : Point) :
    kernelProbability 0 p = if p = (0, 0) then 1 else 0 := by
  by_cases hp : p = (0, 0) <;> simp [kernelProbability, count, hp]

theorem kernelProbability_succ (n : ℕ) (p : Point) :
    kernelProbability (n + 1) p = transition (kernelProbability n) p := by
  calc
    _ = (∑ d : Fin 4, (((predecessor p d).elim (0 : ℕ) (count n) : ℕ) : ℝ)) /
        ((4 : ℝ) ^ n * 4) := by
      simp [kernelProbability, count, pow_succ, Nat.cast_sum]
    _ = (1 / 4 : ℝ) * ∑ d : Fin 4,
        ((((predecessor p d).elim (0 : ℕ) (count n) : ℕ) : ℝ) / (4 : ℝ) ^ n) := by
      rw [← Finset.sum_div]
      field_simp <;> ring
    _ = transition (kernelProbability n) p := by
      unfold transition
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      cases h : predecessor p d <;> simp [kernelProbability]

theorem kernelProbability_le_survival (n : ℕ) (p : Point) :
    kernelProbability n p ≤ survival n p := by
  induction n generalizing p with
  | zero => by_cases hp : p = (0, 0) <;> simp [kernelProbability_zero, survival, hp]
  | succ n ih =>
      rw [kernelProbability_succ]
      exact transition_mono ih p

end TranscendentalTuran.Green.Walks
