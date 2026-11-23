module

public import TranscendentalTuran.Optimization.RootLocalization
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Complete-root polynomial estimates

Formalization author and responsible maintainer: Xizhi Liu.

The variance identity proves the optimal bound for a two-root link. The
degree-three identity evaluates the root clique at uniform weights.
-/

namespace TranscendentalTuran.Optimization

open Finset

theorem sum_sq_ge_mean_sq {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) :
    (∑ i, r i) ^ 2 / (n : ℝ) ≤ ∑ i, (r i) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : 0 ≤ ∑ i : Fin n, (r i - (∑ j, r j) / (n : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he : (∑ i : Fin n, (r i - (∑ j, r j) / (n : ℝ)) ^ 2) =
      (∑ i, (r i) ^ 2) - (∑ i, r i) ^ 2 / (n : ℝ) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hn0] <;> ring
  rw [he] at hnn
  linarith

theorem two_elementary_le_mass_square {I : Type*} [Fintype I] (r : I → ℝ) :
    2 * elementary r 2 ≤ (∑ i, r i) ^ 2 := by
  have he := two_mul_elementary_two r
  have hn : 0 ≤ ∑ i, (r i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

theorem two_elementary_le_clique_factor {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) :
    2 * elementary r 2 ≤ (1 - 1 / (n : ℝ)) * (∑ i, r i) ^ 2 := by
  have hsq := sum_sq_ge_mean_sq hn r
  have he := two_mul_elementary_two r
  have hid : (1 - 1 / (n : ℝ)) * (∑ i, r i) ^ 2 =
      (∑ i, r i) ^ 2 - (∑ i, r i) ^ 2 / (n : ℝ) := by ring
  rw [hid]
  linarith

theorem six_elementary_three_uniform (n : ℕ) (c : ℝ) :
    6 * elementary (fun _i : Fin n => c) 3 =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * c ^ 3 := by
  have h2 := two_mul_elementary_two (fun _i : Fin n => c)
  have h3 := three_mul_elementary_three (fun _i : Fin n => c)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2 h3
  linear_combination 2 * h3 + ((n : ℝ) * c) * h2

theorem uniform_root_clique_value {n : ℕ} (hn : 0 < n) :
    6 * elementary (fun _i : Fin n => 1 / (n : ℝ)) 3 =
      RootLocalization.cliqueProbability (n : ℝ) := by
  rw [six_elementary_three_uniform]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold RootLocalization.cliqueProbability
  field_simp [ne_of_gt hn0] <;> ring

end TranscendentalTuran.Optimization
