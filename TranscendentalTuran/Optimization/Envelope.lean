/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Inverting an affine maximum envelope

This is the order-theoretic step in the arithmetic reduction of
`single_three_graph_transcendental_density_short.tex`.

For strictly positive slopes, an attained maximum of `A z + g * B z`
determines `g` as an attained minimum of `(α - A z) / B z`.
No algebraicity or quantifier-elimination hypothesis enters these lemmas.
-/

namespace TranscendentalTuran.Optimization

variable {ι : Type*} {s : Set ι} {A B : ι → ℝ} {g α : ℝ}

/-- The pointwise inequality used in envelope inversion. -/
theorem le_ratio_of_affine_le {z : ι} (hB : 0 < B z)
    (h : A z + g * B z ≤ α) : g ≤ (α - A z) / B z := by
  apply (le_div_iff₀ hB).2
  linarith

/-- Equality at a maximizer gives equality in the recovered ratio. -/
theorem ratio_eq_of_affine_eq {z : ι} (hB : 0 < B z)
    (h : A z + g * B z = α) : (α - A z) / B z = g := by
  apply (div_eq_iff (ne_of_gt hB)).2
  linarith

/-- An attained affine maximum yields an attained ratio minimum. -/
theorem isLeast_ratio_of_isGreatest_affine
    (hB : ∀ z ∈ s, 0 < B z)
    (hα : IsGreatest ((fun z => A z + g * B z) '' s) α) :
    IsLeast ((fun z => (α - A z) / B z) '' s) g := by
  obtain ⟨z₀, hz₀, heq⟩ := hα.1
  refine ⟨⟨z₀, hz₀, ratio_eq_of_affine_eq (hB z₀ hz₀) heq⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact le_ratio_of_affine_le (hB z hz) (hα.2 ⟨z, hz, rfl⟩)

/-- The inverse implication records that no information is lost. -/
theorem isGreatest_affine_of_isLeast_ratio
    (hB : ∀ z ∈ s, 0 < B z)
    (hg : IsLeast ((fun z => (α - A z) / B z) '' s) g) :
    IsGreatest ((fun z => A z + g * B z) '' s) α := by
  obtain ⟨z₀, hz₀, heq⟩ := hg.1
  have hz₀eq : A z₀ + g * B z₀ = α := by
    have h := (div_eq_iff (ne_of_gt (hB z₀ hz₀))).1 heq
    linarith
  refine ⟨⟨z₀, hz₀, hz₀eq⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have h := (le_div_iff₀ (hB z hz)).1 (hg.2 ⟨z, hz, rfl⟩)
  linarith

/-- Positive slopes make attained envelope values strictly increasing. -/
theorem affine_maximum_strict_mono
    (hB : ∀ z ∈ s, 0 < B z) {g₁ g₂ α₁ α₂ : ℝ}
    (h₁ : IsGreatest ((fun z => A z + g₁ * B z) '' s) α₁)
    (h₂ : IsGreatest ((fun z => A z + g₂ * B z) '' s) α₂)
    (hg : g₁ < g₂) : α₁ < α₂ := by
  obtain ⟨z, hz, heq⟩ := h₁.1
  calc
    α₁ = A z + g₁ * B z := heq.symm
    _ < A z + g₂ * B z := by
      have h := mul_lt_mul_of_pos_right hg (hB z hz)
      linarith
    _ ≤ α₂ := h₂.2 ⟨z, hz, rfl⟩

end TranscendentalTuran.Optimization
