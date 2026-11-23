/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.Profiles
public import TranscendentalTuran.Transfer.TableDominance
public import Mathlib.Data.Fintype.EquivFin

/-! # Selecting sixty-four private profiles at an adjacent table switch -/

@[expose] public section

namespace TranscendentalTuran.Transfer

universe u v w z
variable {d : ℕ} {A : Type u} {T : Type w} {V : Fin d → Type v}

theorem threshold_rowColours_zero
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (roots : Finset T) : rowColours (thresholdTable ψ guard 0) roots = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, a, b, b', hne, hb, hb'⟩ := (mem_rowColours _ roots c).mp hc
  apply hne
  apply diagonal_injective ψ hψ guard hguard
  simpa only [thresholdTable_zero] using hb.trans hb'.symm

theorem threshold_columnColours_last
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (roots : Finset T) : columnColours (thresholdTable ψ guard d) roots = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, b, a, a', hne, ha, ha'⟩ :=
    (mem_rowColours (fun b a => thresholdTable ψ guard d a b) roots c).mp hc
  apply hne
  apply diagonal_injective ψ hψ guard hguard
  simpa only [thresholdTable_last] using ha.trans ha'.symm

theorem exists_dominant_switch [Fintype A]
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (roots : Finset T) (n t : ℕ) (hA : Fintype.card A = n)
    (hn : 128 ≤ n) (ht : 128 ≤ t)
    (hroots : (roots.card : ℝ) ≤ 4 * (n : ℝ) / 3)
    (hmissing : ∀ k ≤ d, ((nonrootCells (thresholdTable ψ guard k) roots).card : ℝ) ≤
      2 * (n : ℝ) ^ 2 / t) :
    ∃ j : Fin d,
      11 * (n : ℝ) / 12 < (rowColours (thresholdTable ψ guard (j.val + 1)) roots).card ∧
      11 * (n : ℝ) / 12 < (columnColours (thresholdTable ψ guard j.val) roots).card := by
  have hdom (k : ℕ) (hk : k ≤ d) :=
    (unique_dominant_direction (thresholdTable_separated ψ hψ guard hguard k)
      roots n t hA hA hn ht hroots (hmissing k hk)).1
  let p : ℕ → Prop := fun k =>
    11 * (n : ℝ) / 12 < (rowColours (thresholdTable ψ guard k) roots).card
  have hzero : ¬ p 0 := by
    dsimp [p]
    rw [threshold_rowColours_zero ψ hψ guard hguard, Finset.card_empty, Nat.cast_zero]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hlast : p d := by
    rcases hdom d le_rfl with h | h
    · exact h
    · rw [threshold_columnColours_last ψ hψ guard hguard, Finset.card_empty,
        Nat.cast_zero] at h
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
  obtain ⟨k, hkd, hk, hnext⟩ := exists_adjacent_change p hzero hlast
  refine ⟨⟨k, hkd⟩, hnext, ?_⟩
  exact (hdom k (Nat.le_of_lt hkd)).resolve_left hk

/-- Exact deletion and block counting for the manuscript guard. At least
one sixth of the guard survives; blocks of size at least 512 supply 64
profiles. The return value is a genuine injection of the selected indices. -/
theorem select_private_profiles [Fintype A] [DecidableEq A] [DecidableEq T]
    {Blocks : Type z} [Fintype Blocks] [DecidableEq Blocks]
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (roots : Finset T) (n t : ℕ) (hA : Fintype.card A = n)
    (hn : 128 ≤ n) (ht : 512 ≤ t)
    (hroots : (roots.card : ℝ) ≤ 4 * (n : ℝ) / 3)
    (hmissing : ∀ k ≤ d, ((nonrootCells (thresholdTable ψ guard k) roots).card : ℝ) ≤
      2 * (n : ℝ) ^ 2 / t)
    (block : A → Blocks) (hblocks : n = t * Fintype.card Blocks)
    (σ : A → A) (hσinj : Function.Injective σ) (hσ : ∀ a, σ a ≠ a) :
    ∃ j : Fin d, ∃ take : Fin 64 ↪ A,
      (∀ a b, block (take a) = block (take b)) ∧
      ∀ a b v w c, c ∈ roots →
        shiftedProfiles ψ guard j σ (take a) v = c →
        shiftedProfiles ψ guard j σ (take b) w = c → v = w := by
  classical
  obtain ⟨j, hr, hc⟩ := exists_dominant_switch ψ hψ guard hguard roots n t hA
    hn (by omega) hroots hmissing
  let bad := rowSupport (shiftedProfiles ψ guard j σ) roots
  let good := Finset.univ \ bad
  have hbad : (bad.card : ℝ) < 5 * (n : ℝ) / 6 := by
    have hbudget : (bad.card : ℝ) +
        (rowColours (thresholdTable ψ guard (j.val + 1)) roots).card +
        (columnColours (thresholdTable ψ guard j.val) roots).card ≤ 2 * roots.card := by
      exact_mod_cast bad_profiles_card_budget ψ hψ guard hguard j σ hσinj hσ roots
    linarith
  have hpartition : good.card + bad.card = n := by
    simpa [good, hA] using Finset.card_sdiff_add_card_eq_card
      (show bad ⊆ (Finset.univ : Finset A) from Finset.subset_univ _)
  have hgood : (n : ℝ) / 6 < good.card := by
    have hp : (good.card : ℝ) + bad.card = n := by exact_mod_cast hpartition
    linarith
  have htR : (512 : ℝ) ≤ t := by exact_mod_cast ht
  have hnblocks : (n : ℝ) = (t : ℝ) * Fintype.card Blocks := by exact_mod_cast hblocks
  have hblock0 : (0 : ℝ) ≤ Fintype.card Blocks := Nat.cast_nonneg _
  have hcard : 64 * Fintype.card Blocks < good.card := by
    have hlarge : (64 : ℝ) * Fintype.card Blocks < good.card := by
      nlinarith
    exact_mod_cast hlarge
  obtain ⟨b, S, hSgood, hS64, hSblock⟩ :=
    exists_retained_block_subset block good 64 hcard
  let e : S ≃ Fin 64 := Finset.equivFinOfCardEq hS64
  let take : Fin 64 ↪ A :=
    ⟨fun a => (e.symm a).val, fun _ _ h => e.symm.injective (Subtype.ext h)⟩
  have htake (a : Fin 64) : take a ∈ S := (e.symm a).property
  refine ⟨j, take, ?_, ?_⟩
  · intro a a'
    exact (hSblock _ (htake a)).trans (hSblock _ (htake a')).symm
  · intro a a' v w c hc hav haw
    exact root_preimage_unique_on_good_profiles
      (switch_profiles_separated ψ hψ guard hguard j σ hσinj) roots
      (Finset.mem_sdiff.mp (hSgood (htake a))).2
      (Finset.mem_sdiff.mp (hSgood (htake a'))).2 hc hav haw

end TranscendentalTuran.Transfer
