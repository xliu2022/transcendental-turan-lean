/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.ThresholdTables
public import TranscendentalTuran.Transfer.TableCounting

/-! # Controlling bad profiles after a two-dimensional direction switch -/

@[expose] public section

namespace TranscendentalTuran.Transfer

open scoped BigOperators

universe u v w
variable {d : ℕ} {A : Type u} {T : Type w} {V : Fin d → Type v}
variable [DecidableEq T]

def shiftedProfiles (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (j : Fin d) (σ : A → A) : A → V j → T :=
  fun a v => switchMap ψ guard j a v (σ a)

/-- The common dominant colours of the adjacent threshold tables each
have a single possible core vertex among all shifted profiles. -/
theorem intersection_colour_unique_preimage
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (j : Fin d) (σ : A → A) (hσ : ∀ a, σ a ≠ a) (roots : Finset T)
    {c : T}
    (hc : c ∈ rowColours (thresholdTable ψ guard (j.val + 1)) roots ∩
      columnColours (thresholdTable ψ guard j.val) roots) :
    ∃ r : A, ∀ a v, shiftedProfiles ψ guard j σ a v = c → v = guard j r := by
  classical
  obtain ⟨hr, hs⟩ := Finset.mem_inter.mp hc
  obtain ⟨_, r, y₀, y₁, hy, hy₀, hy₁⟩ :=
    (mem_rowColours _ roots c).mp hr
  obtain ⟨_, s, x₀, x₁, hx, hx₀, hx₁⟩ :=
    (mem_rowColours (fun b a => thresholdTable ψ guard j.val a b) roots c).mp hs
  have hy₀' : switchMap ψ guard j r (guard j r) y₀ = c := by
    rw [switchMap_left]
    exact hy₀
  have hy₁' : switchMap ψ guard j r (guard j r) y₁ = c := by
    rw [switchMap_left]
    exact hy₁
  have hx₀' : switchMap ψ guard j x₀ (guard j s) s = c := by
    rw [switchMap_right]
    exact hx₀
  have hx₁' : switchMap ψ guard j x₁ (guard j s) s = c := by
    rw [switchMap_right]
    exact hx₁
  refine ⟨r, ?_⟩
  intro a v hav
  exact common_colour_profile_preimage (guard j) (hguard j) (switchMap ψ guard j)
    (switchMap_separates ψ hψ guard hguard j) σ hσ
    hy hy₀' hy₁' hx hx₀' hx₁' hav

theorem bad_profile_colours_subset
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (j : Fin d) (σ : A → A) (hσ : ∀ a, σ a ≠ a) (roots : Finset T) :
    rowColours (shiftedProfiles ψ guard j σ) roots ⊆
      roots \ (rowColours (thresholdTable ψ guard (j.val + 1)) roots ∩
        columnColours (thresholdTable ψ guard j.val) roots) := by
  classical
  intro c hc
  obtain ⟨hroot, a, v, w, hvw, hv, hw⟩ := (mem_rowColours _ roots c).mp hc
  refine Finset.mem_sdiff.mpr ⟨hroot, ?_⟩
  intro hinter
  obtain ⟨r, hr⟩ := intersection_colour_unique_preimage ψ hψ guard hguard j σ hσ roots hinter
  exact hvw ((hr a v hv).trans (hr a w hw).symm)

/-- The cardinality estimate is integral, avoiding truncation in `q - |R∩C|`.
It is equivalent to the deletion budget used in the manuscript. -/
theorem bad_profiles_card_budget [Fintype A]
    (ψ : ((i : Fin d) → V i) → T) (hψ : SeparatesCoordinates ψ)
    (guard : (i : Fin d) → A → V i) (hguard : ∀ i, Function.Injective (guard i))
    (j : Fin d) (σ : A → A) (hσinj : Function.Injective σ)
    (hσ : ∀ a, σ a ≠ a) (roots : Finset T) :
    (rowSupport (shiftedProfiles ψ guard j σ) roots).card +
      (rowColours (thresholdTable ψ guard (j.val + 1)) roots).card +
        (columnColours (thresholdTable ψ guard j.val) roots).card ≤ 2 * roots.card := by
  classical
  let R := rowColours (thresholdTable ψ guard (j.val + 1)) roots
  let C := columnColours (thresholdTable ψ guard j.val) roots
  have hbad : (rowSupport (shiftedProfiles ψ guard j σ) roots).card ≤
      (roots \ (R ∩ C)).card := by
    exact (rowSupport_card_le (switch_profiles_separated ψ hψ guard hguard j σ hσinj) roots).trans
      (Finset.card_le_card (bad_profile_colours_subset ψ hψ guard hguard j σ hσ roots))
  have hR : R ⊆ roots := rowColours_subset _ _
  have hC : C ⊆ roots := columnColours_subset _ _
  have hinter : R ∩ C ⊆ roots := (Finset.inter_subset_left).trans hR
  have hdiff := Finset.card_sdiff_add_card_eq_card hinter
  have hunion := Finset.card_union_add_card_inter R C
  have hle := Finset.card_le_card (Finset.union_subset hR hC)
  change (rowSupport (shiftedProfiles ψ guard j σ) roots).card + R.card + C.card ≤ _
  omega

omit [DecidableEq T] in
/-- After deleting the bad profiles, every root colour belongs to at most
one core vertex globally, even when the profile indices agree. -/
theorem root_preimage_unique_on_good_profiles {B : Type*} [Fintype A]
    {f : A → B → T} (hf : SeparatedTable f) (roots : Finset T)
    {a a' : A} {v v' : B} {c : T}
    (ha : a ∉ rowSupport f roots) (_ha' : a' ∉ rowSupport f roots)
    (hc : c ∈ roots) (hav : f a v = c) (hav' : f a' v' = c) : v = v' := by
  classical
  by_contra hvv'
  by_cases haa' : a = a'
  · subst a'
    apply ha
    exact (mem_rowSupport f roots a).mpr ⟨c, hc, v, v', hvv', hav, hav'⟩
  · exact hf a a' v v' haa' hvv' (hav.trans hav'.symm)

/-- A finite partition with more than `h` times the number of blocks in
retained vertices has a block containing more than `h` retained vertices. -/
theorem exists_large_retained_block {Blocks : Type*} [Fintype Blocks]
    [DecidableEq Blocks] [DecidableEq A] (block : A → Blocks) (good : Finset A)
    (h : ℕ) (hgood : h * Fintype.card Blocks < good.card) :
    ∃ b, h < (good.filter (fun a => block a = b)).card := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : good.card ≤ Fintype.card Blocks * h := by
    calc
      good.card = ∑ b : Blocks, (good.filter (fun a => block a = b)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ ≤ ∑ _b : Blocks, h := Finset.sum_le_sum (fun b _ => hnone b)
      _ = Fintype.card Blocks * h := by simp
  rw [Nat.mul_comm (Fintype.card Blocks) h] at hsum
  omega

theorem exists_retained_block_subset {Blocks : Type*} [Fintype Blocks]
    [DecidableEq Blocks] [DecidableEq A] (block : A → Blocks) (good : Finset A)
    (h : ℕ) (hgood : h * Fintype.card Blocks < good.card) :
    ∃ b, ∃ S : Finset A, S ⊆ good ∧ S.card = h ∧ ∀ a ∈ S, block a = b := by
  obtain ⟨b, hb⟩ := exists_large_retained_block block good h hgood
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hb)
  refine ⟨b, S, ?_, hcard, ?_⟩
  · exact hS.trans (Finset.filter_subset _ _)
  · intro a ha
    exact (Finset.mem_filter.mp (hS ha)).2

end TranscendentalTuran.Transfer
