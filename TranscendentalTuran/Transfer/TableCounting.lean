/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.Tables
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Omega

/-! # Finite counting for separated two-dimensional tables -/

@[expose] public section

namespace TranscendentalTuran.Transfer

open scoped BigOperators

universe u v w
variable {A : Type u} {B : Type v} {C : Type w}

theorem SeparatedTable.swap {f : A → B → C} (hf : SeparatedTable f) :
    SeparatedTable (fun b a => f a b) := by
  intro b b' a a' hb ha
  exact hf a a' b b' ha hb

noncomputable def rowColours (f : A → B → C) (roots : Finset C) : Finset C := by
  classical
  exact roots.filter fun c => ∃ a b b', b ≠ b' ∧ f a b = c ∧ f a b' = c

noncomputable def columnColours (f : A → B → C) (roots : Finset C) : Finset C :=
  rowColours (fun b a => f a b) roots

noncomputable def rowSupport [Fintype A] (f : A → B → C) (roots : Finset C) : Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    ∃ c ∈ roots, ∃ b b', b ≠ b' ∧ f a b = c ∧ f a b' = c

noncomputable def columnSupport [Fintype B] (f : A → B → C) (roots : Finset C) : Finset B :=
  rowSupport (fun b a => f a b) roots

theorem mem_rowColours (f : A → B → C) (roots : Finset C) (c : C) :
    c ∈ rowColours f roots ↔
      c ∈ roots ∧ ∃ a b b', b ≠ b' ∧ f a b = c ∧ f a b' = c := by
  classical
  simp [rowColours]

theorem mem_rowSupport [Fintype A] (f : A → B → C) (roots : Finset C) (a : A) :
    a ∈ rowSupport f roots ↔
      ∃ c ∈ roots, ∃ b b', b ≠ b' ∧ f a b = c ∧ f a b' = c := by
  classical
  simp [rowSupport]

theorem rowColours_subset (f : A → B → C) (roots : Finset C) :
    rowColours f roots ⊆ roots := by
  classical
  exact Finset.filter_subset _ _

theorem columnColours_subset (f : A → B → C) (roots : Finset C) :
    columnColours f roots ⊆ roots := rowColours_subset _ _

theorem row_column_colours_disjoint {f : A → B → C} (hf : SeparatedTable f)
    (roots : Finset C) : Disjoint (rowColours f roots) (columnColours f roots) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hr hc
  obtain ⟨_, a, b, b', hbb', hb, hb'⟩ := (mem_rowColours f roots c).mp hr
  obtain ⟨_, y, x, x', hxx', hx, hx'⟩ :=
    (mem_rowColours (fun b a => f a b) roots c).mp hc
  have hrow := fibre_in_row_of_two_columns hf hbb' hb hb'
  exact hxx' ((hrow x y hx).trans (hrow x' y hx').symm)

theorem oriented_colours_card_le {f : A → B → C} (hf : SeparatedTable f)
    (roots : Finset C) :
    (rowColours f roots).card + (columnColours f roots).card ≤ roots.card := by
  classical
  rw [← Finset.card_union_of_disjoint (row_column_colours_disjoint hf roots)]
  exact Finset.card_le_card (Finset.union_subset (rowColours_subset f roots)
    (columnColours_subset f roots))

theorem rowSupport_card_le [Fintype A] {f : A → B → C} (hf : SeparatedTable f)
    (roots : Finset C) : (rowSupport f roots).card ≤ (rowColours f roots).card := by
  classical
  have h (a : rowSupport f roots) :
      ∃ c, c ∈ roots ∧ ∃ b b', b ≠ b' ∧ f a.val b = c ∧ f a.val b' = c :=
    (mem_rowSupport f roots a.val).mp a.property
  choose colour hcolour b₀ b₁ hne h₀ h₁ using h
  let g : rowSupport f roots → rowColours f roots := fun a =>
    ⟨colour a, (mem_rowColours f roots (colour a)).mpr
      ⟨hcolour a, a.val, b₀ a, b₁ a, hne a, h₀ a, h₁ a⟩⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' haa'
  apply Subtype.ext
  have hc : colour a = colour a' := congrArg Subtype.val haa'
  have hrow := fibre_in_row_of_two_columns hf (hne a) (h₀ a) (h₁ a)
  exact (hrow a'.val (b₀ a') ((h₀ a').trans hc.symm)).symm

theorem columnSupport_card_le [Fintype B] {f : A → B → C} (hf : SeparatedTable f)
    (roots : Finset C) : (columnSupport f roots).card ≤ (columnColours f roots).card :=
  rowSupport_card_le hf.swap roots

noncomputable def outsideSupport [Fintype A] [Fintype B]
    (f : A → B → C) (roots : Finset C) : Finset (A × B) := by
  classical
  exact (Finset.univ \ rowSupport f roots).product
    (Finset.univ \ columnSupport f roots)

noncomputable def nonrootCells [Fintype A] [Fintype B]
    (f : A → B → C) (roots : Finset C) : Finset (A × B) := by
  classical
  exact Finset.univ.filter fun p => f p.1 p.2 ∉ roots

theorem outsideSupport_card [Fintype A] [Fintype B]
    (f : A → B → C) (roots : Finset C) :
    (outsideSupport f roots).card =
      (Fintype.card A - (rowSupport f roots).card) *
        (Fintype.card B - (columnSupport f roots).card) := by
  classical
  simp [outsideSupport, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

/-- Outside the supporting rows and columns, each root colour occurs at
most once. This supplies the additive `q` term in the manuscript's count. -/
theorem outside_root_cells_injective [Fintype A] [Fintype B]
    {f : A → B → C} (hf : SeparatedTable f) (roots : Finset C) :
    Set.InjOn (fun p : A × B => f p.1 p.2)
      {p | p ∈ outsideSupport f roots ∧ f p.1 p.2 ∈ roots} := by
  classical
  intro p hp p' hp' heq
  have hpr : p.1 ∉ rowSupport f roots :=
    (Finset.mem_sdiff.mp (Finset.mem_product.mp hp.1).1).2
  have hpc : p.2 ∉ columnSupport f roots :=
    (Finset.mem_sdiff.mp (Finset.mem_product.mp hp.1).2).2
  by_cases hrow : p.1 = p'.1
  · apply Prod.ext hrow
    by_contra hcol
    apply hpr
    apply (mem_rowSupport f roots p.1).mpr
    refine ⟨f p.1 p.2, hp.2, p.2, p'.2, hcol, rfl, ?_⟩
    simpa [hrow] using heq.symm
  · have hcol : p.2 = p'.2 := (same_colour_row_or_column hf heq).resolve_left hrow
    exfalso
    apply hpc
    apply (mem_rowSupport (fun b a => f a b) roots p.2).mpr
    refine ⟨f p.1 p.2, hp.2, p.1, p'.1, hrow, rfl, ?_⟩
    simpa [hcol] using heq.symm

/-- The uncovered rectangle is accounted for by nonroot cells and by at
most one remaining cell per root colour. -/
theorem outsideSupport_card_le [Fintype A] [Fintype B]
    {f : A → B → C} (hf : SeparatedTable f) (roots : Finset C) :
    (outsideSupport f roots).card ≤ (nonrootCells f roots).card + roots.card := by
  classical
  let s := outsideSupport f roots
  have hroot : (s.filter (fun p => f p.1 p.2 ∈ roots)).card ≤ roots.card := by
    apply Finset.card_le_card_of_injOn (fun p : A × B => f p.1 p.2)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp p' hp' heq
      apply outside_root_cells_injective hf roots
      · exact Finset.mem_filter.mp hp
      · exact Finset.mem_filter.mp hp'
      · exact heq
  have hnonroot : (s.filter (fun p => f p.1 p.2 ∉ roots)).card ≤
      (nonrootCells f roots).card := by
    apply Finset.card_le_card
    intro p hp
    change p ∈ (Finset.univ : Finset (A × B)).filter (fun p => f p.1 p.2 ∉ roots)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := s)
    (fun p => f p.1 p.2 ∈ roots)
  change s.card ≤ _
  omega

/-- A partition into parts in which every three distinct cells contain a
root cell leaves at most two nonroot cells per part. For the manuscript,
the parts are the cyclic diagonals of pairs of guard clique blocks. -/
theorem nonroot_partition_bound {Cells Parts : Type*} [Fintype Cells] [Fintype Parts]
    [DecidableEq Cells] [DecidableEq Parts] [DecidableEq C] (f : Cells → C) (roots : Finset C)
    (part : Cells → Parts)
    (htriples : ∀ a b c, part a = part b → part a = part c →
      a ≠ b → a ≠ c → b ≠ c → f a ∈ roots ∨ f b ∈ roots ∨ f c ∈ roots) :
    (Finset.univ.filter (fun a => f a ∉ roots)).card ≤ 2 * Fintype.card Parts := by
  classical
  let bad : Finset Cells := Finset.univ.filter fun a => f a ∉ roots
  have hfibre (p : Parts) : (bad.filter (fun a => part a = p)).card ≤ 2 := by
    by_contra h
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
    have hap := (Finset.mem_filter.mp ha).2
    have hbp := (Finset.mem_filter.mp hb).2
    have hcp := (Finset.mem_filter.mp hc).2
    have han : f a ∉ roots := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hbn : f b ∉ roots := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hcn : f c ∉ roots := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    rcases htriples a b c (hap.trans hbp.symm) (hap.trans hcp.symm) hab hac hbc
      with h | h | h
    · exact han h
    · exact hbn h
    · exact hcn h
  calc
    bad.card = ∑ p : Parts, (bad.filter (fun a => part a = p)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _p : Parts, 2 := Finset.sum_le_sum (fun p _ => hfibre p)
    _ = 2 * Fintype.card Parts := by simp [Nat.mul_comm]

end TranscendentalTuran.Transfer
