/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Omega

/-!
# Choosing one of two options with matching conflicts

This proves the choice step in factor recovery. The manuscript colours a
union of two matchings. We prove the same finite choice statement by Hall:
two options per row and at most two options per conflict class imply Hall's
inequality by double counting. No graph colouring assertion is assumed.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

open scoped BigOperators

universe u v
variable {R : Type u} {C : Type v}

/-- Two options per row admit distinct resource representatives when every
resource is used by at most two options globally. -/
theorem select_two_options [Fintype R] [DecidableEq R] [DecidableEq C]
    (label : R × Bool → C)
    (hcap : ∀ c, (Finset.univ.filter (fun p : R × Bool => label p = c)).card ≤ 2) :
    ∃ choice : R → Bool, Function.Injective (fun r => label (r, choice r)) := by
  classical
  let t : R → Finset C := fun r => {label (r, false), label (r, true)}
  have hhall : ∀ s : Finset R, s.card ≤ (s.biUnion t).card := by
    intro s
    let options : Finset (R × Bool) := s.product Finset.univ
    have himage : options.image label = s.biUnion t := by
      ext c
      simp only [Finset.mem_image, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨r, b⟩, hp, heq⟩
        have hr : r ∈ s := (Finset.mem_product.mp hp).1
        refine ⟨r, hr, ?_⟩
        cases b <;> simp [t, ← heq]
      · rintro ⟨r, hr, hc⟩
        have hc' : c = label (r, false) ∨ c = label (r, true) := by simpa [t] using hc
        rcases hc' with hc' | hc'
        · exact ⟨(r, false), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, hc'.symm⟩
        · exact ⟨(r, true), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, hc'.symm⟩
    have hcount : options.card ≤ (options.image label).card * 2 := by
      calc
        options.card = ∑ c ∈ options.image label,
            (options.filter (fun p => label p = c)).card :=
          Finset.card_eq_sum_card_image label options
        _ ≤ ∑ _c ∈ options.image label, 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact (Finset.card_le_card (Finset.filter_subset_filter _
            (Finset.subset_univ options))).trans (hcap c)
        _ = _ := by simp
    have hoptions : options.card = s.card * 2 := by simp [options]
    rw [hoptions, himage] at hcount
    omega
  obtain ⟨g, hg, hgt⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  have hex (r : R) : ∃ b : Bool, label (r, b) = g r := by
    have h : g r = label (r, false) ∨ g r = label (r, true) := by
      simpa [t] using hgt r
    rcases h with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  choose choice hchoice using hex
  refine ⟨choice, ?_⟩
  intro r s h
  apply hg
  simpa only [hchoice] using h

/-- A symmetric relation in which each vertex has at most one neighbor.
Loops are harmless for the finite resource argument and are not excluded. -/
structure MatchingRelation (O : Type*) where
  rel : O → O → Prop
  symm : ∀ {x y}, rel x y → rel y x
  unique : ∀ {x y z}, rel x y → rel x z → y = z

namespace MatchingRelation

variable {O : Type*} [Fintype O] [DecidableEq O]

noncomputable def conflictClass (M : MatchingRelation O) (x : O) : Finset O := by
  classical
  exact insert x (Finset.univ.filter (M.rel x))

theorem mem_conflictClass (M : MatchingRelation O) (x y : O) :
    y ∈ M.conflictClass x ↔ y = x ∨ M.rel x y := by
  classical
  simp [conflictClass]

theorem self_mem_conflictClass (M : MatchingRelation O) (x : O) :
    x ∈ M.conflictClass x := (M.mem_conflictClass x x).mpr (Or.inl rfl)

theorem conflictClass_card_le_two (M : MatchingRelation O) (x : O) :
    (M.conflictClass x).card ≤ 2 := by
  classical
  have hcard : (Finset.univ.filter (M.rel x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    exact M.unique (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
  have h := Finset.card_insert_le x (Finset.univ.filter (M.rel x))
  change (insert x (Finset.univ.filter (M.rel x))).card ≤ 2
  omega

theorem conflictClass_eq_of_rel (M : MatchingRelation O) {x y : O}
    (hxy : M.rel x y) : M.conflictClass x = M.conflictClass y := by
  ext z
  rw [M.mem_conflictClass, M.mem_conflictClass]
  constructor
  · rintro (rfl | hxz)
    · exact Or.inr (M.symm hxy)
    · exact Or.inl (M.unique hxz hxy)
  · rintro (rfl | hyz)
    · exact Or.inr hxy
    · exact Or.inl (M.unique hyz (M.symm hxy))

theorem conflictClass_fibre_card_le_two (M : MatchingRelation O) (c : Finset O) :
    (Finset.univ.filter (fun x => M.conflictClass x = c)).card ≤ 2 := by
  classical
  by_cases h : (Finset.univ.filter (fun x => M.conflictClass x = c)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hxc := (Finset.mem_filter.mp hx).2
    have hsub : Finset.univ.filter (fun y => M.conflictClass y = c) ⊆
        M.conflictClass x := by
      intro y hy
      have hyc := (Finset.mem_filter.mp hy).2
      rw [hxc, ← hyc]
      exact M.self_mem_conflictClass y
    exact (Finset.card_le_card hsub).trans (M.conflictClass_card_le_two x)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

end MatchingRelation

/-- Choose exactly one option in each row so that no two chosen options
from different rows form a matching conflict. -/
theorem choose_without_matching_conflicts [Fintype R] [DecidableEq R]
    (M : MatchingRelation (R × Bool)) :
    ∃ choice : R → Bool,
      ∀ r s, r ≠ s → ¬ M.rel (r, choice r) (s, choice s) := by
  classical
  obtain ⟨choice, hinj⟩ := select_two_options M.conflictClass
    M.conflictClass_fibre_card_le_two
  refine ⟨choice, ?_⟩
  intro r s hrs hrel
  exact hrs (hinj (M.conflictClass_eq_of_rel hrel))

/-- Finite simultaneous choice avoiding a common forbidden set. The size
bound is deliberately expressed without an assumed ordering of the rows. -/
theorem select_distinct_indices_avoiding [Fintype R] [DecidableEq R] [DecidableEq C]
    (allowed : R → Finset C) (forbidden : Finset C)
    (hsize : ∀ r, forbidden.card + Fintype.card R ≤ (allowed r).card) :
    ∃ choice : R → C, Function.Injective choice ∧
      ∀ r, choice r ∈ allowed r ∧ choice r ∉ forbidden := by
  classical
  let t : R → Finset C := fun r => allowed r \ forbidden
  have ht (r : R) : Fintype.card R ≤ (t r).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := allowed r) (t := forbidden)
    have hs := hsize r
    dsimp [t]
    omega
  have hhall : ∀ s : Finset R, s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨r, hr⟩ := hs
      have hsub : t r ⊆ s.biUnion t := by
        intro c hc
        exact Finset.mem_biUnion.mpr ⟨r, hr, hc⟩
      exact (Finset.card_le_univ s).trans ((ht r).trans (Finset.card_le_card hsub))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp
  obtain ⟨choice, hinj, hc⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨choice, hinj, ?_⟩
  intro r
  exact Finset.mem_sdiff.mp (hc r)

/-- The numerical certificate allocation used in the manuscript: thirteen
data vertices, forty already selected root indices, and at least sixty-three
available data indices at each vertex. -/
theorem select_certificate_indices [Fintype R] [DecidableEq R] [DecidableEq C]
    (hrows : Fintype.card R ≤ 13) (allowed : R → Finset C) (forbidden : Finset C)
    (hforbidden : forbidden.card ≤ 40) (hallowed : ∀ r, 63 ≤ (allowed r).card) :
    ∃ choice : R → C, Function.Injective choice ∧
      ∀ r, choice r ∈ allowed r ∧ choice r ∉ forbidden := by
  apply select_distinct_indices_avoiding allowed forbidden
  intro r
  have h := hallowed r
  omega

end TranscendentalTuran.Transfer
