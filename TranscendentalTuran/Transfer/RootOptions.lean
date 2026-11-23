/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.Choices

/-! # Compatible choices of declaring root labels and profile indices -/

@[expose] public section

namespace TranscendentalTuran.Transfer

universe u v w
variable {Q : Type u} {R : Type v} {I : Type w}

theorem matching_pair_partner_unique [DecidableEq Q]
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    {a b c : Q} (hab : {a, b} ∈ Γ) (hac : {a, c} ∈ Γ) : b = c := by
  have heq : ({a, b} : Finset Q) = {a, c} := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hmatching _ hab _ hac hne))
      (a := a) (by simp) (by simp)
  have hba : b ≠ a := by
    intro h
    have hc := hcard _ hab
    simp [h] at hc
  have hb : b ∈ ({a, c} : Finset Q) := by rw [← heq]; simp
  simpa [hba] using hb

/-- Root labels are private to rows, and each row has two distinct profile
indices. A matching of declaring pairs permits a compatible choice in every
row. The selected labels are injective and paired selected labels have
different indices. -/
theorem select_root_options [Fintype R] [DecidableEq R] [DecidableEq Q]
    (Γ : Finset (Finset Q))
    (hcard : ∀ e ∈ Γ, e.card = 2)
    (hmatching : ∀ e ∈ Γ, ∀ e' ∈ Γ, e ≠ e' → Disjoint e e')
    (label : R → Bool → Q) (index : R → Bool → I)
    (hprivate : ∀ r s a b, label r a = label s b → r = s)
    (hindex : ∀ r, Function.Injective (index r)) :
    ∃ choice : R → Bool,
      Function.Injective (fun r => label r (choice r)) ∧
      ∀ r s, {label r (choice r), label s (choice s)} ∈ Γ →
        index r (choice r) ≠ index s (choice s) := by
  classical
  let M : MatchingRelation (R × Bool) :=
    { rel := fun p q => p.1 ≠ q.1 ∧ index p.1 p.2 = index q.1 q.2 ∧
        {label p.1 p.2, label q.1 q.2} ∈ Γ
      symm := by
        intro p q hpq
        exact ⟨Ne.symm hpq.1, hpq.2.1.symm, by
          simpa [Finset.pair_comm] using hpq.2.2⟩
      unique := by
        intro p q z hpq hpz
        have hlabel := matching_pair_partner_unique Γ hcard hmatching hpq.2.2 hpz.2.2
        have hrow := hprivate q.1 z.1 q.2 z.2 hlabel
        have hi := hpq.2.1.symm.trans hpz.2.1
        apply Prod.ext hrow
        rw [← hrow] at hi
        exact hindex q.1 hi }
  obtain ⟨choice, hchoice⟩ := choose_without_matching_conflicts M
  refine ⟨choice, ?_, ?_⟩
  · intro r s h
    exact hprivate r s (choice r) (choice s) h
  · intro r s hrs heq
    by_cases h : r = s
    · subst s
      have hc := hcard _ hrs
      simp at hc
    · exact hchoice r s h ⟨h, heq, hrs⟩

end TranscendentalTuran.Transfer
