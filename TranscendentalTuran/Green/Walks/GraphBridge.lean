/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Kernel
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace TranscendentalTuran.Green.Walks

theorem predecessor_unique {p q : Point} {d e : Fin 4}
    (hd : predecessor p d = some q) (he : predecessor p e = some q) : d = e := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    fin_cases d <;> fin_cases e <;>
    first | rfl | (simp [predecessor, hi, hj, Prod.mk.injEq] at hd he <;> omega)

theorem predecessor_symmetric {p q : Point} (h : ∃ d, predecessor p d = some q) :
    ∃ d, predecessor q d = some p := by
  rcases p with ⟨i, j⟩
  obtain ⟨d, hd⟩ := h
  fin_cases d
  · simp only [predecessor, Option.some.injEq] at hd
    subst q
    exact ⟨1, by simp [predecessor]⟩
  · by_cases hi : i = 0
    · simp [predecessor, hi] at hd
    · simp [predecessor, hi] at hd
      subst q
      refine ⟨0, ?_⟩
      simp [predecessor, Prod.mk.injEq]
      omega
  · by_cases hi : i = 0
    · simp [predecessor, hi] at hd
    · simp [predecessor, hi] at hd
      subst q
      refine ⟨3, ?_⟩
      simp [predecessor, Prod.mk.injEq]
      omega
  · by_cases hj : j = 0
    · simp [predecessor, hj] at hd
    · simp [predecessor, hj] at hd
      subst q
      refine ⟨2, ?_⟩
      simp [predecessor, Prod.mk.injEq]
      omega

theorem predecessor_irreflexive (p : Point) : ¬∃ d, predecessor p d = some p := by
  rcases p with ⟨i, j⟩
  rintro ⟨d, hd⟩
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    fin_cases d <;> simp_all [predecessor, Prod.mk.injEq] <;> omega

/-- The ordinary simple graph on the quadrant with the paper's four displacements. -/
def quadrantGraph : SimpleGraph Point where
  Adj p q := ∃ d, predecessor p d = some q
  symm := ⟨fun _ _ => predecessor_symmetric⟩
  loopless := ⟨predecessor_irreflexive⟩

noncomputable def directionOfAdj {p q : Point} (h : quadrantGraph.Adj p q) : Fin 4 :=
  Classical.choose h

theorem predecessor_directionOfAdj {p q : Point} (h : quadrantGraph.Adj p q) :
    predecessor p (directionOfAdj h) = some q := Classical.choose_spec h

@[simp] theorem directionOfAdj_mk {p q : Point} (d : Fin 4)
    (hd : predecessor p d = some q) :
    directionOfAdj (show quadrantGraph.Adj p q from ⟨d, hd⟩) = d :=
  predecessor_unique (predecessor_directionOfAdj _) hd

/-- Read a legal direction word as an ordinary graph walk, from its endpoint back
to the corner. -/
noncomputable def toGraphWalk : (w : List (Fin 4)) → (p : Point) →
    IsWalk w p → quadrantGraph.Walk p (0, 0)
  | [], p, h => by cases h; exact .nil
  | d :: w, p, h =>
      match hp : predecessor p d with
      | none => False.elim (by
          obtain ⟨q, hq, _⟩ := h
          rw [hp] at hq
          cases hq)
      | some q => .cons ⟨d, hp⟩ (toGraphWalk w q (by
          obtain ⟨q', hq', hw⟩ := h
          have heq : q = q' := Option.some.inj (hp.symm.trans hq')
          subst q'
          exact hw))

@[simp] theorem toGraphWalk_cons (d : Fin 4) (w : List (Fin 4)) (p q : Point)
    (hp : predecessor p d = some q) (hw : IsWalk w q) :
    toGraphWalk (d :: w) p ⟨q, hp, hw⟩ =
      SimpleGraph.Walk.cons (show quadrantGraph.Adj p q from ⟨d, hp⟩)
        (toGraphWalk w q hw) := by
  simp only [toGraphWalk]
  split
  · rename_i hn
    rw [hp] at hn
    cases hn
  · rename_i q' hq'
    have heq : q' = q := Option.some.inj (hq'.symm.trans hp)
    subst q'
    rfl

theorem toGraphWalk_length (w : List (Fin 4)) (p : Point) (h : IsWalk w p) :
    (toGraphWalk w p h).length = w.length := by
  induction w generalizing p with
  | nil => cases h; rfl
  | cons d w ih =>
      obtain ⟨q, hp, hw⟩ := h
      rw [toGraphWalk_cons d w p q hp hw]
      simpa only [SimpleGraph.Walk.length_cons, List.length_cons] using
        congrArg (fun n : ℕ => n + 1) (ih q hw)

/-- Recover each direction from an ordinary graph walk; uniqueness follows from the
four different displacement vectors. -/
noncomputable def graphWord {p q : Point} : quadrantGraph.Walk p q → List (Fin 4)
  | .nil => []
  | .cons h w => directionOfAdj h :: graphWord w

theorem graphWord_length {p q : Point} (w : quadrantGraph.Walk p q) :
    (graphWord w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [graphWord, ih]

theorem graphWord_isWalk : {p : Point} → (w : quadrantGraph.Walk p (0, 0)) →
    IsWalk (graphWord w) p
  | _, .nil => rfl
  | _, .cons h w => ⟨_, predecessor_directionOfAdj h, graphWord_isWalk w⟩

theorem graphWord_toGraphWalk (w : List (Fin 4)) (p : Point) (h : IsWalk w p) :
    graphWord (toGraphWalk w p h) = w := by
  induction w generalizing p with
  | nil => cases h; rfl
  | cons d w ih =>
      obtain ⟨q, hp, hw⟩ := h
      rw [toGraphWalk_cons d w p q hp hw]
      simp only [graphWord, List.cons.injEq]
      constructor
      · exact predecessor_unique (predecessor_directionOfAdj _) hp
      · exact ih q hw

theorem toGraphWalk_graphWord : {p : Point} → (w : quadrantGraph.Walk p (0, 0)) →
    toGraphWalk (graphWord w) p (graphWord_isWalk w) = w
  | _, .nil => rfl
  | _, .cons h w => by
      change toGraphWalk (directionOfAdj h :: graphWord w) _ _ = _
      rw [toGraphWalk_cons (directionOfAdj h) (graphWord w) _ _
        (predecessor_directionOfAdj h) (graphWord_isWalk w), toGraphWalk_graphWord w]

/-- The counted finite direction words are exactly the usual fixed-length graph walks. -/
noncomputable def wordsGraphWalkEquiv (n : ℕ) (p : Point) :
    {w // w ∈ words n p} ≃ {w : quadrantGraph.Walk p (0, 0) // w.length = n} where
  toFun w :=
    ⟨toGraphWalk w.val p ((mem_words n p w.val).1 w.property).2,
      by rw [toGraphWalk_length]; exact ((mem_words n p w.val).1 w.property).1⟩
  invFun w :=
    ⟨graphWord w.val, (mem_words n p _).2
      ⟨by rw [graphWord_length, w.property], graphWord_isWalk w.val⟩⟩
  left_inv w := by apply Subtype.ext; exact graphWord_toGraphWalk _ _ _
  right_inv w := by apply Subtype.ext; exact toGraphWalk_graphWord _

/-- The recurrence counts ordinary graph walks, with no labelling multiplicity. -/
theorem natCard_graphWalk (n : ℕ) (p : Point) :
    Nat.card {w : quadrantGraph.Walk p (0, 0) // w.length = n} = count n p := by
  letI : Fintype {w // w ∈ words n p} := Finset.fintypeCoeSort (words n p)
  calc
    _ = Nat.card {w // w ∈ words n p} := Nat.card_congr (wordsGraphWalkEquiv n p).symm
    _ = (words n p).card := by simp [Nat.card_eq_fintype_card]
    _ = count n p := card_words n p

end TranscendentalTuran.Green.Walks
