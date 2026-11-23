/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Walks.Determinant
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fintype.Sets

@[expose] public section

open Finset DyckStep

namespace TranscendentalTuran.Green.Walks

/-- A one-dimensional direction word stays strictly positive and takes initial
height `b` to final height `a`. -/
def PositiveWord (b : ℕ) (w : List DyckStep) (a : ℕ) : Prop :=
  b + w.count U = a + w.count D ∧
    ∀ k, (w.take k).count D < b + (w.take k).count U

@[simp] theorem positiveWord_nil (a b : ℕ) :
    PositiveWord b [] a ↔ a = b ∧ b ≠ 0 := by
  simp [PositiveWord, eq_comm, Nat.pos_iff_ne_zero]

theorem positiveWord_cons_U (a b : ℕ) (w : List DyckStep) :
    PositiveWord b (U :: w) a ↔ b ≠ 0 ∧ PositiveWord (b + 1) w a := by
  constructor
  · rintro ⟨he, hp⟩
    have hb := hp 0
    simp at hb
    refine ⟨by omega, ?_, ?_⟩
    · simp at he
      omega
    · intro k
      have h := hp (k + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · rintro ⟨hb, he, hp⟩
    constructor
    · simp
      omega
    · intro k
      cases k with
      | zero => simp; omega
      | succ k =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp k

theorem positiveWord_cons_D (a b : ℕ) (w : List DyckStep) :
    PositiveWord b (D :: w) a ↔ b ≠ 0 ∧ PositiveWord (b - 1) w a := by
  constructor
  · rintro ⟨he, hp⟩
    have hb := hp 0
    simp at hb
    refine ⟨by omega, ?_, ?_⟩
    · simp at he
      omega
    · intro k
      have h := hp (k + 1)
      simp at h
      omega
  · rintro ⟨hb, he, hp⟩
    constructor
    · simp
      omega
    · intro k
      cases k with
      | zero => simp; omega
      | succ k =>
          have h := hp k
          simp
          omega

/-- The finite family of positive walks.  Reading these words starts at the second
endpoint, which agrees with the endpoint recurrence defining `lineCount`. -/
def lineWords : ℕ → ℕ → ℕ → Finset (List DyckStep)
  | 0, a, b => if a = b ∧ b ≠ 0 then {[]} else ∅
  | n + 1, a, b => if b = 0 then ∅ else
      ((lineWords n a (b + 1)).image (List.cons U)) ∪
        ((lineWords n a (b - 1)).image (List.cons D))

private theorem UD_images_disjoint (s t : Finset (List DyckStep)) :
    Disjoint (s.image (List.cons U)) (t.image (List.cons D)) := by
  apply Finset.disjoint_left.mpr
  intro w hw₁ hw₂
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw₁
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hw₂
  cases hv

theorem card_lineWords (n a b : ℕ) : (lineWords n a b).card = lineCount n a b := by
  induction n generalizing a b with
  | zero =>
      by_cases h : a = b ∧ b ≠ 0 <;> simp [lineWords, lineCount, h]
  | succ n ih =>
      by_cases hb : b = 0
      · simp [lineWords, lineCount, hb]
      · rw [lineWords, if_neg hb, Finset.card_union_of_disjoint (UD_images_disjoint _ _)]
        rw [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
          Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih, ih]
        simp [lineCount, hb, Nat.add_comm]

theorem mem_lineWords (n a b : ℕ) (w : List DyckStep) :
    w ∈ lineWords n a b ↔ w.length = n ∧ PositiveWord b w a := by
  induction n generalizing a b w with
  | zero =>
      by_cases h : a = b ∧ b ≠ 0 <;> cases w <;> simp [lineWords, h]
  | succ n ih =>
      by_cases hb : b = 0
      · subst b
        have hn : ¬PositiveWord 0 w a := by
          rintro ⟨_, hp⟩
          have h := hp 0
          simp at h
        simp [lineWords, hn]
      · cases w with
        | nil => simp [lineWords, hb]
        | cons s w =>
            cases s <;>
              simp [lineWords, hb, Finset.mem_image, ih,
                positiveWord_cons_U, positiveWord_cons_D]

/-- The concrete return-word family is equivalent to Mathlib's Dyck words. -/
def returnWordsEquiv (n : ℕ) :
    {w // w ∈ lineWords (2 * n) 1 1} ≃ {p : DyckWord // p.semilength = n} where
  toFun w := by
    obtain ⟨hlen, hbal, hpos⟩ := (mem_lineWords (2 * n) 1 1 w.val).1 w.property
    let p : DyckWord :=
      { toList := w.val
        count_U_eq_count_D := by omega
        count_D_le_count_U := fun k => by have h := hpos k; omega }
    refine ⟨p, ?_⟩
    have h := p.two_mul_semilength_eq_length
    change 2 * p.semilength = w.val.length at h
    omega
  invFun p := by
    refine ⟨p.val.toList, (mem_lineWords (2 * n) 1 1 p.val.toList).2 ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← p.val.two_mul_semilength_eq_length, p.property]
    · have h := p.val.count_U_eq_count_D
      omega
    · intro k
      have h := p.val.count_D_le_count_U k
      omega
  left_inv w := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; apply DyckWord.ext; rfl

/-- One positive walker returns from `1` to `1` in `2n` steps in exactly `Cₙ` ways. -/
theorem lineCount_even_one (n : ℕ) : lineCount (2 * n) 1 1 = catalan n := by
  letI : Fintype {w // w ∈ lineWords (2 * n) 1 1} :=
    Finset.fintypeCoeSort (lineWords (2 * n) 1 1)
  rw [← card_lineWords]
  calc
    _ = Fintype.card {w // w ∈ lineWords (2 * n) 1 1} := (Fintype.card_coe (lineWords (2 * n) 1 1)).symm
    _ = Fintype.card {p : DyckWord // p.semilength = n} :=
      Fintype.card_congr (returnWordsEquiv n)
    _ = catalan n := DyckWord.card_dyckWord_semilength_eq_catalan n

end TranscendentalTuran.Green.Walks
