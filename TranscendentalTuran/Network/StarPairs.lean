module

public import TranscendentalTuran.Network.StarEnergy

@[expose] public section

/-!
# Actual permitted pairs of a signed star family

Formalization author and responsible maintainer: Xizhi Liu.

The permitted-pair formula is related here to a concrete symmetric relation,
including the exclusion of two leaves with the same assigned center.
-/

namespace TranscendentalTuran.Network.StarEnergy

open scoped BigOperators

variable {C B : Type*} [Fintype C] [Fintype B] [DecidableEq C] [DecidableEq B]

def SameStar (f : B → Option C) (b d : B) : Prop :=
  ∃ c, f b = some c ∧ f d = some c

instance (f : B → Option C) (b d : B) : Decidable (SameStar f b d) :=
  inferInstanceAs (Decidable (∃ c, f b = some c ∧ f d = some c))

def PermittedPair (f : B → Option C) : C ⊕ B → C ⊕ B → Prop
  | .inl c, .inl d => c ≠ d
  | .inl c, .inr b => f b = some c
  | .inr b, .inl c => f b = some c
  | .inr b, .inr d => b ≠ d ∧ ¬ SameStar f b d

instance (f : B → Option C) (a b : C ⊕ B) : Decidable (PermittedPair f a b) := by
  cases a <;> cases b <;> unfold PermittedPair <;> infer_instance

theorem ordered_distinct_sum {A : Type*} [Fintype A] [DecidableEq A] (w : A → ℝ) :
    (∑ a, ∑ b, if a ≠ b then w a * w b else 0) =
      (∑ a, w a) ^ 2 - ∑ a, w a ^ 2 := by
  have hi (a b : A) : (if a ≠ b then w a * w b else 0) =
      w a * w b - if a = b then w a ^ 2 else 0 := by
    by_cases h : a = b <;> simp [h, pow_two]
  simp_rw [hi, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul_sum]
  ring

theorem sameStar_indicator (f : B → Option C) (b d : B) (v : ℝ) :
    (if SameStar f b d then v else 0) =
      ∑ c, if f b = some c ∧ f d = some c then v else 0 := by
  cases hb : f b with
  | none => simp [SameStar, hb]
  | some c =>
    cases hd : f d with
    | none => simp [SameStar, hd]
    | some c' =>
      by_cases h : c = c'
      · subst c'; simp [SameStar, hb, hd]
      · have hboth (a : C) : ¬ (c = a ∧ c' = a) :=
          fun ha => h (ha.1.trans ha.2.symm)
        simp [SameStar, hb, hd, h, hboth]

theorem within_star_ordered_sum (f : B → Option C) (y : B → ℝ) :
    (∑ b, ∑ d, if b ≠ d ∧ SameStar f b d then y b * y d else 0) =
      2 * ∑ c, fiberPairs f y c := by
  have hp (b d : B) : (if b ≠ d ∧ SameStar f b d then y b * y d else 0) =
      ∑ c, if b ≠ d ∧ f b = some c ∧ f d = some c then y b * y d else 0 := by
    by_cases hbd : b = d
    · subst d; simp
    · simpa [hbd] using sameStar_indicator f b d (y b * y d)
  simp_rw [hp]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  let w : B → ℝ := fun b => if f b = some c then y b else 0
  have hw : (∑ b, ∑ d, if b ≠ d ∧ f b = some c ∧ f d = some c then y b * y d else 0) =
      ∑ b, ∑ d, if b ≠ d then w b * w d else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    dsimp [w]
    split_ifs <;> simp_all
  rw [hw, ordered_distinct_sum]
  have hsq : (∑ b, w b ^ 2) = fiberSquareMass f y c := by
    apply Finset.sum_congr rfl
    intro b _
    simp only [w, fiberSquareMass]
    split_ifs <;> simp
  rw [hsq]
  change fiberMass f y c ^ 2 - fiberSquareMass f y c = 2 * fiberPairs f y c
  unfold fiberPairs
  ring

theorem leaf_allowed_ordered_sum (f : B → Option C) (y : B → ℝ) :
    (∑ b, ∑ d, if b ≠ d ∧ ¬ SameStar f b d then y b * y d else 0) =
      2 * completePairs y - 2 * (∑ c, fiberPairs f y c) := by
  have hi (b d : B) :
      (if b ≠ d ∧ ¬ SameStar f b d then y b * y d else 0) =
      (if b ≠ d then y b * y d else 0) -
        (if b ≠ d ∧ SameStar f b d then y b * y d else 0) := by
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_sub_distrib]
  rw [ordered_distinct_sum, within_star_ordered_sum]
  unfold completePairs
  ring

theorem permitted_ordered_sum (f : B → Option C) (x : C → ℝ) (y : B → ℝ) :
    (∑ a : C ⊕ B, ∑ b : C ⊕ B,
      if PermittedPair f a b then Sum.elim x y a * Sum.elim x y b else 0) =
      2 * permittedPairWeight f x y := by
  simp only [Fintype.sum_sum_type, PermittedPair, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib]
  rw [ordered_distinct_sum, leaf_allowed_ordered_sum]
  have hcross : (∑ c, ∑ b, if f b = some c then x c * y b else 0) =
      ∑ c, x c * fiberMass f y c := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [fiberMass, Finset.mul_sum, mul_ite, mul_zero]
  have hreverse : (∑ b, ∑ c, if f b = some c then y b * x c else 0) =
      ∑ c, x c * fiberMass f y c := by
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hcross
  rw [hcross, hreverse]
  unfold permittedPairWeight completePairs
  ring

end TranscendentalTuran.Network.StarEnergy
