module

public import TranscendentalTuran.Network.PartialIsoRelation
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Reindexing and partitioning a partial-matching energy

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Network

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A B C D A' B' : Type*}

noncomputable def relationEnergy [Fintype A] [Fintype B]
    (R : A → B → Prop) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  (∑ a, x a ^ 2) + (∑ b, y b ^ 2) -
    2 * ∑ a, ∑ b, if R a b then x a * y b else 0

theorem PartialIso.ofRel_defect [Fintype A] [Fintype B]
    (R : A → B → Prop) (hf hb) (x : A → ℝ) (y : B → ℝ) :
    (PartialIso.ofRel R hf hb).defect x y = relationEnergy R x y := by
  rw [PartialIso.defect, PartialIso.ofRel_dot]
  rfl

theorem relationEnergy_reindex [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (e : A' ≃ A) (f : B' ≃ B) (R : A → B → Prop) (x : A → ℝ) (y : B → ℝ) :
    relationEnergy (fun a b => R (e a) (f b)) (fun a => x (e a)) (fun b => y (f b)) =
      relationEnergy R x y := by
  have hc : (∑ a : A', ∑ b : B', if R (e a) (f b) then x (e a) * y (f b) else 0) =
      ∑ a : A, ∑ b : B, if R a b then x a * y b else 0 := by
    calc
      _ = ∑ a : A', ∑ b : B, if R (e a) b then x (e a) * y b else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        exact f.sum_comp (fun b : B => if R (e a) b then x (e a) * y b else 0)
      _ = _ := e.sum_comp (fun a : A => ∑ b : B, if R a b then x a * y b else 0)
  unfold relationEnergy
  rw [e.sum_comp (fun a => x a ^ 2), f.sum_comp (fun b => y b ^ 2), hc]

theorem relationEnergy_congr [Fintype A] [Fintype B] {R S : A → B → Prop}
    (h : ∀ a b, R a b ↔ S a b) (x : A → ℝ) (y : B → ℝ) :
    relationEnergy R x y = relationEnergy S x y := by
  simp only [relationEnergy, h]

theorem relationEnergy_symm [Fintype A] [Fintype B]
    (R : A → B → Prop) (x : A → ℝ) (y : B → ℝ) :
    relationEnergy (fun b a => R a b) y x = relationEnergy R x y := by
  unfold relationEnergy
  rw [Finset.sum_comm (f := fun b a => if R a b then y b * x a else 0)]
  simp only [mul_comm (y _)]
  ring

theorem relationEnergy_sum [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (R : (A ⊕ C) → (B ⊕ D) → Prop) (x : A → ℝ) (y : B → ℝ)
    (z : C → ℝ) (t : D → ℝ)
    (h₀ : ∀ a d, ¬ R (.inl a) (.inr d))
    (h₁ : ∀ c b, ¬ R (.inr c) (.inl b)) :
    relationEnergy R (Sum.elim x z) (Sum.elim y t) =
      relationEnergy (fun a b => R (.inl a) (.inl b)) x y +
      relationEnergy (fun c d => R (.inr c) (.inr d)) z t := by
  unfold relationEnergy
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h₀, h₁,
    if_false, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem PartialIso.defect_symm [Fintype A] [Fintype B]
    (f : PartialIso A B) (x : A → ℝ) (y : B → ℝ) :
    f.symm.defect y x = f.defect x y := by
  unfold PartialIso.defect
  change PartialIso.normSq y + PartialIso.normSq x -
    2 * PartialIso.dot y (f.pull x) = _
  rw [PartialIso.dot_comm, ← f.dot_push]
  ring

theorem relationEnergy_sum_any [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (R : (A ⊕ C) → (B ⊕ D) → Prop) (x : A ⊕ C → ℝ) (y : B ⊕ D → ℝ)
    (h₀ : ∀ a d, ¬ R (.inl a) (.inr d))
    (h₁ : ∀ c b, ¬ R (.inr c) (.inl b)) :
    relationEnergy R x y =
      relationEnergy (fun a b => R (.inl a) (.inl b))
        (fun a => x (.inl a)) (fun b => y (.inl b)) +
      relationEnergy (fun c d => R (.inr c) (.inr d))
        (fun c => x (.inr c)) (fun d => y (.inr d)) := by
  unfold relationEnergy
  simp only [Fintype.sum_sum_type, h₀, h₁, ite_false,
    Finset.sum_const_zero, add_zero, zero_add]
  ring

end TranscendentalTuran.Network
