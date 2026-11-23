module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Grounded partial bijections and series composition

Formalization author and responsible maintainer: Xizhi Liu.

The defect includes both unmatched endpoint squares. Composition therefore
handles interrupted paths automatically, with no assumption that all ports
are occupied.
-/

namespace TranscendentalTuran.Network

open scoped BigOperators

structure PartialIso (A B : Type*) where
  forward : A → Option B
  backward : B → Option A
  reverse : ∀ a b, forward a = some b ↔ backward b = some a

namespace PartialIso

variable {A B C : Type*}

def symm (f : PartialIso A B) : PartialIso B A :=
  ⟨f.backward, f.forward, fun b a => (f.reverse a b).symm⟩

def comp (f : PartialIso A B) (g : PartialIso B C) : PartialIso A C where
  forward a := (f.forward a).bind g.forward
  backward c := (g.backward c).bind f.backward
  reverse a c := by
    simp only [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨b, hab, hbc⟩
      exact ⟨b, (g.reverse b c).mp hbc, (f.reverse a b).mp hab⟩
    · rintro ⟨b, hcb, hba⟩
      exact ⟨b, (f.reverse a b).mpr hba, (g.reverse b c).mpr hcb⟩

def pull (f : PartialIso A B) (x : A → ℝ) : B → ℝ :=
  fun b => (f.backward b).elim 0 x

def push (f : PartialIso A B) (y : B → ℝ) : A → ℝ :=
  fun a => (f.forward a).elim 0 y

def normSq [Fintype A] (x : A → ℝ) : ℝ := ∑ a, x a ^ 2
def dot [Fintype A] (x y : A → ℝ) : ℝ := ∑ a, x a * y a

theorem dot_comm [Fintype A] (x y : A → ℝ) : dot x y = dot y x := by
  unfold dot
  simp only [mul_comm]

theorem dot_self [Fintype A] (x : A → ℝ) : dot x x = normSq x := by
  simp only [dot, normSq, pow_two]

def defect [Fintype A] [Fintype B] (f : PartialIso A B) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  normSq x + normSq y - 2 * dot x (f.push y)

theorem dot_push [Fintype A] [Fintype B] (f : PartialIso A B) (x : A → ℝ) (y : B → ℝ) :
    dot x (f.push y) = dot (f.pull x) y := by
  classical
  have hforward (a : A) : f.push y a = ∑ b, if f.forward a = some b then y b else 0 := by
    cases ha : f.forward a <;> simp [push, ha, eq_comm]
  have hbackward (b : B) : f.pull x b = ∑ a, if f.backward b = some a then x a else 0 := by
    cases hb : f.backward b <;> simp [pull, hb, eq_comm]
  unfold dot
  simp_rw [hforward, hbackward, Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  simp_rw [f.reverse]

theorem push_pull_eq [Fintype A] [Fintype B] (f : PartialIso A B) (x : A → ℝ) (a : A) :
    f.push (f.pull x) a = if f.forward a = none then 0 else x a := by
  cases ha : f.forward a with
  | none => simp [push, ha]
  | some b => simp [push, pull, ha, (f.reverse a b).mp ha]

theorem pull_normSq_le [Fintype A] [Fintype B] (f : PartialIso A B) (x : A → ℝ) :
    normSq (f.pull x) ≤ normSq x := by
  classical
  rw [← dot_self, ← f.dot_push]
  unfold dot normSq
  apply Finset.sum_le_sum
  intro a _
  rw [f.push_pull_eq]
  split_ifs <;> nlinarith [sq_nonneg (x a)]

theorem push_normSq_le [Fintype A] [Fintype B] (f : PartialIso A B) (y : B → ℝ) :
    normSq (f.push y) ≤ normSq y := f.symm.pull_normSq_le y

theorem comp_push (f : PartialIso A B) (g : PartialIso B C) (z : C → ℝ) :
    (f.comp g).push z = f.push (g.push z) := by
  funext a
  cases h : f.forward a <;> simp [push, comp, h]

theorem comp_dot [Fintype A] [Fintype B] (f : PartialIso A B) (g : PartialIso B C)
    (x : A → ℝ) (z : C → ℝ) :
    dot x ((f.comp g).push z) = dot (f.pull x) (g.push z) := by
  rw [comp_push, f.dot_push]

/-- The weighted two-segment inequality before division. -/
theorem compose_defect_mul [Fintype A] [Fintype B] [Fintype C]
    (f : PartialIso A B) (g : PartialIso B C) (x : A → ℝ) (y : B → ℝ) (z : C → ℝ)
    (u v : ℝ) :
    u * v * (f.comp g).defect x z ≤ (u + v) * (u * f.defect x y + v * g.defect y z) := by
  let a := f.pull x
  let b := g.push z
  have ha : normSq a ≤ normSq x := f.pull_normSq_le x
  have hb : normSq b ≤ normSq z := g.push_normSq_le z
  have hs : 0 ≤ ∑ i : B, (u * a i + v * b i - (u + v) * y i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hex : (∑ i : B, (u * a i + v * b i - (u + v) * y i) ^ 2) =
      u ^ 2 * normSq a + v ^ 2 * normSq b + (u + v) ^ 2 * normSq y +
      2 * u * v * dot a b - 2 * u * (u + v) * dot a y - 2 * v * (u + v) * dot y b := by
    unfold normSq dot
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hex] at hs
  have hax := mul_le_mul_of_nonneg_left ha (sq_nonneg u)
  have hbx := mul_le_mul_of_nonneg_left hb (sq_nonneg v)
  unfold defect
  rw [f.dot_push, comp_dot]
  change u * v * (normSq x + normSq z - 2 * dot a b) ≤
    (u + v) * (u * (normSq x + normSq y - 2 * dot a y) +
      v * (normSq y + normSq z - 2 * dot y b))
  nlinarith

/-- Series reduction remains valid at all missing ports. -/
theorem compose_defect [Fintype A] [Fintype B] [Fintype C]
    (f : PartialIso A B) (g : PartialIso B C) (x : A → ℝ) (y : B → ℝ) (z : C → ℝ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (u * v / (u + v)) * (f.comp g).defect x z ≤ u * f.defect x y + v * g.defect y z := by
  have hs : 0 < u + v := add_pos hu hv
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hs).mpr
  simpa only [mul_comm] using compose_defect_mul f g x y z u v

end PartialIso
end TranscendentalTuran.Network
