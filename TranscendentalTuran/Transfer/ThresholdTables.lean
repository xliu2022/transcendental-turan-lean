/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TranscendentalTuran.Transfer.Tables
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic
public import Lean.Elab.Tactic.Omega

/-!
# The actual threshold tables of a finite product map

This file constructs `F_k(x,y) = φ(x^k,y^(d-k))`, including both endpoints,
and the three-argument map used at an adjacent direction switch. The factors
may have different vertex types; a common guard is supplied by injections.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

universe u v w
variable {d : ℕ} {A : Type u} {T : Type w} {V : Fin d → Type v}

def SeparatesCoordinates (ψ : ((i : Fin d) → V i) → T) : Prop :=
  ∀ x y, (∀ i, x i ≠ y i) → ψ x ≠ ψ y

def thresholdTuple (guard : (i : Fin d) → A → V i) (k : ℕ) (a b : A) :
    (i : Fin d) → V i :=
  fun i => if i.val < k then guard i a else guard i b

def thresholdTable (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (k : ℕ) (a b : A) : T :=
  ψ (thresholdTuple guard k a b)

theorem thresholdTable_separated (ψ : ((i : Fin d) → V i) → T)
    (hψ : SeparatesCoordinates ψ) (guard : (i : Fin d) → A → V i)
    (hguard : ∀ i, Function.Injective (guard i)) (k : ℕ) :
    SeparatedTable (thresholdTable ψ guard k) := by
  intro a a' b b' haa' hbb'
  apply hψ
  intro i
  dsimp [thresholdTuple]
  by_cases hi : i.val < k
  · simp only [hi, ite_true]
    exact fun h => haa' (hguard i h)
  · simp only [hi, ite_false]
    exact fun h => hbb' (hguard i h)

@[simp] theorem thresholdTable_zero (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (a b : A) :
    thresholdTable ψ guard 0 a b = ψ (fun i => guard i b) := by
  rfl

@[simp] theorem thresholdTable_last (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (a b : A) :
    thresholdTable ψ guard d a b = ψ (fun i => guard i a) := by
  unfold thresholdTable
  congr 1
  funext i
  simp [thresholdTuple, i.isLt]

theorem diagonal_injective (ψ : ((i : Fin d) → V i) → T)
    (hψ : SeparatesCoordinates ψ) (guard : (i : Fin d) → A → V i)
    (hguard : ∀ i, Function.Injective (guard i)) :
    Function.Injective (fun a => ψ (fun i => guard i a)) := by
  intro a b hab
  by_contra hne
  exact hψ _ _ (fun i h => hne (hguard i h)) hab

/-- A coordinate replacement isolates the factor at an adjacent switch.
Only the distinguished factor has an arbitrary core vertex. -/
def switchMap (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (j : Fin d) (a : A) (v : V j) (b : A) : T :=
  ψ (Function.update (thresholdTuple guard j.val a b) j v)

theorem switchMap_separates (ψ : ((i : Fin d) → V i) → T)
    (hψ : SeparatesCoordinates ψ) (guard : (i : Fin d) → A → V i)
    (hguard : ∀ i, Function.Injective (guard i)) (j : Fin d) :
    ∀ a a' v v' b b', a ≠ a' → v ≠ v' → b ≠ b' →
      switchMap ψ guard j a v b ≠ switchMap ψ guard j a' v' b' := by
  intro a a' v v' b b' haa' hvv' hbb'
  apply hψ
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hvv'
  · simp only [Function.update_of_ne hij]
    dsimp [thresholdTuple]
    by_cases hi : i.val < j.val
    · simp only [hi, ite_true]
      exact fun h => haa' (hguard i h)
    · simp only [hi, ite_false]
      exact fun h => hbb' (hguard i h)

theorem switchMap_right (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (j : Fin d) (a b : A) :
    switchMap ψ guard j a (guard j b) b = thresholdTable ψ guard j.val a b := by
  unfold switchMap thresholdTable
  congr 1
  funext i
  by_cases hij : i = j
  · subst i
    simp [thresholdTuple]
  · simp [Function.update_of_ne hij]

theorem switchMap_left (ψ : ((i : Fin d) → V i) → T)
    (guard : (i : Fin d) → A → V i) (j : Fin d) (a b : A) :
    switchMap ψ guard j a (guard j a) b = thresholdTable ψ guard (j.val + 1) a b := by
  unfold switchMap thresholdTable
  congr 1
  funext i
  by_cases hij : i = j
  · subst i
    simp [thresholdTuple]
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi : (i.val < j.val + 1) = (i.val < j.val) := by
      apply propext
      omega
    simp [Function.update_of_ne hij, thresholdTuple, hi]

/-- A fixed-point-free shift is needed later for anchor exclusion; its
injectivity already gives row/column separation of the profile table. -/
theorem switch_profiles_separated (ψ : ((i : Fin d) → V i) → T)
    (hψ : SeparatesCoordinates ψ) (guard : (i : Fin d) → A → V i)
    (hguard : ∀ i, Function.Injective (guard i)) (j : Fin d)
    (σ : A → A) (hσ : Function.Injective σ) :
    SeparatedTable (fun a v => switchMap ψ guard j a v (σ a)) := by
  intro a a' v v' haa' hvv'
  exact switchMap_separates ψ hψ guard hguard j a a' v v' (σ a) (σ a')
    haa' hvv' (fun h => haa' (hσ h))

end TranscendentalTuran.Transfer
