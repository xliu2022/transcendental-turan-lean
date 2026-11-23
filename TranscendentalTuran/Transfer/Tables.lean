/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Push

/-!
# Exact two-dimensional fibre lemmas for factor recovery

All statements concern actual functions and their equal-value fibres.
The separation condition is supplied, in the graph application, by pair
coverage of the cores and edge preservation of the product homomorphism.
-/

@[expose] public section

namespace TranscendentalTuran.Transfer

universe u v w z
variable {A : Type u} {B : Type v} {C : Type w} {V : Type z}

def SeparatedTable (f : A → B → C) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' → f a b ≠ f a' b'

theorem same_colour_row_or_column {f : A → B → C} (hf : SeparatedTable f)
    {a a' : A} {b b' : B} (h : f a b = f a' b') : a = a' ∨ b = b' := by
  by_cases ha : a = a'
  · exact Or.inl ha
  · right
    by_contra hb
    exact hf a a' b b' ha hb h

theorem fibre_in_row_of_two_columns {f : A → B → C} (hf : SeparatedTable f)
    {c : C} {a : A} {b b' : B} (hbb' : b ≠ b')
    (hb : f a b = c) (hb' : f a b' = c) :
    ∀ x y, f x y = c → x = a := by
  intro x y hxy
  by_contra hxa
  have hyb : y = b :=
    (same_colour_row_or_column hf (hxy.trans hb.symm)).resolve_left hxa
  have hyb' : y = b' :=
    (same_colour_row_or_column hf (hxy.trans hb'.symm)).resolve_left hxa
  exact hbb' (hyb.symm.trans hyb')

theorem fibre_in_column_of_two_rows {f : A → B → C} (hf : SeparatedTable f)
    {c : C} {a a' : A} {b : B} (haa' : a ≠ a')
    (ha : f a b = c) (ha' : f a' b = c) :
    ∀ x y, f x y = c → y = b := by
  intro x y hxy
  by_contra hyb
  have hxa : x = a :=
    (same_colour_row_or_column hf (hxy.trans ha.symm)).resolve_right hyb
  have hxa' : x = a' :=
    (same_colour_row_or_column hf (hxy.trans ha'.symm)).resolve_right hyb
  exact haa' (hxa.symm.trans hxa')

/-- Every nonempty fibre is contained in a row or in a column. -/
theorem fibre_in_row_or_column {f : A → B → C} (hf : SeparatedTable f)
    {c : C} (hc : ∃ a b, f a b = c) :
    (∃ a, ∀ x y, f x y = c → x = a) ∨
      (∃ b, ∀ x y, f x y = c → y = b) := by
  classical
  obtain ⟨a, b, hab⟩ := hc
  by_cases hrow : ∀ x y, f x y = c → x = a
  · exact Or.inl ⟨a, hrow⟩
  · push Not at hrow
    obtain ⟨a', b', hab', hne⟩ := hrow
    have hbb' : b' = b :=
      (same_colour_row_or_column hf (hab'.trans hab.symm)).resolve_left hne
    subst b'
    exact Or.inr ⟨b, fibre_in_column_of_two_rows hf hne hab' hab⟩

/-- Two distinct occurrences make the direction of a supported fibre unique. -/
theorem row_column_fibre_singleton {f : A → B → C} {c : C}
    {a : A} {b : B}
    (hrow : ∀ x y, f x y = c → x = a)
    (hcol : ∀ x y, f x y = c → y = b)
    {x x' : A} {y y' : B} (hxy : f x y = c) (hxy' : f x' y' = c) :
    (x, y) = (x', y') := by
  exact Prod.ext ((hrow x y hxy).trans (hrow x' y' hxy').symm)
    ((hcol x y hxy).trans (hcol x' y' hxy').symm)

/-- A finite sequence which changes truth value has an adjacent change.
No monotonicity assumption is made. -/
theorem exists_adjacent_change (p : ℕ → Prop) (hzero : ¬ p 0)
    {d : ℕ} (hd : p d) : ∃ k, k < d ∧ ¬ p k ∧ p (k + 1) := by
  induction d with
  | zero => exact (hzero hd).elim
  | succ d ih =>
      by_cases hpd : p d
      · obtain ⟨k, hkd, hk, hk'⟩ := ih hpd
        exact ⟨k, Nat.lt_trans hkd (Nat.lt_succ_self d), hk, hk'⟩
      · exact ⟨d, Nat.lt_succ_self d, hpd, hd⟩

theorem two_occurrences_avoid {f : A → C} {a b : A} {c : C}
    (hab : a ≠ b) (ha : f a = c) (hb : f b = c) (avoid : A) :
    ∃ x, x ≠ avoid ∧ f x = c := by
  by_cases h : a = avoid
  · exact ⟨b, fun he => hab (h.trans he.symm), hb⟩
  · exact ⟨a, h, ha⟩

/-- The row and column anchors of a common dominant colour coincide. -/
theorem common_colour_anchors_eq (guard : A → V) (hguard : Function.Injective guard)
    (Φ : A → V → A → C)
    (hsep : ∀ a a' v v' b b', a ≠ a' → v ≠ v' → b ≠ b' →
      Φ a v b ≠ Φ a' v' b')
    {c : C} {r s y₀ y₁ x₀ x₁ : A}
    (hy : y₀ ≠ y₁) (hy₀ : Φ r (guard r) y₀ = c) (hy₁ : Φ r (guard r) y₁ = c)
    (hx : x₀ ≠ x₁) (hx₀ : Φ x₀ (guard s) s = c) (hx₁ : Φ x₁ (guard s) s = c) :
    r = s := by
  by_contra hrs
  obtain ⟨y, hys, hyc⟩ := two_occurrences_avoid hy hy₀ hy₁ s
  obtain ⟨x, hxr, hxc⟩ :=
    two_occurrences_avoid (f := fun x => Φ x (guard s) s) hx hx₀ hx₁ r
  exact hsep r x (guard r) (guard s) y s (Ne.symm hxr)
    (fun h => hrs (hguard h)) hys (hyc.trans hxc.symm)

/-- A common dominant colour has only one core vertex as an original
preimage across all cyclic-shift profiles. Repeated indices at that same
core vertex are permitted. -/
theorem common_colour_profile_preimage (guard : A → V)
    (hguard : Function.Injective guard) (Φ : A → V → A → C)
    (hsep : ∀ a a' v v' b b', a ≠ a' → v ≠ v' → b ≠ b' →
      Φ a v b ≠ Φ a' v' b')
    (σ : A → A) (hσ : ∀ a, σ a ≠ a)
    {c : C} {r s y₀ y₁ x₀ x₁ : A}
    (hy : y₀ ≠ y₁) (hy₀ : Φ r (guard r) y₀ = c) (hy₁ : Φ r (guard r) y₁ = c)
    (hx : x₀ ≠ x₁) (hx₀ : Φ x₀ (guard s) s = c) (hx₁ : Φ x₁ (guard s) s = c)
    {a : A} {v : V} (hav : Φ a v (σ a) = c) : v = guard r := by
  have hrs := common_colour_anchors_eq guard hguard Φ hsep hy hy₀ hy₁ hx hx₀ hx₁
  subst s
  by_contra hvr
  obtain ⟨y, hya, hyc⟩ := two_occurrences_avoid hy hy₀ hy₁ (σ a)
  have har : a = r := by
    by_contra har
    exact hsep a r v (guard r) (σ a) y har hvr (Ne.symm hya)
      (hav.trans hyc.symm)
  obtain ⟨x, hxa, hxc⟩ :=
    two_occurrences_avoid (f := fun x => Φ x (guard r) r) hx hx₀ hx₁ a
  have hσar : σ a = r := by
    by_contra hσar
    exact hsep a x v (guard r) (σ a) r (Ne.symm hxa) hvr hσar
      (hav.trans hxc.symm)
  exact hσ a (hσar.trans har.symm)

end TranscendentalTuran.Transfer
