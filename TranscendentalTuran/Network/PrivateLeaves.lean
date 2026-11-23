module

public import TranscendentalTuran.Network.PortEnergy
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# One private leaf for each exit port

Formalization author and responsible maintainer: Xizhi Liu.

The construction keeps a specified finite center set and replaces each
occupied port leaving that set by its own degree-one leaf. Targets are
remembered only to clone their weights; different exit ports always
receive different new leaves.
-/

namespace TranscendentalTuran.Network.PrivateLeaves

open Finset
open Green.FiniteNetwork
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Center (C : Finset V) := {v : V // v ∈ C}

abbrev Exit (N : DirectionalNetwork V) (C : Finset V) :=
  {e : Center C × Fin 4 × V // N.neighbor e.1.val e.2.1 = some e.2.2 ∧ e.2.2 ∉ C}

noncomputable instance (N : DirectionalNetwork V) (C : Finset V) : Fintype (Exit N C) :=
  Fintype.ofFinite _

namespace Exit

def center {N : DirectionalNetwork V} {C : Finset V} (e : Exit N C) : Center C := e.val.1
def port {N : DirectionalNetwork V} {C : Finset V} (e : Exit N C) : Fin 4 := e.val.2.1
def target {N : DirectionalNetwork V} {C : Finset V} (e : Exit N C) : V := e.val.2.2

theorem edge {N : DirectionalNetwork V} {C : Finset V} (e : Exit N C) :
    N.neighbor e.center.val e.port = some e.target := e.property.1

theorem outside {N : DirectionalNetwork V} {C : Finset V} (e : Exit N C) :
    e.target ∉ C := e.property.2

@[ext] theorem ext {N : DirectionalNetwork V} {C : Finset V} {e f : Exit N C}
    (hc : e.center = f.center) (hd : e.port = f.port) (ht : e.target = f.target) : e = f :=
  Subtype.ext (Prod.ext hc (Prod.ext hd ht))

end Exit

abbrev Vertex (N : DirectionalNetwork V) (C : Finset V) := Center C ⊕ Exit N C

def neighbor (N : DirectionalNetwork V) (C : Finset V) :
    Vertex N C → Fin 4 → Option (Vertex N C)
  | Sum.inl c, d =>
    match hn : N.neighbor c.val d with
    | none => none
    | some w =>
      if hw : w ∈ C then some (Sum.inl ⟨w, hw⟩)
      else some (Sum.inr ⟨(c, d, w), hn, hw⟩)
  | Sum.inr e, d =>
    if d = reverseDirection e.port then some (Sum.inl e.center) else none

theorem neighbor_center_none (N : DirectionalNetwork V) (C : Finset V)
    (c : Center C) (d : Fin 4) (hn : N.neighbor c.val d = none) :
    neighbor N C (Sum.inl c) d = none := by
  simp only [neighbor]
  split
  · rfl
  · rename_i w hw
    have hbad : some w = (none : Option V) := hw.symm.trans hn
    cases hbad

theorem neighbor_center_mem (N : DirectionalNetwork V) (C : Finset V)
    (c : Center C) (d : Fin 4) (w : V) (hn : N.neighbor c.val d = some w) (hw : w ∈ C) :
    neighbor N C (Sum.inl c) d = some (Sum.inl ⟨w, hw⟩) := by
  simp only [neighbor]
  split
  · rename_i hnone
    have hbad : (none : Option V) = some w := hnone.symm.trans hn
    cases hbad
  · rename_i w' hw'
    have he : w' = w := Option.some.inj (hw'.symm.trans hn)
    subst w'
    simp only [dif_pos hw]

theorem neighbor_center_exit (N : DirectionalNetwork V) (C : Finset V)
    (c : Center C) (d : Fin 4) (w : V) (hn : N.neighbor c.val d = some w) (hw : w ∉ C) :
    neighbor N C (Sum.inl c) d = some (Sum.inr ⟨(c, d, w), hn, hw⟩) := by
  simp only [neighbor]
  split
  · rename_i hnone
    have hbad : (none : Option V) = some w := hnone.symm.trans hn
    cases hbad
  · rename_i w' hw'
    have he : w' = w := Option.some.inj (hw'.symm.trans hn)
    subst w'
    simp only [dif_neg hw]

theorem neighbor_center_center_iff (N : DirectionalNetwork V) (C : Finset V)
    (c c' : Center C) (d : Fin 4) :
    neighbor N C (Sum.inl c) d = some (Sum.inl c') ↔
      N.neighbor c.val d = some c'.val := by
  constructor
  · intro h
    cases hn : N.neighbor c.val d with
    | none => rw [neighbor_center_none N C c d hn] at h; cases h
    | some w =>
      by_cases hw : w ∈ C
      · rw [neighbor_center_mem N C c d w hn hw] at h
        have he : (⟨w, hw⟩ : Center C) = c' := by simpa using h
        have hv := congrArg Subtype.val he
        exact congrArg Option.some hv
      · rw [neighbor_center_exit N C c d w hn hw] at h
        cases h
  · intro hn
    rcases c' with ⟨w, hw⟩
    exact neighbor_center_mem N C c d w hn hw

theorem neighbor_center_leaf_iff (N : DirectionalNetwork V) (C : Finset V)
    (c : Center C) (e : Exit N C) (d : Fin 4) :
    neighbor N C (Sum.inl c) d = some (Sum.inr e) ↔ c = e.center ∧ d = e.port := by
  constructor
  · intro h
    cases hn : N.neighbor c.val d with
    | none => rw [neighbor_center_none N C c d hn] at h; cases h
    | some w =>
      by_cases hw : w ∈ C
      · rw [neighbor_center_mem N C c d w hn hw] at h
        cases h
      · have he : (⟨(c, d, w), hn, hw⟩ : Exit N C) = e := by
          rw [neighbor_center_exit N C c d w hn hw] at h
          simpa using h
        exact ⟨congrArg Exit.center he, congrArg Exit.port he⟩
  · rintro ⟨rfl, rfl⟩
    rcases e with ⟨⟨c, d, w⟩, he, hw⟩
    exact neighbor_center_exit N C c d w he hw

theorem neighbor_leaf_center_iff (N : DirectionalNetwork V) (C : Finset V)
    (e : Exit N C) (c : Center C) (d : Fin 4) :
    neighbor N C (Sum.inr e) d = some (Sum.inl c) ↔
      d = reverseDirection e.port ∧ e.center = c := by
  by_cases hd : d = reverseDirection e.port <;> simp [neighbor, hd]

@[simp] theorem neighbor_leaf_leaf (N : DirectionalNetwork V) (C : Finset V)
    (e f : Exit N C) (d : Fin 4) :
    neighbor N C (Sum.inr e) d ≠ some (Sum.inr f) := by
  by_cases hd : d = reverseDirection e.port <;> simp [neighbor, hd]

theorem reverseDirection_injective : Function.Injective reverseDirection := by
  intro d e h
  have hh := congrArg reverseDirection h
  simpa only [reverseDirection_involutive] using hh

theorem neighbor_reverse (N : DirectionalNetwork V) (C : Finset V)
    (v w : Vertex N C) (d : Fin 4) :
    neighbor N C v d = some w ↔ neighbor N C w (reverseDirection d) = some v := by
  cases v with
  | inl c =>
    cases w with
    | inl c' =>
      rw [neighbor_center_center_iff, neighbor_center_center_iff]
      exact N.reverse_step c.val c'.val d
    | inr e =>
      rw [neighbor_center_leaf_iff, neighbor_leaf_center_iff]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨hd, hc⟩
        exact ⟨hc.symm, reverseDirection_injective hd⟩
  | inr e =>
    cases w with
    | inl c =>
      rw [neighbor_leaf_center_iff, neighbor_center_leaf_iff]
      constructor
      · rintro ⟨rfl, hc⟩
        exact ⟨hc.symm, reverseDirection_involutive _⟩
      · rintro ⟨hc, hd⟩
        have hh := congrArg reverseDirection hd
        exact ⟨by simpa only [reverseDirection_involutive] using hh, hc.symm⟩
    | inr f => simp

def network (N : DirectionalNetwork V) (C : Finset V) : DirectionalNetwork (Vertex N C) where
  neighbor := neighbor N C
  reverse_step := neighbor_reverse N C

def cloneWeight (N : DirectionalNetwork V) (C : Finset V) (x : V → ℝ) : Vertex N C → ℝ :=
  Sum.elim (fun c => x c.val) (fun e => x e.target)

theorem portEnergy_center (N : DirectionalNetwork V) (C : Finset V)
    (x : V → ℝ) (c : Center C) (d : Fin 4) :
    (network N C).portEnergy (cloneWeight N C x) (Sum.inl c) d = N.portEnergy x c.val d := by
  cases hn : N.neighbor c.val d with
  | none =>
    simp only [DirectionalNetwork.portEnergy, network]
    rw [neighbor_center_none N C c d hn, hn]
    rfl
  | some w =>
    by_cases hw : w ∈ C
    · simp only [DirectionalNetwork.portEnergy, network]
      rw [neighbor_center_mem N C c d w hn hw, hn]
      rfl
    · simp only [DirectionalNetwork.portEnergy, network]
      rw [neighbor_center_exit N C c d w hn hw]
      change (x c.val - x w) ^ 2 / 2 = _
      rw [hn]

private theorem sum_four_ite (d₀ : Fin 4) (a b : ℝ) :
    (∑ d : Fin 4, if d = d₀ then a else b) = a + 3 * b := by
  fin_cases d₀ <;> simp [Fin.sum_univ_succ] <;> ring

theorem portEnergy_leaf_sum (N : DirectionalNetwork V) (C : Finset V)
    (x : V → ℝ) (e : Exit N C) :
    (∑ d : Fin 4, (network N C).portEnergy (cloneWeight N C x) (Sum.inr e) d) =
      N.portEnergy x e.target (reverseDirection e.port) + 3 * x e.target ^ 2 := by
  have he (d : Fin 4) : (network N C).portEnergy (cloneWeight N C x) (Sum.inr e) d =
      if d = reverseDirection e.port then (x e.target - x e.center.val) ^ 2 / 2
        else x e.target ^ 2 := by
    by_cases hd : d = reverseDirection e.port <;>
      simp [DirectionalNetwork.portEnergy, network, neighbor, cloneWeight, hd]
  simp_rw [he]
  rw [sum_four_ite]
  have hr := (N.reverse_step e.center.val e.target e.port).mp e.edge
  simp only [DirectionalNetwork.portEnergy, hr]

theorem energy_clone_eq (N : DirectionalNetwork V) (C : Finset V) (x : V → ℝ) :
    (network N C).energy (cloneWeight N C x) =
      (∑ c : Center C, ∑ d : Fin 4, N.portEnergy x c.val d) +
      (∑ e : Exit N C, N.portEnergy x e.target (reverseDirection e.port)) +
        3 * ∑ e : Exit N C, x e.target ^ 2 := by
  rw [DirectionalNetwork.energy_eq_sum_portEnergy, Fintype.sum_sum_type]
  simp_rw [portEnergy_center, portEnergy_leaf_sum]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Distinct exits use distinct original reverse ports. -/
theorem exit_reversePort_injective (N : DirectionalNetwork V) (C : Finset V) :
    Function.Injective (fun e : Exit N C => (e.target, reverseDirection e.port)) := by
  intro e f h
  have ht : e.target = f.target := congrArg Prod.fst h
  have hd : e.port = f.port := reverseDirection_injective (congrArg Prod.snd h)
  have he := (N.reverse_step e.center.val e.target e.port).mp e.edge
  have hf := (N.reverse_step f.center.val f.target f.port).mp f.edge
  rw [← ht, ← hd] at hf
  have hc : e.center.val = f.center.val := Option.some.inj (he.symm.trans hf)
  exact Exit.ext (Subtype.ext hc) hd ht

abbrev RetainedPort (N : DirectionalNetwork V) (C : Finset V) :=
  (Center C × Fin 4) ⊕ Exit N C

def retainedPort (N : DirectionalNetwork V) (C : Finset V) : RetainedPort N C → V × Fin 4
  | Sum.inl p => (p.1.val, p.2)
  | Sum.inr e => (e.target, reverseDirection e.port)

theorem retainedPort_injective (N : DirectionalNetwork V) (C : Finset V) :
    Function.Injective (retainedPort N C) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (Prod.ext
        (Subtype.ext (congrArg (fun p : V × Fin 4 => p.1) h))
        (congrArg (fun p : V × Fin 4 => p.2) h))
    | inr b =>
      have he : a.1.val = b.target := congrArg Prod.fst h
      exact False.elim (b.outside (he ▸ a.1.property))
  | inr a =>
    cases b with
    | inl b =>
      have he : a.target = b.1.val := congrArg Prod.fst h
      exact False.elim (a.outside (he.symm ▸ b.1.property))
    | inr b => exact congrArg Sum.inr (exit_reversePort_injective N C h)

theorem retained_energy_le (N : DirectionalNetwork V) (C : Finset V) (x : V → ℝ) :
    (∑ c : Center C, ∑ d : Fin 4, N.portEnergy x c.val d) +
      (∑ e : Exit N C, N.portEnergy x e.target (reverseDirection e.port)) ≤ N.energy x := by
  have h : (∑ a : RetainedPort N C,
      N.portEnergy x (retainedPort N C a).1 (retainedPort N C a).2) ≤
      ∑ p : V × Fin 4, N.portEnergy x p.1 p.2 := by
    apply Finset.sum_le_sum_of_injOn (retainedPort N C)
      (retainedPort_injective N C).injOn (Finset.subset_univ _)
    · intro a _; exact le_rfl
    · intro p _ _; exact N.portEnergy_nonneg x p.1 p.2
  rw [DirectionalNetwork.energy_eq_sum_portEnergy]
  simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type, retainedPort] using h

theorem exit_squares_le (N : DirectionalNetwork V) (C B : Finset V)
    (hB : ∀ e : Exit N C, e.target ∈ B) (x : V → ℝ) :
    (∑ e : Exit N C, x e.target ^ 2) ≤ 4 * ∑ b ∈ B, x b ^ 2 := by
  let f : Exit N C → Center B × Fin 4 :=
    fun e => (⟨e.target, hB e⟩, reverseDirection e.port)
  have hf : Function.Injective f := by
    intro e e' h
    apply exit_reversePort_injective N C
    exact Prod.ext (congrArg (fun p : Center B × Fin 4 => p.1.val) h)
      (congrArg (fun p : Center B × Fin 4 => p.2) h)
  have hs : (∑ e : Exit N C, x e.target ^ 2) ≤
      ∑ p : Center B × Fin 4, x p.1.val ^ 2 := by
    apply Finset.sum_le_sum_of_injOn f hf.injOn (Finset.subset_univ _)
    · intro e _; exact le_rfl
    · intro p _ _; exact sq_nonneg _
  convert hs using 1
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_coe_sort B (fun b => x b ^ 2)).symm

/-- Every discarded target has at most four incoming ports. The three new
grounded ports on each clone therefore cost at most twelve target squares. -/
theorem energy_clone_le (N : DirectionalNetwork V) (C B : Finset V)
    (hB : ∀ e : Exit N C, e.target ∈ B) (x : V → ℝ) :
    (network N C).energy (cloneWeight N C x) ≤
      N.energy x + 12 * ∑ b ∈ B, x b ^ 2 := by
  rw [energy_clone_eq]
  have h₁ := retained_energy_le N C x
  have h₂ := exit_squares_le N C B hB x
  linarith

end TranscendentalTuran.Network.PrivateLeaves
