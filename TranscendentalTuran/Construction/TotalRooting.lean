module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

namespace TranscendentalTuran.Source

open TuranUniversality Encoding

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {D : Type*} [DecidableEq D]

@[simp] theorem toRight_singleton_data (x : D) :
    ({Sum.inr x} : Finset (Root ⊕ D)).toRight = {x} := by ext y; simp

@[simp] theorem toLeft_singleton_data (x : D) :
    ({Sum.inr x} : Finset (Root ⊕ D)).toLeft = ∅ := by ext r; simp

@[simp] theorem toRight_singleton_root (r : Root) :
    ({Sum.inl r} : Finset (Root ⊕ D)).toRight = ∅ := by ext x; simp

@[simp] theorem toLeft_singleton_root (r : Root) :
    ({Sum.inl r} : Finset (Root ⊕ D)).toLeft = {r} := by ext s; simp

/-- The canonical total rooting of a graph explicitly split into roots
and data. This is shared by upper-bound completion and lower realizations. -/
def sumRooting (D : Type*) : Rooting Root (Root ⊕ D) :=
  ⟨fun r => some (Sum.inl r), by
    intro r s v hr hs
    exact Sum.inl.inj (Option.some.inj (hr.trans hs.symm))⟩

@[simp] theorem sumRooting_val (r : Root) :
    (sumRooting D).val r = some (Sum.inl r) := rfl

@[simp] theorem sumRooting_inl_not_data (r : Root) :
    ¬ Data (sumRooting D) (Sum.inl r) := by
  intro h
  exact h ((Rooting.mem_range _ _).mpr ⟨r, rfl⟩)

@[simp] theorem sumRooting_inr_data (x : D) : Data (sumRooting D) (Sum.inr x) := by
  intro h
  obtain ⟨r, hr⟩ := (Rooting.mem_range _ _).mp h
  cases hr

theorem sumRooting_data_exists {v : Root ⊕ D} (hv : Data (sumRooting D) v) :
    ∃ x : D, v = Sum.inr x := by
  cases v with
  | inl r => exact False.elim (sumRooting_inl_not_data r hv)
  | inr x => exact ⟨x, rfl⟩

@[simp] theorem sumRooting_link (G : RGraph (Root ⊕ D) 3) (r : Root) (x y : D) :
    Link G (sumRooting D) r (Sum.inr x) (Sum.inr y) ↔
      {Sum.inl r, Sum.inr x, Sum.inr y} ∈ G.edges := by
  simp only [Link, sumRooting_inr_data, true_and, sumRooting_val, Option.some.injEq]
  simp

@[simp] theorem sumRooting_pairLink (G : RGraph (Root ⊕ D) 3) (r s : Root) (x : D) :
    PairLink G (sumRooting D) r s (Sum.inr x) ↔
      {Sum.inl r, Sum.inl s, Sum.inr x} ∈ G.edges := by
  simp only [PairLink, sumRooting_inr_data, true_and, sumRooting_val, Option.some.injEq]
  simp

end TranscendentalTuran.Source
