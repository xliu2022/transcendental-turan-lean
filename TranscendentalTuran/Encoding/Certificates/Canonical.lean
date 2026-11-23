module

public import TranscendentalTuran.Encoding.LocalMonotonicity
public import TuranUniversality.Hypergraph.FiniteBasis

@[expose] public section

namespace TranscendentalTuran.Encoding.Certificates

open TuranUniversality

universe u v w
variable {Q : Type u} {R : Type v} {D : Type w}
  [Fintype R] [DecidableEq R] [DecidableEq Q]

theorem unique_label_preimage (labels : R ↪ Q) (q : Q) (h : ∃ r, labels r = q) :
    ∃! r, r ∈ (Finset.univ : Finset R) ∧ labels r = q := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, ⟨Finset.mem_univ _, hr⟩,
    fun s hs => labels.injective (hs.2.trans hr.symm)⟩

def labelIndex (labels : R ↪ Q) (q : Q) : Option R :=
  if h : ∃ r, labels r = q then
    some (Finset.univ.choose (fun r => labels r = q) (unique_label_preimage labels q h))
  else none

theorem labelIndex_some_iff (labels : R ↪ Q) (q : Q) (r : R) :
    labelIndex labels q = some r ↔ labels r = q := by
  by_cases h : ∃ r, labels r = q
  · rw [labelIndex, dite_eq_left h]
    have hp := Finset.choose_property (fun r => labels r = q)
      Finset.univ (unique_label_preimage labels q h)
    constructor
    · intro hr
      simpa only [Option.some.inj hr] using hp
    · intro hr
      congr 1
      apply labels.injective
      exact hp.trans hr.symm
  · rw [labelIndex, dite_eq_right h]
    constructor
    · intro he
      cases he
    · intro hr
      exact False.elim (h ⟨r, hr⟩)

def canonicalRooting (labels : R ↪ Q) : Rooting Q (R ⊕ D) :=
  ⟨fun q => (labelIndex labels q).map Sum.inl, by
    intro a b v ha hb
    obtain ⟨r, hr, hrv⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨s, hs, hsv⟩ := Option.map_eq_some_iff.mp hb
    have hrs : r = s := Sum.inl.inj (hrv.trans hsv.symm)
    have har := (labelIndex_some_iff labels a r).mp hr
    have hbs := (labelIndex_some_iff labels b s).mp hs
    exact har.symm.trans ((congrArg labels hrs).trans hbs)⟩

@[simp] theorem canonicalRooting_inl (labels : R ↪ Q) (q : Q) (r : R) :
    (canonicalRooting (D := D) labels).val q = some (Sum.inl r) ↔ labels r = q := by
  simp only [canonicalRooting, Option.map_eq_some_iff]
  constructor
  · rintro ⟨s, hs, hsr⟩
    have := Sum.inl.inj hsr
    subst s
    exact (labelIndex_some_iff labels q r).mp hs
  · intro h
    exact ⟨r, (labelIndex_some_iff labels q r).mpr h, rfl⟩

@[simp] theorem canonicalRooting_inr (labels : R ↪ Q) (q : Q) (d : D) :
    (canonicalRooting labels).val q ≠ some (Sum.inr d) := by
  simp [canonicalRooting, Option.map_eq_some_iff]

@[simp] theorem canonicalRooting_root (labels : R ↪ Q) (r : R) :
    (canonicalRooting (D := D) labels).val (labels r) = some (Sum.inl r) :=
  (canonicalRooting_inl labels _ r).mpr rfl

@[simp] theorem canonicalRooting_data [Fintype Q] [DecidableEq D]
    (labels : R ↪ Q) (d : D) : Sum.inr d ∉ (canonicalRooting labels).range := by
  simp only [Rooting.mem_range, not_exists]
  exact fun q => canonicalRooting_inr labels q d

@[simp] theorem canonicalRooting_root_mem [Fintype Q] [DecidableEq D]
    (labels : R ↪ Q) (r : R) : Sum.inl r ∈ (canonicalRooting (D := D) labels).range := by
  exact (Rooting.mem_range _ _).mpr ⟨labels r, canonicalRooting_root labels r⟩

end TranscendentalTuran.Encoding.Certificates

namespace TranscendentalTuran.Encoding.RootedPattern

open TuranUniversality Certificates

variable {Q : Type*} [DecidableEq Q]

def canonical (p : RootedPattern Q) : Rooting Q p.Vertices := canonicalRooting p.rootLabels

theorem matches_self [Fintype Q] (p : RootedPattern Q) : p.Matches p.graph p.canonical id := by
  refine ⟨⟨Function.injective_id, RGraph.isHom_id _⟩, ?_, ?_⟩
  · exact fun i => canonicalRooting_root p.rootLabels i
  · exact fun j => canonicalRooting_data p.rootLabels j

end TranscendentalTuran.Encoding.RootedPattern

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Encoding.Certificates

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V]

def rootedMapOfMatch (p : RootedPattern Root) (G : RGraph V 3) (μ : Rooting Root V)
    {f : p.Vertices → V} (hf : p.Matches G μ f) :
    RootedMap p.graph p.canonical G μ where
  map := ⟨f, hf.embedding.1⟩
  hom := hf.embedding.2
  roots := by
    intro q v hv
    cases v with
    | inl r =>
        have hq := (canonicalRooting_inl p.rootLabels q r).mp hv
        subst q
        exact hf.root_eq r
    | inr d => exact False.elim (canonicalRooting_inr p.rootLabels q d hv)
  data := by
    intro v hv
    cases v with
    | inl r => exact False.elim (hv (canonicalRooting_root_mem p.rootLabels r))
    | inr d => exact hf.data_out d

theorem failed_pattern_persists (p : RootedPattern Root)
    (hbad : ¬ RootedLegal p.graph p.canonical) (G : RGraph V 3) (μ : Rooting Root V)
    (hmatch : p.Realizes G μ) : ¬ RootedLegal G μ := by
  obtain ⟨f, hf⟩ := hmatch
  exact fun hlegal => hbad ((rootedMapOfMatch p G μ hf).rootedLegal hlegal)

end TranscendentalTuran.Source.Certificates
