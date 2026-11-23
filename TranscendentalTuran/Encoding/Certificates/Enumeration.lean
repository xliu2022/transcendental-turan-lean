module

public import TranscendentalTuran.Encoding.Certificates.Bounded
public import TranscendentalTuran.Encoding.Certificates.DecidableRules
public import TranscendentalTuran.Encoding.PatternBasis

@[expose] public section

namespace TranscendentalTuran.Encoding.Certificates

open TuranUniversality

set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {Q : Type*} [DecidableEq Q]

abbrev PatternCode (Q : Type*) [DecidableEq Q] :=
  Σ r : ℕ, Σ d : ℕ, (Fin r ↪ Q) × RGraph (Fin r ⊕ Fin d) 3

def patternCode (p : RootedPattern Q) : PatternCode Q :=
  ⟨p.rootCount, p.dataCount, p.rootLabels, p.graph⟩
def codePattern (c : PatternCode Q) : RootedPattern Q :=
  ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩

theorem patternCode_injective : Function.Injective (patternCode (Q := Q)) := by
  intro p p' h
  have := congrArg codePattern h
  change p = p' at this
  exact this

instance : DecidableEq (RootedPattern Q) := fun p p' =>
  decidable_of_iff (patternCode p = patternCode p')
    ⟨fun h => patternCode_injective h, fun h => congrArg patternCode h⟩

local instance enumerableEmbeddings [Fintype Q] (r : ℕ) : Fintype (Fin r ↪ Q) :=
  Fintype.ofEquiv {f : Fin r → Q // Function.Injective f}
    { toFun := fun f => ⟨f.val, f.property⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev BoundedCode (Q : Type*) [DecidableEq Q] :=
  Σ r : Fin 41, Σ d : Fin 14, (Fin r.val ↪ Q) × RGraph (Fin r.val ⊕ Fin d.val) 3

def decodeBounded (c : BoundedCode Q) : RootedPattern Q :=
  ⟨c.1.val, c.2.1.val, c.2.2.1, c.2.2.2⟩

def allBoundedPatterns [Fintype Q] : Finset (RootedPattern Q) :=
  Finset.univ.image decodeBounded

theorem mem_allBoundedPatterns [Fintype Q] (p : RootedPattern Q) :
    p ∈ allBoundedPatterns ↔ p.rootCount ≤ 40 ∧ p.dataCount ≤ 13 := by
  constructor
  · intro hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨by change c.1.val ≤ 40; have := c.1.isLt; omega,
      by change c.2.1.val ≤ 13; have := c.2.1.isLt; omega⟩
  · rintro ⟨hr, hd⟩
    exact Finset.mem_image.mpr
      ⟨⟨⟨p.rootCount, by omega⟩, ⟨p.dataCount, by omega⟩, p.rootLabels, p.graph⟩,
        Finset.mem_univ _, rfl⟩

instance (p : RootedPattern Q) (Γ : Finset (Finset Q)) (e : Finset p.Vertices) :
    Decidable (p.AllowedEdge Γ e) := by
  unfold RootedPattern.AllowedEdge
  infer_instance

instance (p : RootedPattern Q) (Γ : Finset (Finset Q)) : Decidable (p.TransferCompatible Γ) := by
  unfold RootedPattern.TransferCompatible
  infer_instance

end TranscendentalTuran.Encoding.Certificates

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Encoding.Certificates

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- A finite executable enumeration of the actual positive certificates.
The macro-inline attribute prevents evaluation of this immense closed set
when the module is loaded; the enumeration is performed only if requested. -/
@[macro_inline] def forbiddenPatterns : Finset (RootedPattern Root) :=
  allBoundedPatterns.filter fun p => p.TransferCompatible Γ ∧ ¬ RootedLegal p.graph p.canonical

theorem mem_forbiddenPatterns (p : RootedPattern Root) : p ∈ forbiddenPatterns ↔
    p.rootCount ≤ 40 ∧ p.dataCount ≤ 13 ∧ p.TransferCompatible Γ ∧
      ¬ RootedLegal p.graph p.canonical := by
  simp only [forbiddenPatterns, Finset.mem_filter, mem_allBoundedPatterns, and_assoc]

theorem forbiddenPatterns_roots {p : RootedPattern Root} (hp : p ∈ forbiddenPatterns) :
    p.rootCount ≤ 40 := (mem_forbiddenPatterns p).mp hp |>.1
theorem forbiddenPatterns_data {p : RootedPattern Root} (hp : p ∈ forbiddenPatterns) :
    p.dataCount ≤ 13 := (mem_forbiddenPatterns p).mp hp |>.2.1
theorem forbiddenPatterns_compatible {p : RootedPattern Root} (hp : p ∈ forbiddenPatterns) :
    p.TransferCompatible Γ := (mem_forbiddenPatterns p).mp hp |>.2.2.1

theorem rootedLegal_iff_patternLegal {V : Type*} [DecidableEq V]
    (G : RGraph V 3) (μ : Rooting Root V) :
    RootedLegal G μ ↔ PatternLegal forbiddenPatterns G μ := by
  constructor
  · intro hlegal p hp hmatch
    exact failed_pattern_persists p ((mem_forbiddenPatterns p).mp hp).2.2.2 G μ hmatch hlegal
  · intro hlegal
    by_contra hbad
    obtain ⟨p, hr, hd, hc, hb, hm⟩ := exists_bounded_pattern hbad
    exact hlegal p ((mem_forbiddenPatterns p).mpr ⟨hr, hd, hc, hb⟩) hm

theorem admissible_iff_patternClass {V : Type*} [DecidableEq V] (G : RGraph V 3) :
    Admissible G ↔ PatternClass forbiddenPatterns G := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, (rootedLegal_iff_patternLegal G μ).mp hμ⟩
  · rintro ⟨μ, hμ⟩
    exact ⟨μ, (rootedLegal_iff_patternLegal G μ).mpr hμ⟩

theorem rootedLegal_of_edgeless {V : Type*} [DecidableEq V]
    (G : RGraph V 3) (μ : Rooting Root V) (hG : G.edges = ∅) : RootedLegal G μ := by
  constructor <;> intros
  all_goals
    simp_all [Link, PairLink, Marked, Declared, MatchingEdge, OwnerEdge,
      IsCenter, CompleteE, CompleteD, StructuralAt, ParentH, ParentV]

theorem forbiddenPatterns_have_edges {p : RootedPattern Root} (hp : p ∈ forbiddenPatterns) :
    p.graph.edges.Nonempty := by
  by_contra h
  have he : p.graph.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  exact ((mem_forbiddenPatterns p).mp hp).2.2.2 (rootedLegal_of_edgeless p.graph p.canonical he)

end TranscendentalTuran.Source.Certificates
