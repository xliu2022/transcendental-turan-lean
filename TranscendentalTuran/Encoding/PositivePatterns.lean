module

public import TuranUniversality.Hypergraph.PartialRooting
public import TuranUniversality.Hypergraph.Hom
public import TuranUniversality.Hypergraph.Restriction

@[expose] public section

/-!
# Positive rooted certificates

Formalization author and responsible maintainer: Xizhi Liu.

A certificate is an actual finite three-graph with distinct labeled roots
and data vertices. A match preserves every edge, every root label, and data
status. This module treats finite collections of these concrete patterns;
the manuscript's individual local violations must be supplied as patterns
before the resulting class can be identified with its source class.
-/

namespace TranscendentalTuran.Encoding

open TuranUniversality

universe u v w

structure RootedPattern (Q : Type u) where
  rootCount : ℕ
  dataCount : ℕ
  rootLabels : Fin rootCount ↪ Q
  graph : RGraph (Fin rootCount ⊕ Fin dataCount) 3

namespace RootedPattern

abbrev Vertices {Q : Type u} (p : RootedPattern Q) :=
  Fin p.rootCount ⊕ Fin p.dataCount

variable {Q : Type u} {V : Type v} {W : Type w}
  [Fintype Q] [DecidableEq Q] [DecidableEq V] [DecidableEq W]

structure Matches (p : RootedPattern Q) (G : RGraph V 3) (μ : Rooting Q V)
    (f : p.Vertices → V) : Prop where
  embedding : p.graph.IsEmbedding G f
  root_eq : ∀ i, μ.val (p.rootLabels i) = some (f (Sum.inl i))
  data_out : ∀ j, f (Sum.inr j) ∉ μ.range

instance (p : RootedPattern Q) (G : RGraph V 3) (μ : Rooting Q V)
    (f : p.Vertices → V) : Decidable (p.Matches G μ f) :=
  decidable_of_iff
    (p.graph.IsEmbedding G f ∧
      (∀ i, μ.val (p.rootLabels i) = some (f (Sum.inl i))) ∧
      (∀ j, f (Sum.inr j) ∉ μ.range))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.embedding, h.root_eq, h.data_out⟩⟩

def Realizes (p : RootedPattern Q) (G : RGraph V 3) (μ : Rooting Q V) : Prop :=
  ∃ f, p.Matches G μ f

instance [Fintype V] (p : RootedPattern Q) (G : RGraph V 3) (μ : Rooting Q V) :
    Decidable (p.Realizes G μ) :=
  inferInstanceAs (Decidable (∃ f, p.Matches G μ f))

def dataImages (p : RootedPattern Q) (f : p.Vertices → V) : Finset V :=
  Finset.univ.image (fun j => f (Sum.inr j))

theorem dataImages_card_le (p : RootedPattern Q) (f : p.Vertices → V) :
    (p.dataImages f).card ≤ p.dataCount := by
  exact (Finset.card_image_le).trans (by simp)

theorem mem_dataImages (p : RootedPattern Q) (f : p.Vertices → V) (j : Fin p.dataCount) :
    f (Sum.inr j) ∈ p.dataImages f := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- Exactly the three edge shapes retained in the manuscript's certificates. -/
def AllowedEdge (p : RootedPattern Q) (Γ : Finset (Finset Q))
    (e : Finset p.Vertices) : Prop :=
  (∃ a b c, e = {Sum.inr a, Sum.inr b, Sum.inr c}) ∨
  (∃ r a b, e = {Sum.inl r, Sum.inr a, Sum.inr b}) ∨
  (∃ r s a, e = {Sum.inl r, Sum.inl s, Sum.inr a} ∧
    {p.rootLabels r, p.rootLabels s} ∈ Γ)

def TransferCompatible (p : RootedPattern Q) (Γ : Finset (Finset Q)) : Prop :=
  ∀ e ∈ p.graph.edges, p.AllowedEdge Γ e

theorem Matches.extend {p : RootedPattern Q} {G : RGraph V 3}
    {μ ν : Rooting Q V} {f : p.Vertices → V}
    (h : p.Matches G μ f) (hext : Rooting.Extends μ ν)
    (hdata : ∀ j, f (Sum.inr j) ∉ ν.range) : p.Matches G ν f where
  embedding := h.embedding
  root_eq := fun i => hext _ _ (h.root_eq i)
  data_out := hdata

end RootedPattern

variable {Q : Type u} {V : Type v} {W : Type w}
  [Fintype Q] [DecidableEq Q] [DecidableEq V] [DecidableEq W]

def PatternLegal (R : Finset (RootedPattern Q)) (G : RGraph V 3)
    (μ : Rooting Q V) : Prop :=
  ∀ p ∈ R, ¬ p.Realizes G μ

def PatternClass (R : Finset (RootedPattern Q)) (G : RGraph V 3) : Prop :=
  ∃ μ, PatternLegal R G μ

instance [Fintype V] (R : Finset (RootedPattern Q)) (G : RGraph V 3)
    (μ : Rooting Q V) : Decidable (PatternLegal R G μ) :=
  inferInstanceAs (Decidable (∀ p ∈ R, ¬ p.Realizes G μ))

instance [Fintype V] (R : Finset (RootedPattern Q)) (G : RGraph V 3) :
    Decidable (PatternClass R G) :=
  inferInstanceAs (Decidable (∃ μ, PatternLegal R G μ))

/-- Pull a partial root assignment back along an embedding; roots outside
the image are removed. They are never reinterpreted as data vertices. -/
noncomputable def pullbackRooting (μ : Rooting Q W) (f : V ↪ W) : Rooting Q V :=
  (μ.inverse.precompose f).inverse

theorem pullbackRooting_some_iff (μ : Rooting Q W) (f : V ↪ W) (a : Q) (v : V) :
    (pullbackRooting μ f).val a = some v ↔ μ.val a = some (f v) := by
  rw [pullbackRooting, Rooting.inverse_some_iff]
  change μ.inverse.val (f v) = some a ↔ μ.val a = some (f v)
  exact Rooting.inverse_some_iff μ (f v) a

theorem mem_pullbackRooting_range (μ : Rooting Q W) (f : V ↪ W) (v : V) :
    v ∈ (pullbackRooting μ f).range ↔ f v ∈ μ.range := by
  simp only [Rooting.mem_range, pullbackRooting_some_iff]

theorem PatternLegal.pullback (R : Finset (RootedPattern Q))
    (G : RGraph V 3) (H : RGraph W 3) (f : V ↪ W)
    (hf : G.IsEmbedding H f) (μ : Rooting Q W) (hμ : PatternLegal R H μ) :
    PatternLegal R G (pullbackRooting μ f) := by
  intro p hp hmatch
  obtain ⟨g, hg⟩ := hmatch
  apply hμ p hp
  refine ⟨f ∘ g, hf.comp hg.embedding, ?_, ?_⟩
  · intro i
    exact (pullbackRooting_some_iff μ f _ _).mp (hg.root_eq i)
  · intro j hj
    exact hg.data_out j ((mem_pullbackRooting_range μ f _).mpr hj)

theorem PatternClass.of_embedding (R : Finset (RootedPattern Q))
    (G : RGraph V 3) (H : RGraph W 3) {f : V → W}
    (hf : G.IsEmbedding H f) (hH : PatternClass R H) : PatternClass R G := by
  obtain ⟨μ, hμ⟩ := hH
  exact ⟨pullbackRooting μ ⟨f, hf.1⟩,
    PatternLegal.pullback R G H ⟨f, hf.1⟩ hf μ hμ⟩

/-- Admissibility on a retained vertex set, expressed in the ambient host. -/
def PatternLegalOn (R : Finset (RootedPattern Q)) (G : RGraph V 3)
    (T : Finset V) (μ : Rooting Q V) : Prop :=
  μ.range ⊆ T ∧ ∀ p ∈ R, ∀ f : p.Vertices → V,
    p.Matches G μ f → ¬ (∀ v, f v ∈ T)

theorem patternLegalOn_univ_iff [Fintype V]
    (R : Finset (RootedPattern Q)) (G : RGraph V 3) (μ : Rooting Q V) :
    PatternLegalOn R G Finset.univ μ ↔ PatternLegal R G μ := by
  constructor
  · intro h p hp ⟨f, hf⟩
    exact h.2 p hp f hf (fun _ => Finset.mem_univ _)
  · intro h
    refine ⟨Finset.subset_univ _, ?_⟩
    intro p hp f hf _
    exact h p hp ⟨f, hf⟩

/-- A failed positive certificate can be repaired only by rooting one of
its data vertices. Its existing root labels remain fixed. -/
theorem positive_pattern_repair
    (R : Finset (RootedPattern Q)) (G : RGraph V 3)
    {p : RootedPattern Q} (hp : p ∈ R) {μ ν : Rooting Q V}
    {f : p.Vertices → V} (hf : p.Matches G μ f)
    {T : Finset V} (hT : p.dataImages f ⊆ T)
    (hext : Rooting.Extends μ ν) (hlegal : PatternLegalOn R G T ν) :
    ∃ a v, μ.val a = none ∧ ν.val a = some v ∧ v ∈ p.dataImages f ∧ v ∉ μ.range := by
  classical
  have hnew : ∃ j : Fin p.dataCount, f (Sum.inr j) ∈ ν.range := by
    by_contra h
    have hout : ∀ j, f (Sum.inr j) ∉ ν.range := by simpa using h
    apply hlegal.2 p hp f (hf.extend hext hout)
    intro v
    cases v with
    | inl i => exact hlegal.1 ((Rooting.mem_range ν _).mpr
        ⟨p.rootLabels i, hext _ _ (hf.root_eq i)⟩)
    | inr j => exact hT (p.mem_dataImages f j)
  obtain ⟨j, hj⟩ := hnew
  obtain ⟨a, ha⟩ := (Rooting.mem_range ν _).mp hj
  refine ⟨a, f (Sum.inr j), ?_, ha, p.mem_dataImages f j, hf.data_out j⟩
  cases hma : μ.val a with
  | none => rfl
  | some v =>
    have hv : v = f (Sum.inr j) := Option.some.inj ((hext a v hma).symm.trans ha)
    exact False.elim (hf.data_out j ((Rooting.mem_range μ _).mpr ⟨a, hv ▸ hma⟩))

/-- Bounded root search for a concrete finite positive-pattern collection. -/
theorem positive_patterns_bounded_obstruction [Fintype V]
    (R : Finset (RootedPattern Q)) (G : RGraph V 3) (w : ℕ)
    (hw : ∀ p ∈ R, p.dataCount ≤ w) (hbad : ¬ PatternClass R G) :
    ∃ T : Finset V,
      T.card ≤ w * ∑ j ∈ Finset.range (Fintype.card Q + 1), (Fintype.card Q * w) ^ j ∧
      ∀ μ, ¬ PatternLegalOn R G T μ := by
  classical
  apply Rooting.bounded_obstruction (PatternLegalOn R G) w
  · intro μ hμ
    exact hbad ⟨μ, (patternLegalOn_univ_iff R G μ).mp hμ⟩
  · intro μ hμ
    have hfail : ¬ PatternLegal R G μ := by
      intro h
      exact hμ ((patternLegalOn_univ_iff R G μ).mpr h)
    simp only [PatternLegal, not_forall, not_not] at hfail
    obtain ⟨p, hp, f, hf⟩ := hfail
    refine ⟨p.dataImages f, (p.dataImages_card_le f).trans (hw p hp), ?_⟩
    intro T ν hT hext hlegal
    exact positive_pattern_repair R G hp hf hT hext hlegal

end TranscendentalTuran.Encoding
