module

public import TuranUniversality.Hypergraph.Labeled
public import Mathlib.Logic.Equiv.Finset
public import Mathlib.Logic.Encodable.Pi

@[expose] public section

/-!
# Effective finite graph operations

Formalization author and responsible maintainer: Xizhi Liu.

The finite witness is generated using finite lists, decidable predicates,
and explicit encodings. Classical choice remains available in proofs, but
is not used to compute the witness or its vertex labeling.
-/

namespace TranscendentalTuran.Effective

open TuranUniversality

universe u v

/-- Encode a graph by its finite edge set and its uniformity certificate. -/
def graphEncodingEquiv {V : Type u} [DecidableEq V] (r : ℕ) :
    RGraph V r ≃ {s : Finset (Finset V) // ∀ e ∈ s, e.card = r} where
  toFun G := ⟨G.edges, G.uniform⟩
  invFun s := ⟨s.val, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance graphEncodable {V : Type u} [DecidableEq V] [Encodable V] (r : ℕ) :
    Encodable (RGraph V r) :=
  Encodable.ofEquiv _ (graphEncodingEquiv r)

/-- Sort a finite family by its encoding to obtain an effective index. -/
def finsetIndex {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) : Fin s.card ≃ s :=
  (Encodable.fintypeEquivFin.trans (finCongr (Fintype.card_coe s))).symm

theorem finsetIndex_mem {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) (i : Fin s.card) : (finsetIndex s i).val ∈ s :=
  Subtype.property (finsetIndex s i)

theorem finsetIndex_surjective {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) (x : V) (hx : x ∈ s) :
    ∃ i : Fin s.card, (finsetIndex s i).val = x := by
  refine ⟨(finsetIndex s).symm ⟨x, hx⟩, ?_⟩
  exact congrArg Subtype.val ((finsetIndex s).apply_symm_apply ⟨x, hx⟩)

/-- Extract the indexed element while keeping the finite set a symbolic
parameter of all projection proofs. -/
def finsetElement {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) (i : Fin s.card) : V := (finsetIndex s i).val

theorem finsetElement_mem {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) (i : Fin s.card) : finsetElement s i ∈ s :=
  finsetIndex_mem s i

theorem finsetElement_surjective {V : Type*} [DecidableEq V] [Encodable V]
    (s : Finset V) (x : V) (hx : x ∈ s) :
    ∃ i : Fin s.card, finsetElement s i = x :=
  finsetIndex_surjective s x hx

/-- Compute a pullback by a decidable finite edge filter. -/
def pullback {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {r : ℕ} (G : RGraph W r) (f : V ↪ W) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.map f ∈ G.edges)
  uniform := fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

theorem pullback_eq {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {r : ℕ} (G : RGraph W r) (f : V ↪ W) : pullback G f = G.pullback f := by
  apply RGraph.ext
  rfl

/-- A computable labeling obtained by sorting the explicit vertex encodings. -/
def ofRGraph {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]
    {r : ℕ} (G : RGraph V r) : FiniteGraph r :=
  ⟨Fintype.card V, pullback G Encodable.fintypeEquivFin.symm.toEmbedding⟩

theorem ofRGraph_embedding {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]
    {r : ℕ} (G : RGraph V r) :
    (ofRGraph G).2.IsEmbedding G Encodable.fintypeEquivFin.symm := by
  dsimp only [ofRGraph]
  rw [pullback_eq]
  exact G.pullback_equiv_embedding _

theorem embedding_ofRGraph {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]
    {r : ℕ} (G : RGraph V r) :
    G.IsEmbedding (ofRGraph G).2 Encodable.fintypeEquivFin := by
  dsimp only [ofRGraph]
  rw [pullback_eq]
  exact G.pullback_equiv_inverse _

theorem ofRGraph_homFree {V W : Type*} [Fintype V] [DecidableEq V] [Encodable V]
    [DecidableEq W] {r : ℕ} (G : RGraph V r) (H : RGraph W r) :
    (ofRGraph G).2.HomFree H ↔ G.HomFree H :=
  ⟨fun h => h.of_hom (ofRGraph_embedding G).isHom,
    fun h => h.of_hom (embedding_ofRGraph G).isHom⟩

theorem ofRGraph_edges_nonempty {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]
    {r : ℕ} (G : RGraph V r) (h : G.edges.Nonempty) :
    (ofRGraph G).2.edges.Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨_, (embedding_ofRGraph G).2 e he⟩

/-- The same pair extension, with the finite decidable instances explicit. -/
def pairExtension {V : Type u} [Fintype V] [DecidableEq V]
    (A : RGraph V 3) : RGraph (RGraph.ExtensionVertex V) 3 where
  edges := A.edges.image (fun e => e.image Sum.inl) ∪
    Finset.univ.image RGraph.privateEdge
  uniform := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      exact A.uniform d hd
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
      exact RGraph.privateEdge_card p

theorem pairExtension_eq {V : Type u} [Fintype V] [DecidableEq V]
    (A : RGraph V 3) : pairExtension A = A.pairExtension := by
  apply RGraph.ext
  rfl

/-- The product is computed by filtering the finite list of possible edges. -/
def product {I : Type u} [Fintype I] [DecidableEq I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {r : ℕ} (G : ∀ i, RGraph (V i) r) : RGraph (∀ i, V i) r where
  edges := (Finset.univ.powersetCard r).filter
    (fun e => ∀ i, e.image (fun x => x i) ∈ (G i).edges)
  uniform := fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

theorem product_eq {I : Type u} [Fintype I] [DecidableEq I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {r : ℕ} (G : ∀ i, RGraph (V i) r) : product G = RGraph.product G := by
  apply RGraph.ext
  ext e
  simp only [product, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    true_and, RGraph.product_mem]

end TranscendentalTuran.Effective
