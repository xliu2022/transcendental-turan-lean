module

public import TranscendentalTuran.Construction.Guard
public import TranscendentalTuran.Construction.SourceBasis
public import TranscendentalTuran.Construction.EffectiveFiniteGraph
public import TuranUniversality.Hypergraph.GuardedBasis
public import TuranUniversality.Hypergraph.Labeled

@[expose] public section

namespace TranscendentalTuran.Guard

open TuranUniversality Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- Label the exact disjoint-clique guard by the explicit arithmetic product
equivalence. The macro avoids evaluating this enormous graph at module load. -/
@[macro_inline] def finiteGraph : FiniteGraph 3 :=
  ⟨copies * guardBlockSize, Effective.pullback
    (RGraph.cliquePacking copies guardBlockSize) finProdFinEquiv.symm.toEmbedding⟩

theorem finiteGraph_embedding :
    finiteGraph.2.IsEmbedding graph finProdFinEquiv.symm := by
  dsimp only [finiteGraph, graph]
  rw [Effective.pullback_eq]
  exact (RGraph.cliquePacking copies guardBlockSize).pullback_equiv_embedding _

theorem embedding_finiteGraph :
    graph.IsEmbedding finiteGraph.2 finProdFinEquiv := by
  dsimp only [finiteGraph, graph]
  rw [Effective.pullback_eq]
  exact (RGraph.cliquePacking copies guardBlockSize).pullback_equiv_inverse _

theorem contains_iff (G : FiniteGraph 3) : finiteGraph.Contains G ↔
    ∃ f, graph.IsEmbedding G.2 f := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨_, hf.comp embedding_finiteGraph⟩
  · rintro ⟨f, hf⟩
    exact ⟨_, hf.comp finiteGraph_embedding⟩

theorem graph_has_edges : graph.edges.Nonempty := by
  have hb : 0 < copies := by rw [copies_value]; norm_num
  have ht : 3 ≤ guardBlockSize := by norm_num [guardBlockSize]
  let b : Fin copies := ⟨0, hb⟩
  let a : Fin guardBlockSize := ⟨0, by omega⟩
  let c : Fin guardBlockSize := ⟨1, by omega⟩
  let d : Fin guardBlockSize := ⟨2, by omega⟩
  refine ⟨{(b, a), (b, c), (b, d)}, ?_⟩
  exact RGraph.cliquePacking_triple b a c d
    (by intro h; have := congrArg Fin.val h; simp [a, c] at this)
    (by intro h; have := congrArg Fin.val h; simp [a, d] at this)
    (by intro h; have := congrArg Fin.val h; simp [c, d] at this)

theorem finiteGraph_has_edges : finiteGraph.2.edges.Nonempty := by
  obtain ⟨e, he⟩ := graph_has_edges
  exact ⟨_, embedding_finiteGraph.2 e he⟩

theorem contains_large_clique :
    finiteGraph.Contains ⟨q + 3, RGraph.clique (Fin (q + 3)) 3⟩ := by
  apply (contains_iff _).mpr
  have hsize : copies * guardBlockSize ≤ q + 3 := by
    have h := order_ratio
    omega
  let f : Vertex → Fin (q + 3) := fun v => Fin.castLE hsize (finProdFinEquiv v)
  have hf : Function.Injective f :=
    (Fin.castLE_injective hsize).comp finProdFinEquiv.injective
  refine ⟨f, hf, ?_⟩
  intro e he
  apply (RGraph.mem_clique _).mpr
  rw [Finset.card_image_of_injective _ hf]
  exact graph.uniform e he

end TranscendentalTuran.Guard

namespace TranscendentalTuran.Construction

open TuranUniversality Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- All bounded obstructions to admissibility or guard avoidance. Each
member is an ordinary source obstruction and contains the exact guard. -/
@[macro_inline] def guardedBasis : Finset (FiniteGraph 3) :=
  FiniteGraph.guardedBasis Source.finiteClass Source.obstructionOrder Guard.finiteGraph

theorem guardedBasis_spec (G : FiniteGraph 3) :
    Source.finiteClass G ∨ ¬ Guard.finiteGraph.Contains G ↔
      ∀ A ∈ guardedBasis, ¬ A.Contains G :=
  FiniteGraph.guardedBasis_spec Source.finiteClass Source.finiteClass_monotone
    Source.obstructionOrder Source.finiteClass_bounded Guard.finiteGraph G

theorem guardedBasis_properties {A : FiniteGraph 3} (hA : A ∈ guardedBasis) :
    ¬ Source.finiteClass A ∧ Guard.finiteGraph.Contains A :=
  FiniteGraph.guardedBasis_contains_guard Source.finiteClass
    Source.obstructionOrder Guard.finiteGraph hA

theorem guardedBasis_has_edges {A : FiniteGraph 3} (hA : A ∈ guardedBasis) :
    A.2.edges.Nonempty := by
  obtain ⟨f, hf⟩ := (guardedBasis_properties hA).2
  obtain ⟨e, he⟩ := Guard.finiteGraph_has_edges
  exact ⟨_, hf.2 e he⟩

theorem guardedBasis_nonempty : guardedBasis.Nonempty := by
  classical
  by_contra h
  have hempty : guardedBasis = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hclass := (guardedBasis_spec ⟨q + 3, RGraph.clique (Fin (q + 3)) 3⟩).mpr
    (by simp [hempty])
  rcases hclass with hsource | hguard
  · exact Source.large_clique_not_admissible (q + 3) le_rfl hsource
  · exact hguard Guard.contains_large_clique

-- The index type below contains `guardedBasis.card`. Elaborator reduction
-- must treat the underlying enormous enumeration symbolically as well.
attribute [irreducible] guardedBasis

/-- Index the actual finite guarded basis by sorting explicit encodings.
Keep this executable equivalence opaque to elaborator reduction: projecting a
factor's membership proof must not evaluate the entire finite enumeration. -/
@[macro_inline, irreducible] def factorIndex : Fin guardedBasis.card ≃ guardedBasis :=
  Effective.finsetIndex guardedBasis

@[macro_inline] def factor (i : Fin guardedBasis.card) : FiniteGraph 3 :=
  Effective.finsetElement guardedBasis i

theorem factor_mem (i : Fin guardedBasis.card) : factor i ∈ guardedBasis :=
  Effective.finsetElement_mem guardedBasis i

theorem factor_surjective {A : FiniteGraph 3} (hA : A ∈ guardedBasis) :
    ∃ i : Fin guardedBasis.card, factor i = A :=
  Effective.finsetElement_surjective guardedBasis A hA

theorem factor_outside (i : Fin guardedBasis.card) : ¬ Source.finiteClass (factor i) :=
  (guardedBasis_properties (factor_mem i)).1

theorem factor_has_edges (i : Fin guardedBasis.card) : (factor i).2.edges.Nonempty :=
  guardedBasis_has_edges (factor_mem i)

theorem factor_contains_guard (i : Fin guardedBasis.card) :
    ∃ f, Guard.graph.IsEmbedding (factor i).2 f :=
  (Guard.contains_iff _).mp (guardedBasis_properties (factor_mem i)).2

end TranscendentalTuran.Construction
