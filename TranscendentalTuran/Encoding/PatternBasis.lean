module

public import TranscendentalTuran.Encoding.PositivePatterns
public import TuranUniversality.Hypergraph.FiniteBasis
public import TuranUniversality.Hypergraph.Relabel

@[expose] public section

/-!
# Effective finite bases for positive-pattern classes

Formalization author and responsible maintainer: Xizhi Liu.

The bound and the enumerating algorithm are functions of the finite pattern
collection and the root count. Their definitions contain no choice of a
forbidden basis. The enormous concrete bound is not evaluated by the proofs.
-/

namespace TranscendentalTuran.Encoding

open TuranUniversality

variable {Q V : Type*} [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]

theorem patternLegalOn_of_induced (R : Finset (RootedPattern Q)) (G : RGraph V 3)
    (T : Finset V) (ν : Rooting Q T)
    (hν : PatternLegal R (G.pullback (Function.Embedding.subtype (· ∈ T))) ν) :
    PatternLegalOn R G T (ν.map (Function.Embedding.subtype (· ∈ T))) := by
  classical
  let i : T ↪ V := Function.Embedding.subtype (· ∈ T)
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := (Rooting.mem_range _ v).mp hv
    change (ν.val a).map i = some v at ha
    obtain ⟨u, _, hu⟩ := Option.map_eq_some_iff.mp ha
    exact hu ▸ u.property
  · intro p hp f hf hall
    let g : p.Vertices → T := fun v => ⟨f v, hall v⟩
    have hginj : Function.Injective g := by
      intro a b hab
      exact hf.embedding.1 (congrArg Subtype.val hab)
    apply hν p hp
    refine ⟨g, ⟨hginj, ?_⟩, ?_, ?_⟩
    · intro e he
      apply (G.mem_pullback i (e.image g)).mpr
      constructor
      · rw [Finset.card_image_of_injective _ hginj]
        exact p.graph.uniform e he
      · have hmap : (e.image g).map i = e.image f := by
          simp only [Finset.map_eq_image, Finset.image_image]
          rfl
        rw [hmap]
        exact hf.embedding.2 e he
    · intro a
      exact (Rooting.map_some_iff ν i (p.rootLabels a) (g (Sum.inl a))).mp
        (hf.root_eq a)
    · intro j hj
      obtain ⟨a, ha⟩ := (Rooting.mem_range ν _).mp hj
      apply hf.data_out j
      apply (Rooting.mem_range _ _).mpr
      exact ⟨a, (Rooting.map_some_iff ν i a (g (Sum.inr j))).mpr ha⟩

def patternBound (rootCount witnessSize : ℕ) : ℕ :=
  witnessSize * ∑ j ∈ Finset.range (rootCount + 1), (rootCount * witnessSize) ^ j

def patternFiniteClass (R : Finset (RootedPattern Q)) (G : FiniteGraph 3) : Prop :=
  PatternClass R G.2

instance (R : Finset (RootedPattern Q)) : DecidablePred (patternFiniteClass R) :=
  fun G => inferInstanceAs (Decidable (PatternClass R G.2))

theorem patternFiniteClass_monotone (R : Finset (RootedPattern Q)) :
    FiniteGraph.ClassMonotone (patternFiniteClass R) := by
  intro A G hAG hG
  obtain ⟨f, hf⟩ := hAG
  exact PatternClass.of_embedding R A.2 G.2 hf hG

theorem patternFiniteClass_bounded (R : Finset (RootedPattern Q)) (w : ℕ)
    (hw : ∀ p ∈ R, p.dataCount ≤ w) (G : FiniteGraph 3)
    (hG : ¬ patternFiniteClass R G) :
    ∃ A : FiniteGraph 3, A.1 ≤ patternBound (Fintype.card Q) w ∧
      ¬ patternFiniteClass R A ∧ A.Contains G := by
  classical
  obtain ⟨T, hT, hbad⟩ := positive_patterns_bounded_obstruction R G.2 w hw hG
  let i : T ↪ Fin G.1 := Function.Embedding.subtype (· ∈ T)
  let J := G.2.pullback i
  let e : Fin T.card ≃ T := Fintype.equivOfCardEq (by simp)
  let A := J.pullback e.toEmbedding
  refine ⟨⟨T.card, A⟩, hT, ?_, ?_⟩
  · intro hA
    have hJ : PatternClass R J := PatternClass.of_embedding R J A
      (J.pullback_equiv_inverse e) hA
    obtain ⟨ν, hν⟩ := hJ
    exact hbad (ν.map i) (patternLegalOn_of_induced R G.2 T ν hν)
  · exact ⟨i ∘ e, i.injective.comp e.injective,
      (G.2.pullback_isHom i).comp (J.pullback_isHom e.toEmbedding)⟩

/-- An executable enumeration of all failed graphs below the proved bound. -/
def patternBasis (R : Finset (RootedPattern Q)) (w : ℕ) : Finset (FiniteGraph 3) :=
  FiniteGraph.forbiddenBasis (patternFiniteClass R) (patternBound (Fintype.card Q) w)

theorem patternBasis_spec (R : Finset (RootedPattern Q)) (w : ℕ)
    (hw : ∀ p ∈ R, p.dataCount ≤ w) (G : FiniteGraph 3) :
    PatternClass R G.2 ↔ ∀ A ∈ patternBasis R w, ¬ A.Contains G := by
  exact FiniteGraph.forbiddenBasis_spec _ _ (patternFiniteClass_monotone R)
    (patternFiniteClass_bounded R w hw) G

theorem patternClass_edgeless (R : Finset (RootedPattern Q))
    (hedges : ∀ p ∈ R, p.graph.edges.Nonempty) (G : RGraph V 3) (hG : G.edges = ∅) :
    PatternClass R G := by
  refine ⟨Rooting.empty, ?_⟩
  intro p hp ⟨f, hf⟩
  obtain ⟨e, he⟩ := hedges p hp
  have h := hf.embedding.2 e he
  rw [hG] at h
  exact Finset.notMem_empty _ h

theorem patternBasis_has_edges (R : Finset (RootedPattern Q)) (w : ℕ)
    (hedges : ∀ p ∈ R, p.graph.edges.Nonempty)
    {A : FiniteGraph 3} (hA : A ∈ patternBasis R w) : A.2.edges.Nonempty := by
  exact FiniteGraph.forbiddenBasis_has_edges _ _
    (fun G hG => patternClass_edgeless R hedges G.2 hG) hA

end TranscendentalTuran.Encoding
