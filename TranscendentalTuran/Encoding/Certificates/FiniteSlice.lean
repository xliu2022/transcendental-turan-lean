module

public import TranscendentalTuran.Encoding.Certificates.Canonical
public import TranscendentalTuran.Encoding.Certificates.ParentWitnesses
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Encoding.Certificates Network Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {μ : Rooting Root V}

/-- An actual finite choice of data vertices and assigned root labels. -/
structure Slice (μ : Rooting Root V) where
  data : Finset V
  labels : Finset Root
  data_status : ∀ x ∈ data, Data μ x
  value : labels → V
  value_root : ∀ r, μ.val r.val = some (value r)

namespace Slice

noncomputable def rootIndex (S : Slice μ) : S.labels ≃ Fin S.labels.card := S.labels.equivFin
noncomputable def dataIndex (S : Slice μ) : S.data ≃ Fin S.data.card := S.data.equivFin

noncomputable def rootLabels (S : Slice μ) : Fin S.labels.card ↪ Root :=
  S.rootIndex.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ S.labels))

@[simp] theorem rootLabels_index (S : Slice μ) (r : S.labels) :
    S.rootLabels (S.rootIndex r) = r.val := by
  simp [rootLabels]

noncomputable def toHost (S : Slice μ) : Fin S.labels.card ⊕ Fin S.data.card → V :=
  Sum.elim (fun i => S.value (S.rootIndex.symm i)) (fun j => (S.dataIndex.symm j).val)

@[simp] theorem toHost_root (S : Slice μ) (r : S.labels) :
    S.toHost (Sum.inl (S.rootIndex r)) = S.value r := by simp [toHost]
@[simp] theorem toHost_data (S : Slice μ) (x : S.data) :
    S.toHost (Sum.inr (S.dataIndex x)) = x.val := by simp [toHost]

theorem toHost_injective (S : Slice μ) : Function.Injective S.toHost := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          have hi := S.value_root (S.rootIndex.symm i)
          have hj := S.value_root (S.rootIndex.symm j)
          have hroots := μ.property _ _ _ hi (hj.trans (congrArg some hab.symm))
          have heq : S.rootIndex.symm i = S.rootIndex.symm j := Subtype.ext hroots
          exact congrArg Sum.inl (S.rootIndex.symm.injective heq)
      | inr j =>
          have hrange : S.toHost (Sum.inl i) ∈ μ.range :=
            (Rooting.mem_range μ _).mpr ⟨(S.rootIndex.symm i).val, S.value_root _⟩
          apply False.elim
          apply S.data_status _ (S.dataIndex.symm j).property
          change S.toHost (Sum.inr j) ∈ μ.range
          rw [← hab]
          exact hrange
  | inr i =>
      cases b with
      | inl j =>
          have hrange : S.toHost (Sum.inl j) ∈ μ.range :=
            (Rooting.mem_range μ _).mpr ⟨(S.rootIndex.symm j).val, S.value_root _⟩
          apply False.elim
          apply S.data_status _ (S.dataIndex.symm i).property
          change S.toHost (Sum.inr i) ∈ μ.range
          rw [hab]
          exact hrange
      | inr j =>
          have heq : S.dataIndex.symm i = S.dataIndex.symm j := Subtype.ext hab
          exact congrArg Sum.inr (S.dataIndex.symm.injective heq)

noncomputable def embedding (S : Slice μ) : Fin S.labels.card ⊕ Fin S.data.card ↪ V :=
  ⟨S.toHost, S.toHost_injective⟩

def EdgeShape {r d : ℕ} (labels : Fin r ↪ Root) (e : Finset (Fin r ⊕ Fin d)) : Prop :=
  (∃ a b c, e = {Sum.inr a, Sum.inr b, Sum.inr c}) ∨
  (∃ r a b, e = {Sum.inl r, Sum.inr a, Sum.inr b}) ∨
  (∃ r s a, e = {Sum.inl r, Sum.inl s, Sum.inr a} ∧ {labels r, labels s} ∈ Γ)

/-- Only transferable positive triples are retained; ambient extra root
triples and neutral two-root triples play no role in a certificate. -/
noncomputable def pattern (S : Slice μ) (G : RGraph V 3) : RootedPattern Root where
  rootCount := S.labels.card
  dataCount := S.data.card
  rootLabels := S.rootLabels
  graph := by
    classical
    let J := G.pullback S.embedding
    exact ⟨J.edges.filter (EdgeShape S.rootLabels),
      fun e he => J.uniform e (Finset.mem_filter.mp he).1⟩

theorem mem_pattern (S : Slice μ) (G : RGraph V 3)
    (e : Finset (Fin S.labels.card ⊕ Fin S.data.card)) :
    e ∈ (S.pattern G).graph.edges ↔
      e.card = 3 ∧ e.image S.toHost ∈ G.edges ∧ EdgeShape S.rootLabels e := by
  classical
  change (e ∈ (G.pullback S.embedding).edges.filter (EdgeShape S.rootLabels)) ↔ _
  rw [Finset.mem_filter, G.mem_pullback, Finset.map_eq_image]
  exact and_assoc

theorem edge_mem (S : Slice μ) (G : RGraph V 3)
    {e : Finset (Fin S.labels.card ⊕ Fin S.data.card)}
    (hshape : EdgeShape S.rootLabels e) (he : e.image S.toHost ∈ G.edges) :
    e ∈ (S.pattern G).graph.edges := by
  apply (S.mem_pattern G e).mpr
  refine ⟨?_, he, hshape⟩
  rw [← Finset.card_image_of_injective e S.toHost_injective]
  exact G.uniform _ he

theorem compatible (S : Slice μ) (G : RGraph V 3) : (S.pattern G).TransferCompatible Γ := by
  intro e he
  exact ((S.mem_pattern G e).mp he).2.2

theorem matches_host (S : Slice μ) (G : RGraph V 3) : (S.pattern G).Matches G μ S.toHost := by
  refine ⟨⟨S.toHost_injective, fun e he => ((S.mem_pattern G e).mp he).2.1⟩, ?_, ?_⟩
  · intro i
    exact S.value_root (S.rootIndex.symm i)
  · intro j
    exact S.data_status _ (S.dataIndex.symm j).property

theorem root_eq (S : Slice μ) (G : RGraph V 3) (r : S.labels) :
    (S.pattern G).canonical.val r.val = some (Sum.inl (S.rootIndex r)) := by
  exact (canonicalRooting_inl S.rootLabels _ _).mpr (S.rootLabels_index r)

theorem data_out (S : Slice μ) (G : RGraph V 3) (x : S.data) :
    Data (S.pattern G).canonical (Sum.inr (S.dataIndex x)) :=
  canonicalRooting_data S.rootLabels _

theorem lift_link (S : Slice μ) (G : RGraph V 3) (r : S.labels) (x y : S.data)
    (h : Link G μ r.val x.val y.val) :
    Link (S.pattern G).graph (S.pattern G).canonical r.val
      (Sum.inr (S.dataIndex x)) (Sum.inr (S.dataIndex y)) := by
  obtain ⟨_, _, v, hv, he⟩ := h
  have hvalue : S.value r = v := Option.some.inj ((S.value_root r).symm.trans hv)
  refine ⟨S.data_out G x, S.data_out G y, Sum.inl (S.rootIndex r), S.root_eq G r, ?_⟩
  apply S.edge_mem G (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
  simpa only [Finset.image_insert, Finset.image_singleton, S.toHost_root, S.toHost_data,
    hvalue] using he

theorem lift_pairLink (S : Slice μ) (G : RGraph V 3) (r s : S.labels) (x : S.data)
    (hΓ : {r.val, s.val} ∈ Γ) (h : PairLink G μ r.val s.val x.val) :
    PairLink (S.pattern G).graph (S.pattern G).canonical r.val s.val
      (Sum.inr (S.dataIndex x)) := by
  obtain ⟨_, u, v, hu, hv, he⟩ := h
  have hru : S.value r = u := Option.some.inj ((S.value_root r).symm.trans hu)
  have hsv : S.value s = v := Option.some.inj ((S.value_root s).symm.trans hv)
  refine ⟨S.data_out G x, Sum.inl (S.rootIndex r), Sum.inl (S.rootIndex s),
    S.root_eq G r, S.root_eq G s, ?_⟩
  have hshape : EdgeShape S.rootLabels
      {Sum.inl (S.rootIndex r), Sum.inl (S.rootIndex s), Sum.inr (S.dataIndex x)} :=
    Or.inr (Or.inr ⟨_, _, _, rfl, by simpa only [S.rootLabels_index] using hΓ⟩)
  apply S.edge_mem G hshape
  simpa only [Finset.image_insert, Finset.image_singleton, S.toHost_root, S.toHost_data,
    hru, hsv] using he

theorem lift_triple (S : Slice μ) (G : RGraph V 3) (x y z : S.data)
    (he : {x.val, y.val, z.val} ∈ G.edges) :
    {Sum.inr (S.dataIndex x), Sum.inr (S.dataIndex y), Sum.inr (S.dataIndex z)} ∈
      (S.pattern G).graph.edges := by
  apply S.edge_mem G (Or.inl ⟨_, _, _, rfl⟩)
  simpa only [Finset.image_insert, Finset.image_singleton, S.toHost_data] using he

end Slice

end TranscendentalTuran.Source.Certificates
