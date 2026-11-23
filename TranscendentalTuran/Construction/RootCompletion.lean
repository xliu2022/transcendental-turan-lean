module

public import TranscendentalTuran.Encoding.Certificates.ParentWitnesses
public import TranscendentalTuran.Encoding.Certificates.Declarations
public import TranscendentalTuran.Construction.TotalRooting
public import TuranUniversality.Weighted.Model
public import TuranUniversality.Density.WeightedHomPushforward

@[expose] public section

/-!
# Completing an actual partial rooting

Missing roots are added as new vertices. Existing data are retained, all
root triples and all neutral root-pair triples are added, and no new
declaration, mark, or one-root link is introduced.
-/

namespace TranscendentalTuran.Source.Completion

open TuranUniversality Encoding Certificates

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

variable {V : Type} [DecidableEq V]

abbrev DataVertex (μ : Rooting Root V) := {v : V // Data μ v}
abbrev Vertex (μ : Rooting Root V) := Root ⊕ DataVertex μ

noncomputable instance [Fintype V] (μ : Rooting Root V) : Fintype (DataVertex μ) :=
  Fintype.ofFinite _

def rooting (μ : Rooting Root V) : Rooting Root (Vertex μ) := sumRooting (DataVertex μ)

@[simp] theorem rooting_val (μ : Rooting Root V) (r : Root) :
    (rooting μ).val r = some (Sum.inl r) := rfl

@[simp] theorem inl_not_data (μ : Rooting Root V) (r : Root) :
    ¬ Data (rooting μ) (Sum.inl r) := by
  intro h
  exact h ((Rooting.mem_range _ _).mpr ⟨r, rfl⟩)

@[simp] theorem inr_data (μ : Rooting Root V) (x : DataVertex μ) :
    Data (rooting μ) (Sum.inr x) := by
  intro h
  obtain ⟨r, hr⟩ := (Rooting.mem_range _ _).mp h
  cases hr

theorem data_exists (μ : Rooting Root V) {v : Vertex μ} (hv : Data (rooting μ) v) :
    ∃ x : DataVertex μ, v = Sum.inr x := by
  cases v with
  | inl r => exact False.elim (inl_not_data μ r hv)
  | inr x => exact ⟨x, rfl⟩

/-- The original vertex injection, with roots relabeled by their unique
root labels and data unchanged. -/
noncomputable def vertexMap (μ : Rooting Root V) (v : V) : Vertex μ :=
  if h : v ∈ μ.range then Sum.inl ((Rooting.mem_range μ v).mp h).choose
  else Sum.inr ⟨v, h⟩

theorem vertexMap_root (μ : Rooting Root V) {v : V} {r : Root}
    (hr : μ.val r = some v) : vertexMap μ v = Sum.inl r := by
  classical
  have hv := (Rooting.mem_range μ v).mpr ⟨r, hr⟩
  rw [vertexMap, dite_eq_left hv]
  congr 1
  exact μ.property _ r v ((Rooting.mem_range μ v).mp hv).choose_spec hr

theorem vertexMap_data (μ : Rooting Root V) (v : V) (hv : Data μ v) :
    vertexMap μ v = Sum.inr ⟨v, hv⟩ := by
  classical
  exact dite_eq_right hv

@[simp] theorem vertexMap_inl_iff (μ : Rooting Root V) (v : V) (r : Root) :
    vertexMap μ v = Sum.inl r ↔ μ.val r = some v := by
  classical
  constructor
  · intro h
    by_cases hv : v ∈ μ.range
    · rw [vertexMap, dite_eq_left hv] at h
      have hr := Sum.inl.inj h
      exact hr ▸ ((Rooting.mem_range μ v).mp hv).choose_spec
    · rw [vertexMap, dite_eq_right hv] at h
      cases h
  · exact vertexMap_root μ

@[simp] theorem vertexMap_inr_iff (μ : Rooting Root V) (v : V) (x : DataVertex μ) :
    vertexMap μ v = Sum.inr x ↔ v = x.val := by
  classical
  constructor
  · intro h
    by_cases hv : v ∈ μ.range
    · rw [vertexMap, dite_eq_left hv] at h
      cases h
    · rw [vertexMap, dite_eq_right hv] at h
      exact congrArg Subtype.val (Sum.inr.inj h)
  · rintro rfl
    exact vertexMap_data μ x.val x.property

theorem vertexMap_injective (μ : Rooting Root V) : Function.Injective (vertexMap μ) := by
  intro a b hab
  cases he : vertexMap μ a with
  | inl r =>
    have ha := (vertexMap_inl_iff μ a r).mp he
    have hb := (vertexMap_inl_iff μ b r).mp (hab.symm.trans he)
    exact Option.some.inj (ha.symm.trans hb)
  | inr x =>
    exact ((vertexMap_inr_iff μ a x).mp he).trans
      ((vertexMap_inr_iff μ b x).mp (hab.symm.trans he)).symm

/-- The complete graph has exactly the old edges, root triples, and
neutral-pair triples. Its filtering description keeps all finite semantics
visible without evaluating the immense root set. -/
noncomputable def graph [Fintype V] (G : RGraph V 3) (μ : Rooting Root V) :
    RGraph (Vertex μ) 3 := by
  classical
  exact ⟨Finset.univ.powersetCard 3 |>.filter (fun e =>
      e.toRight = ∅ ∨ (e.toRight.card = 1 ∧ e.toLeft ∉ Γ) ∨
        ∃ d ∈ G.edges, d.image (vertexMap μ) = e),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

theorem mem_graph [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (e : Finset (Vertex μ)) : e ∈ (graph G μ).edges ↔
      e.card = 3 ∧ (e.toRight = ∅ ∨ (e.toRight.card = 1 ∧ e.toLeft ∉ Γ) ∨
        ∃ d ∈ G.edges, d.image (vertexMap μ) = e) := by
  classical
  simp only [graph, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

theorem vertexMap_embedding [Fintype V] (G : RGraph V 3) (μ : Rooting Root V) :
    G.IsEmbedding (graph G μ) (vertexMap μ) := by
  refine ⟨vertexMap_injective μ, ?_⟩
  intro e he
  exact (mem_graph G μ _).mpr ⟨by
    rw [Finset.card_image_of_injective _ (vertexMap_injective μ)]
    exact G.uniform e he, Or.inr (Or.inr ⟨e, he, rfl⟩)⟩

theorem graph_root_clique [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (e : Finset Root) (he : e.card = 3) :
    e.image (Sum.inl : Root → Vertex μ) ∈ (graph G μ).edges := by
  apply (mem_graph G μ _).mpr
  refine ⟨?_, Or.inl ?_⟩
  · rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact he
  · ext x
    simp

theorem graph_neutral_pair [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (p : Finset Root) (hp : p.card = 2) (hne : p ∉ Γ) (x : DataVertex μ) :
    insert (Sum.inr x) (p.image Sum.inl) ∈ (graph G μ).edges := by
  apply (mem_graph G μ _).mpr
  refine ⟨?_, Or.inr (Or.inl ?_)⟩
  · simp [Finset.card_image_of_injective, Sum.inl_injective, hp]
  · have hr : (p.image (Sum.inl : Root → Vertex μ)).toRight = ∅ := by ext y; simp
    have hl : (p.image (Sum.inl : Root → Vertex μ)).toLeft = p := by ext r; simp
    simpa [hr, hl] using hne

theorem link_reflect [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (r : Root) (x y : DataVertex μ)
    (h : Link (graph G μ) (rooting μ) r (Sum.inr x) (Sum.inr y)) :
    Link G μ r x.val y.val := by
  classical
  have he := (sumRooting_link (graph G μ) r x y).mp h
  have hxy : x ≠ y := by
    intro heq
    subst y
    have hc := (graph G μ).uniform _ he
    simp at hc
  have hold : ∃ e ∈ G.edges, e.image (vertexMap μ) =
      {Sum.inl r, Sum.inr x, Sum.inr y} := by
    rcases ((mem_graph G μ _).mp he).2 with hr | hn | ho
    · simp at hr
    · have hc := hn.1
      simp [hxy] at hc
    · exact ho
  obtain ⟨e, heG, him⟩ := hold
  have hrmem : Sum.inl r ∈ e.image (vertexMap μ) := by rw [him]; simp
  obtain ⟨v, _hv, hmap⟩ := Finset.mem_image.mp hrmem
  have hr := (vertexMap_inl_iff μ v r).mp hmap
  have hsame : ({v, x.val, y.val} : Finset V).image (vertexMap μ) =
      {Sum.inl r, Sum.inr x, Sum.inr y} := by
    simp only [Finset.image_insert, Finset.image_singleton, vertexMap_root μ hr,
      vertexMap_data μ x.val x.property, vertexMap_data μ y.val y.property]
  have heq : e = {v, x.val, y.val} :=
    Finset.image_injective (vertexMap_injective μ) (him.trans hsame.symm)
  exact ⟨x.property, y.property, v, hr, heq ▸ heG⟩

theorem pairLink_reflect [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (r s : Root) (x : DataVertex μ) (hrs : ({r, s} : Finset Root) ∈ Γ)
    (h : PairLink (graph G μ) (rooting μ) r s (Sum.inr x)) : PairLink G μ r s x.val := by
  classical
  have he := (sumRooting_pairLink (graph G μ) r s x).mp h
  have hold : ∃ e ∈ G.edges, e.image (vertexMap μ) =
      {Sum.inl r, Sum.inl s, Sum.inr x} := by
    rcases ((mem_graph G μ _).mp he).2 with hr | hn | ho
    · simp at hr
    · exact False.elim (hn.2 (by simpa using hrs))
    · exact ho
  obtain ⟨e, heG, him⟩ := hold
  have hrmem : Sum.inl r ∈ e.image (vertexMap μ) := by rw [him]; simp
  have hsmem : Sum.inl s ∈ e.image (vertexMap μ) := by rw [him]; simp
  obtain ⟨u, _hu, humap⟩ := Finset.mem_image.mp hrmem
  obtain ⟨v, _hv, hvmap⟩ := Finset.mem_image.mp hsmem
  have hr := (vertexMap_inl_iff μ u r).mp humap
  have hs := (vertexMap_inl_iff μ v s).mp hvmap
  have hsame : ({u, v, x.val} : Finset V).image (vertexMap μ) =
      {Sum.inl r, Sum.inl s, Sum.inr x} := by
    simp only [Finset.image_insert, Finset.image_singleton, vertexMap_root μ hr,
      vertexMap_root μ hs, vertexMap_data μ x.val x.property]
  have heq : e = {u, v, x.val} :=
    Finset.image_injective (vertexMap_injective μ) (him.trans hsame.symm)
  exact ⟨x.property, u, v, hr, hs, heq ▸ heG⟩

theorem marked_reflect [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (x : DataVertex μ) (h : Marked (graph G μ) (rooting μ) (Sum.inr x)) :
    Marked G μ x.val := pairLink_reflect G μ _ _ x marker_roots_in_Γ h

theorem declared_reflect [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (τ : Network.PhysicalType) (x : DataVertex μ)
    (h : Declared (graph G μ) (rooting μ) τ (Sum.inr x)) : Declared G μ τ x.val := by
  refine ⟨x.property, ?_⟩
  rcases h.2 with ⟨j, hj⟩ | ⟨ht, hm⟩
  · exact Or.inl ⟨j, pairLink_reflect G μ _ _ x
      (declaring_roots_in_Γ (physicalIndex τ, j)) hj⟩
  · exact Or.inr ⟨ht, marked_reflect G μ x hm⟩

theorem data_triple_reflect [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (x y z : DataVertex μ)
    (he : {Sum.inr x, Sum.inr y, Sum.inr z} ∈ (graph G μ).edges) :
    {x.val, y.val, z.val} ∈ G.edges := by
  classical
  have hc : ({x, y, z} : Finset (DataVertex μ)).card = 3 := by
    have hi := Finset.card_image_of_injective ({x, y, z} : Finset (DataVertex μ))
      (Sum.inr_injective : Function.Injective (Sum.inr : DataVertex μ → Vertex μ))
    rw [← hi]
    simpa only [Finset.image_insert, Finset.image_singleton] using (graph G μ).uniform _ he
  have hold : ∃ e ∈ G.edges, e.image (vertexMap μ) =
      {Sum.inr x, Sum.inr y, Sum.inr z} := by
    rcases ((mem_graph G μ _).mp he).2 with hr | hn | ho
    · simp at hr
    · have hh := hn.1
      simp [hc] at hh
    · exact ho
  obtain ⟨e, heG, him⟩ := hold
  have hsame : ({x.val, y.val, z.val} : Finset V).image (vertexMap μ) =
      {Sum.inr x, Sum.inr y, Sum.inr z} := by
    simp only [Finset.image_insert, Finset.image_singleton,
      vertexMap_data μ x.val x.property, vertexMap_data μ y.val y.property,
      vertexMap_data μ z.val z.property]
  have heq : e = {x.val, y.val, z.val} :=
    Finset.image_injective (vertexMap_injective μ) (him.trans hsame.symm)
  exact heq ▸ heG

/-- Completion is conservative for every actual positive violation. -/
theorem rootedLegal [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (hG : RootedLegal G μ) : RootedLegal (graph G μ) (rooting μ) := by
  classical
  by_contra hbad
  obtain ⟨S⟩ := exists_selectedWitness hbad
  let pick (x : S.data) : DataVertex μ :=
    (data_exists μ (S.data_status x.val x.property)).choose
  have hpick (x : S.data) : x.val = Sum.inr (pick x) :=
    (data_exists μ (S.data_status x.val x.property)).choose_spec
  have hinj : Function.Injective (fun x : S.data => (pick x).val) := by
    intro x y hxy
    apply Subtype.ext
    rw [hpick x, hpick y]
    exact congrArg Sum.inr (Subtype.ext hxy)
  let F : Replay (graph G μ) (rooting μ) S.data S.labels G μ :=
    { map := ⟨fun x => (pick x).val, hinj⟩
      data := fun x => (pick x).property
      declared := fun x τ h => declared_reflect G μ τ (pick x) (hpick x ▸ h)
      marked := fun x h => marked_reflect G μ (pick x) (hpick x ▸ h)
      link := fun r _ x y h => link_reflect G μ r (pick x) (pick y)
        (by simpa only [hpick x, hpick y] using h)
      triples := fun x y z h => data_triple_reflect G μ (pick x) (pick y) (pick z)
        (by simpa only [hpick x, hpick y, hpick z] using h) }
  exact S.fails G μ F hG

theorem polynomial_le_completion [Fintype V] (G : RGraph V 3) (μ : Rooting Root V)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ w : Vertex μ → ℝ, ProbabilityWeights w ∧
      G.edgePolynomial x ≤ (graph G μ).edgePolynomial w := by
  refine ⟨Density.pushforwardWeight (vertexMap μ) x,
    Density.pushforwardWeight_probability (vertexMap μ) x hx, ?_⟩
  exact G.edgePolynomial_le_pushforward (graph G μ) (vertexMap μ)
    (vertexMap_embedding G μ).isHom x hx.1

end TranscendentalTuran.Source.Completion
