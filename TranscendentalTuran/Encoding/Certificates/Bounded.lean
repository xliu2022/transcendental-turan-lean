module

public import TranscendentalTuran.Encoding.Certificates.Declarations

@[expose] public section

namespace TranscendentalTuran.Source.Certificates

open TuranUniversality Encoding Network Parameters
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem bounded_pattern_of_unique_declarations
    (hunique : ∀ x τ σ, Declared G μ τ x → Declared G μ σ x → τ = σ)
    (hbad : ¬ RootedLegal G μ) :
    ∃ p : RootedPattern Root, p.rootCount ≤ 40 ∧ p.dataCount ≤ 13 ∧
      p.TransferCompatible Γ ∧ ¬ RootedLegal p.graph p.canonical ∧ p.Realizes G μ := by
  classical
  obtain ⟨w⟩ := exists_selectedWitness hbad
  have hs (x : w.data) := select_declaration_support hunique x.val
  choose declRoots hdeclCard hdeclPresent hdeclSupport using hs
  let declarations : Finset Root := Finset.univ.biUnion declRoots
  let markers : Finset Root := markerPair.filter (fun r => ∃ v, μ.val r = some v)
  let labels := (w.labels ∪ declarations) ∪ markers
  have hdeclarations : declarations.card ≤ 2 * w.data.card := by
    calc
      declarations.card ≤ ∑ x : w.data, (declRoots x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x : w.data, 2 := Finset.sum_le_sum (fun x _ => hdeclCard x)
      _ = 2 * w.data.card := by simp [Nat.mul_comm]
  have hmarkers : markers.card ≤ 2 := by
    exact (Finset.card_filter_le _ _).trans (by rw [markerPair_card])
  have hlabelCard : labels.card ≤ 40 := by
    have h₁ := Finset.card_union_le w.labels declarations
    have h₂ := Finset.card_union_le (w.labels ∪ declarations) markers
    have hw := w.labels_bound
    have hd := w.data_bound
    dsimp [labels]
    omega
  have hpresent : ∀ r ∈ labels, ∃ v, μ.val r = some v := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_union.mp hr with hr | hr
      · exact w.labels_present r hr
      · obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hr
        exact hdeclPresent x r hx
    · exact (Finset.mem_filter.mp hr).2
  have hvalues (r : labels) : ∃ v, μ.val r.val = some v := hpresent _ r.property
  choose values hvalues using hvalues
  let S : Slice μ := ⟨w.data, labels, w.data_status, values, hvalues⟩
  let p := S.pattern G
  let f : w.data ↪ p.Vertices :=
    ⟨fun x => Sum.inr (S.dataIndex x), fun _ _ h => S.dataIndex.injective (Sum.inr.inj h)⟩
  have hdeclSubset (x : w.data) : declRoots x ⊆ labels := by
    intro r hr
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hr⟩
  have F : Replay G μ w.data w.labels p.graph p.canonical := by
    refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact S.data_out G x
    · intro x τ hx
      obtain ⟨t, ht⟩ := hdeclSupport x τ hx
      exact DeclarationToken.lift S x t (ht.trans (hdeclSubset x))
    · intro x hx
      have hxcopy := hx
      obtain ⟨_, u, v, hu, hv, _⟩ := hxcopy
      have hl : markerLeft ∈ labels := by
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨by simp [markerPair], ⟨u, hu⟩⟩
      have hr : markerRight ∈ labels := by
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨by simp [markerPair], ⟨v, hv⟩⟩
      exact S.lift_pairLink G ⟨markerLeft, hl⟩ ⟨markerRight, hr⟩ x marker_roots_in_Γ hx
    · intro r hr x y he
      have hrl : r ∈ labels := Finset.mem_union_left _ (Finset.mem_union_left _ hr)
      exact S.lift_link G ⟨r, hrl⟩ x y he
    · intro x y z he
      exact S.lift_triple G x y z he
  exact ⟨p, hlabelCard, w.data_bound, S.compatible G,
    w.fails p.graph p.canonical F, S.toHost, S.matches_host G⟩

theorem bounded_pattern_of_declaration_conflict {x : V} {τ σ : PhysicalType}
    (hx : Declared G μ τ x) (hy : Declared G μ σ x) (hne : τ ≠ σ) :
    ∃ p : RootedPattern Root, p.rootCount ≤ 40 ∧ p.dataCount ≤ 13 ∧
      p.TransferCompatible Γ ∧ ¬ RootedLegal p.graph p.canonical ∧ p.Realizes G μ := by
  classical
  obtain ⟨s⟩ := DeclarationToken.exists_of_declared hx
  obtain ⟨t⟩ := DeclarationToken.exists_of_declared hy
  let labels := s.labels ∪ t.labels
  have hcard : labels.card ≤ 40 := by
    have h := Finset.card_union_le s.labels t.labels
    have hs := s.labels_card
    have ht := t.labels_card
    dsimp [labels]
    omega
  have hpresent : ∀ r ∈ labels, ∃ v, μ.val r = some v := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact s.labels_present r hr
    · exact t.labels_present r hr
  have hvalues (r : labels) : ∃ v, μ.val r.val = some v := hpresent _ r.property
  choose values hvalues using hvalues
  let S : Slice μ :=
    ⟨{x}, labels, (by intro y hy; obtain rfl := Finset.mem_singleton.mp hy; exact hx.1),
      values, hvalues⟩
  let x' : S.data := ⟨x, Finset.mem_singleton_self x⟩
  refine ⟨S.pattern G, hcard, by simp [Slice.pattern, S], S.compatible G, ?_,
    S.toHost, S.matches_host G⟩
  intro hlegal
  exact hne (hlegal.declarations_unique _ _ _
    (DeclarationToken.lift S x' s Finset.subset_union_left)
    (DeclarationToken.lift S x' t Finset.subset_union_right))

/-- The concrete source class has the exact positive certificate size
claimed by the manuscript. This theorem constructs an ordinary finite
three-graph pattern, an injective host match, and its failed canonical
rooting; no abstract bounded-certificate hypothesis is used. -/
theorem exists_bounded_pattern (hbad : ¬ RootedLegal G μ) :
    ∃ p : RootedPattern Root, p.rootCount ≤ 40 ∧ p.dataCount ≤ 13 ∧
      p.TransferCompatible Γ ∧ ¬ RootedLegal p.graph p.canonical ∧ p.Realizes G μ := by
  classical
  by_cases hunique : ∀ x τ σ, Declared G μ τ x → Declared G μ σ x → τ = σ
  · exact bounded_pattern_of_unique_declarations hunique hbad
  · push Not at hunique
    obtain ⟨x, τ, σ, hx, hy, hne⟩ := hunique
    exact bounded_pattern_of_declaration_conflict hx hy hne

end TranscendentalTuran.Source.Certificates
