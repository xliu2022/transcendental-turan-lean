module

public import TranscendentalTuran.Network.LayerEnergy
public import TranscendentalTuran.Network.StarPairs
public import TranscendentalTuran.Network.PairPolynomial
public import TranscendentalTuran.Encoding.Certificates.DecidableRules

@[expose] public section

/-!
# The weighted pair bound for an actual special-root link

Formalization author and responsible maintainer: Xizhi Liu.

The input is the ordinary host and its rooted legality. The output bounds
the actual finite pair graph in an individual root link by its signed-star
square expression, using its actual component energy.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

theorem link_ne {r : Root} {x y : V} (h : Link G μ r x y) : x ≠ y := by
  obtain ⟨hx, hy, v, hv, he⟩ := h
  have hvx : v ≠ x := by
    intro hh
    subst x
    exact hx ((Rooting.mem_range μ v).mpr ⟨r, hv⟩)
  intro hxy
  subst y
  have hc := G.uniform {v, x, x} he
  simp [hvx] at hc

abbrev LayerVertex (G : RGraph V 3) (μ : Rooting Root V) (b : Block) :=
  PositiveVertex G μ b ⊕ NegativeVertex G μ b

def layerVertexVal (b : Block) : LayerVertex G μ b → V :=
  Sum.elim Subtype.val Subtype.val

theorem layerVertexVal_injective (h : RootedLegal G μ) (b : Block) :
    Function.Injective (layerVertexVal (G := G) (μ := μ) b) := by
  intro a c he
  cases a with
  | inl a =>
    cases c with
    | inl c => exact congrArg Sum.inl (Subtype.ext he)
    | inr c =>
      change a.val = c.val at he
      exact False.elim (positive_negative_disjoint h b a.val a.property (he ▸ c.property))
  | inr a =>
    cases c with
    | inl c =>
      change a.val = c.val at he
      exact False.elim (positive_negative_disjoint h b a.val (he ▸ c.property) a.property)
    | inr c => exact congrArg Sum.inr (Subtype.ext he)

theorem layerVertexVal_range (b : Block) (x : V) :
    x ∈ Set.range (layerVertexVal (G := G) (μ := μ) b) ↔
      PositiveAt G μ b x ∨ NegativeAt G μ b x := by
  constructor
  · rintro ⟨a, rfl⟩
    cases a with
    | inl a => exact Or.inl a.property
    | inr a => exact Or.inr a.property
  · rintro (hp | hn)
    · exact ⟨Sum.inl ⟨x, hp⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hn⟩, rfl⟩

theorem active_declared_sign {b : Block} {x : V} {τ : PhysicalType}
    (ht : Declared G μ τ x) (ha : Active b τ) :
    PositiveAt G μ b x ∨ NegativeAt G μ b x := by
  rcases sign_trichotomy b τ with hn | hz | hp
  · exact Or.inr ⟨τ, ht, hn⟩
  · exact False.elim (ha hz)
  · exact Or.inl ⟨τ, ht, hp⟩

theorem link_active_endpoints (h : RootedLegal G μ)
    (ht : ∀ x, Data μ x → ∃ τ, Declared G μ τ x)
    (r : Layer) {x y : V} (hl : Link G μ (layerRoot r) x y) :
    x ∈ Set.range (layerVertexVal (G := G) (μ := μ) r.1) ∧
      y ∈ Set.range (layerVertexVal (G := G) (μ := μ) r.1) := by
  obtain ⟨τ, hτ⟩ := ht x hl.1
  obtain ⟨σ, hσ⟩ := ht y hl.2.1
  have ha := h.special_allowed r x y τ σ hτ hσ hl
  exact ⟨(layerVertexVal_range r.1 x).mpr (active_declared_sign hτ ha.1),
    (layerVertexVal_range r.1 y).mpr (active_declared_sign hσ ha.2.1)⟩

theorem link_permitted (h : RootedLegal G μ) (r : Layer)
    (a b : LayerVertex G μ r.1)
    (hl : Link G μ (layerRoot r) (layerVertexVal r.1 a) (layerVertexVal r.1 b)) :
    StarEnergy.PermittedPair (leafCenter (G := G) (μ := μ) r) a b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      intro he
      exact link_ne hl (congrArg Subtype.val he)
    | inr b => exact (leafCenter_some_iff h r b a).mpr ⟨a.property, b.property, hl⟩
  | inr a =>
    cases b with
    | inl b => exact (leafCenter_some_iff h r a b).mpr ⟨b.property, a.property, link_symm hl⟩
    | inr b =>
      constructor
      · intro he
        exact link_ne hl (congrArg Subtype.val he)
      · rintro ⟨c, hca, hcb⟩
        exact no_pair_inside_star h r
          ((leafCenter_some_iff h r a c).mp hca)
          ((leafCenter_some_iff h r b c).mp hcb) hl

theorem actualLink_ordered_bound (h : RootedLegal G μ)
    (ht : ∀ x, Data μ x → ∃ τ, Declared G μ τ x)
    (r : Layer) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, ∑ y, if Link G μ (layerRoot r) x y then w x * w y else 0) ≤
      (∑ c : PositiveVertex G μ r.1, w c.val) ^ 2 +
      (∑ l : NegativeVertex G μ r.1, w l.val) ^ 2 -
        actualLayerEnergy (G := G) (μ := μ) r w := by
  classical
  let e : LayerVertex G μ r.1 → V := layerVertexVal r.1
  let F : V → V → ℝ := fun x y =>
    if Link G μ (layerRoot r) x y then w x * w y else 0
  have he : Function.Injective e := layerVertexVal_injective h r.1
  have hsecond (x : V) : (∑ b, F x (e b)) = ∑ y, F x y := by
    apply Fintype.sum_of_injective e he _ _ _ (fun _ => rfl)
    intro y hy
    have hn : ¬ Link G μ (layerRoot r) x y :=
      fun hl => hy (link_active_endpoints h ht r hl).2
    simp [F, hn]
  have hsum : (∑ a, ∑ b, F (e a) (e b)) = ∑ x, ∑ y, F x y := by
    simp_rw [hsecond]
    apply Fintype.sum_of_injective e he
      (fun a => ∑ y, F (e a) y) (fun x => ∑ y, F x y) _ (fun _ => rfl)
    intro x hx
    apply Finset.sum_eq_zero
    intro y _
    have hn : ¬ Link G μ (layerRoot r) x y :=
      fun hl => hx (link_active_endpoints h ht r hl).1
    simp [F, hn]
  change (∑ x, ∑ y, F x y) ≤ _
  rw [← hsum]
  calc
    _ ≤ ∑ a : LayerVertex G μ r.1, ∑ b : LayerVertex G μ r.1,
        if StarEnergy.PermittedPair (leafCenter r) a b then w (e a) * w (e b) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases hl : Link G μ (layerRoot r) (e a) (e b)
      · simp [F, hl, link_permitted h r a b hl]
      · simp only [F, hl, ite_false]
        split_ifs
        · exact mul_nonneg (hw _) (hw _)
        · exact le_rfl
    _ = _ := by
      have heval (a : LayerVertex G μ r.1) : w (e a) =
          Sum.elim (fun c => w c.val) (fun l => w l.val) a := by
        cases a <;> rfl
      simp_rw [heval]
      rw [StarEnergy.permitted_ordered_sum, actualLayer_square_identity]
      ring

/-- The actual two-uniform data link at a root label. -/
noncomputable def dataPairGraph (r : Root) : RGraph V 2 := by
  classical
  exact ⟨Finset.univ.powersetCard 2 |>.filter (fun p =>
    ∃ v, μ.val r = some v ∧ (∀ x ∈ p, Data μ x) ∧ insert v p ∈ G.edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

theorem dataPairGraph_mem_pair (r : Root) (x y : V) :
    {x, y} ∈ (dataPairGraph (G := G) (μ := μ) r).edges ↔ Link G μ r x y := by
  classical
  simp only [dataPairGraph, Finset.mem_filter]
  change ({x, y} ∈ Finset.univ.powersetCard 2 ∧
    ∃ v, μ.val r = some v ∧ (∀ a ∈ ({x, y} : Finset V), Data μ a) ∧
      insert v {x, y} ∈ G.edges) ↔ _
  constructor
  · rintro ⟨_, v, hv, hd, he⟩
    exact ⟨hd x (by simp), hd y (by simp), v, hv, he⟩
  · intro hl
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair (link_ne hl)⟩, ?_⟩
    obtain ⟨hx, hy, v, hv, he⟩ := hl
    exact ⟨v, hv, by simpa using And.intro hx hy, he⟩

theorem actualLink_polynomial_bound (h : RootedLegal G μ)
    (ht : ∀ x, Data μ x → ∃ τ, Declared G μ τ x)
    (r : Layer) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (dataPairGraph (G := G) (μ := μ) (layerRoot r)).edgePolynomial w ≤
      ((∑ c : PositiveVertex G μ r.1, w c.val) ^ 2 +
        (∑ l : NegativeVertex G μ r.1, w l.val) ^ 2 -
          actualLayerEnergy (G := G) (μ := μ) r w) / 2 := by
  classical
  have hbound := actualLink_ordered_bound h ht r w hw
  have hpair := pairGraph_ordered_sum (dataPairGraph (G := G) (μ := μ) (layerRoot r)) w
  simp only [dataPairGraph_mem_pair] at hpair
  linarith

end TranscendentalTuran.Source
