module

public import TranscendentalTuran.Network.ParentDepth
public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

/-!
# Coordinates supplied by the actual owner relations

Formalization author and responsible maintainer: Xizhi Liu.

The coordinate domain is the component of a marked complete base. Owners
outside this component can have cycles or self-arrows; no global acyclicity
is assumed. Boundary rules and uniqueness of parents suffice on this domain.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

/-- A base with both of its actual owner incidences. -/
structure OwnedBase (G : RGraph V 3) (μ : Rooting Root V) where
  vertex : V
  horizontal : V
  vertical : V
  horizontal_edge : OwnerEdge G μ 0 vertex horizontal
  vertical_edge : OwnerEdge G μ 1 vertex vertical

theorem OwnedBase.vertex_injective (h : RootedLegal G μ) :
    Function.Injective (OwnedBase.vertex : OwnedBase G μ → V) := by
  intro x y he
  have hh := h.owner_functional 0 x.vertex x.horizontal y.horizontal
    x.horizontal_edge (he ▸ y.horizontal_edge)
  have hv := h.owner_functional 1 x.vertex x.vertical y.vertical
    x.vertical_edge (he ▸ y.vertical_edge)
  cases x
  cases y
  simp_all

theorem marked_horizontal_no_parent (h : RootedLegal G μ) {m o : V}
    (hm : Marked G μ m) (ho : OwnerEdge G μ 0 m o) :
    ∀ a, ¬ ParentH G μ a o := by
  rintro a ⟨x, y, hxy, hxa, hyo⟩
  exact h.boundaryH m y x o hm ho hyo hxy

theorem marked_vertical_no_parent (h : RootedLegal G μ) {m o : V}
    (hm : Marked G μ m) (ho : OwnerEdge G μ 1 m o) :
    ∀ a, ¬ ParentV G μ a o := by
  rintro a ⟨x, y, hxy, hya, hxo⟩
  exact h.boundaryV m x y o hm ho hxo hxy

namespace OwnedBase

variable (p : OwnedBase G μ)

def CoordinateDomain (x : OwnedBase G μ) : Prop :=
  ParentDepth.Reachable (ParentH G μ) p.horizontal x.horizontal ∧
  ParentDepth.Reachable (ParentV G μ) p.vertical x.vertical

noncomputable def coordinates (x : OwnedBase G μ) : ℕ × ℕ :=
  (ParentDepth.depth (ParentH G μ) p.horizontal x.horizontal,
   ParentDepth.depth (ParentV G μ) p.vertical x.vertical)

def Adjacent (x y : OwnedBase G μ) : Prop :=
  CompleteE G μ x.vertex y.vertex ∨ CompleteD G μ x.vertex y.vertex ∨
  CompleteE G μ y.vertex x.vertex ∨ CompleteD G μ y.vertex x.vertex

def InComponent (x : OwnedBase G μ) : Prop := Relation.ReflTransGen Adjacent p x

theorem coordinateDomain_self : p.CoordinateDomain p :=
  ⟨⟨0, .here⟩, ⟨0, .here⟩⟩

variable {p} (h : RootedLegal G μ) (hm : Marked G μ p.vertex)
include h hm

theorem coordinates_self : p.coordinates p = (0, 0) := by
  unfold coordinates
  rw [ParentDepth.depth_root
      (marked_horizontal_no_parent h hm p.horizontal_edge) h.parentH_unique,
    ParentDepth.depth_root
      (marked_vertical_no_parent h hm p.vertical_edge) h.parentV_unique]

theorem coordinateDomain_E {x y : OwnedBase G μ}
    (he : CompleteE G μ x.vertex y.vertex) :
    p.CoordinateDomain x ↔ p.CoordinateDomain y := by
  have hh : ParentH G μ x.horizontal y.horizontal :=
    ⟨x.vertex, y.vertex, Or.inl he, x.horizontal_edge, y.horizontal_edge⟩
  have hv := h.E_preserves_vertical _ _ _ _ he x.vertical_edge y.vertical_edge
  constructor
  · rintro ⟨hx, hxx⟩
    exact ⟨ParentDepth.reachable_forward hx hh, hv ▸ hxx⟩
  · rintro ⟨hy, hyy⟩
    exact ⟨ParentDepth.reachable_backward
      (marked_horizontal_no_parent h hm p.horizontal_edge) h.parentH_unique hy hh,
      hv ▸ hyy⟩

theorem coordinateDomain_D {x y : OwnedBase G μ}
    (hd : CompleteD G μ x.vertex y.vertex) :
    p.CoordinateDomain x ↔ p.CoordinateDomain y := by
  have hh : ParentH G μ x.horizontal y.horizontal :=
    ⟨x.vertex, y.vertex, Or.inr hd, x.horizontal_edge, y.horizontal_edge⟩
  have hv : ParentV G μ y.vertical x.vertical :=
    ⟨x.vertex, y.vertex, hd, y.vertical_edge, x.vertical_edge⟩
  constructor
  · rintro ⟨hx, hxx⟩
    exact ⟨ParentDepth.reachable_forward hx hh, ParentDepth.reachable_backward
      (marked_vertical_no_parent h hm p.vertical_edge) h.parentV_unique hxx hv⟩
  · rintro ⟨hy, hyy⟩
    exact ⟨ParentDepth.reachable_backward
      (marked_horizontal_no_parent h hm p.horizontal_edge) h.parentH_unique hy hh,
      ParentDepth.reachable_forward hyy hv⟩

theorem coordinateDomain_adjacent {x y : OwnedBase G μ} (hxy : Adjacent x y) :
    p.CoordinateDomain x ↔ p.CoordinateDomain y := by
  rcases hxy with he | hd | he | hd
  · exact coordinateDomain_E h hm he
  · exact coordinateDomain_D h hm hd
  · exact (coordinateDomain_E h hm he).symm
  · exact (coordinateDomain_D h hm hd).symm

theorem coordinateDomain_of_component {x : OwnedBase G μ} (hx : p.InComponent x) :
    p.CoordinateDomain x := by
  induction hx with
  | refl => exact p.coordinateDomain_self
  | tail _ hxy ih => exact (coordinateDomain_adjacent h hm hxy).mp ih

/-- An east chain changes exactly the horizontal parent depth. -/
theorem coordinates_E {x y : OwnedBase G μ} (hx : p.CoordinateDomain x)
    (he : CompleteE G μ x.vertex y.vertex) :
    (p.coordinates y).1 = (p.coordinates x).1 + 1 ∧
      (p.coordinates y).2 = (p.coordinates x).2 := by
  constructor
  · exact ParentDepth.depth_step
      (marked_horizontal_no_parent h hm p.horizontal_edge) h.parentH_unique hx.1
      ⟨x.vertex, y.vertex, Or.inl he, x.horizontal_edge, y.horizontal_edge⟩
  · unfold coordinates
    rw [h.E_preserves_vertical _ _ _ _ he x.vertical_edge y.vertical_edge]

/-- A southeast chain increases horizontal depth and decreases vertical depth. -/
theorem coordinates_D {x y : OwnedBase G μ} (hx : p.CoordinateDomain x)
    (hd : CompleteD G μ x.vertex y.vertex) :
    (p.coordinates y).1 = (p.coordinates x).1 + 1 ∧
      (p.coordinates x).2 = (p.coordinates y).2 + 1 := by
  exact ⟨ParentDepth.depth_step
      (marked_horizontal_no_parent h hm p.horizontal_edge) h.parentH_unique hx.1
      ⟨x.vertex, y.vertex, Or.inr hd, x.horizontal_edge, y.horizontal_edge⟩,
    ParentDepth.depth_step_back
      (marked_vertical_no_parent h hm p.vertical_edge) h.parentV_unique hx.2
      ⟨x.vertex, y.vertex, hd, y.vertical_edge, x.vertical_edge⟩⟩

theorem no_E_loop {x : OwnedBase G μ} (hx : p.CoordinateDomain x) :
    ¬ CompleteE G μ x.vertex x.vertex := by
  intro he
  have hcoord := (coordinates_E h hm hx he).1
  omega

theorem no_D_loop {x : OwnedBase G μ} (hx : p.CoordinateDomain x) :
    ¬ CompleteD G μ x.vertex x.vertex := by
  intro hd
  have hcoord := (coordinates_D h hm hx hd).1
  omega

end OwnedBase

end TranscendentalTuran.Source
