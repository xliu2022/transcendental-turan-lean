module

public import TranscendentalTuran.Network.BaseNetwork
public import TranscendentalTuran.Network.OwnerCoordinates
public import TranscendentalTuran.Network.PrivateProjection

@[expose] public section

/-!
# The marked complete component and its private-leaf network

Formalization author and responsible maintainer: Xizhi Liu.

The center set consists of complete bases connected to the marked complete
base by complete four-edge moves. Every occupied port exiting this component
has an incomplete target. The ordinary boundary rules place every new
private leaf inside the quadrant.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Green Green.FiniteNetwork
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

noncomputable def ownedOfComplete (x : BaseVertex G μ)
    (hx : IsComplete (G := G) (μ := μ) x.val) : OwnedBase G μ where
  vertex := x.val
  horizontal := Classical.choose hx.1
  vertical := Classical.choose hx.2
  horizontal_edge := Classical.choose_spec hx.1
  vertical_edge := Classical.choose_spec hx.2

def InMarkedComponent (p : OwnedBase G μ) (x : BaseVertex G μ) : Prop :=
  ∃ a : OwnedBase G μ, a.vertex = x.val ∧ p.InComponent a

noncomputable def markedComponent (p : OwnedBase G μ) : Finset (BaseVertex G μ) := by
  classical
  exact Finset.univ.filter (InMarkedComponent p)

theorem mem_markedComponent (p : OwnedBase G μ) (x : BaseVertex G μ) :
    x ∈ markedComponent p ↔ InMarkedComponent p x := by
  classical
  simp [markedComponent]

noncomputable def componentOwned (p : OwnedBase G μ)
    (c : PrivateLeaves.Center (markedComponent p)) : OwnedBase G μ :=
  Classical.choose ((mem_markedComponent p c.val).mp c.property)

theorem componentOwned_vertex (p : OwnedBase G μ)
    (c : PrivateLeaves.Center (markedComponent p)) :
    (componentOwned p c).vertex = c.val.val :=
  (Classical.choose_spec ((mem_markedComponent p c.val).mp c.property)).1

theorem componentOwned_component (p : OwnedBase G μ)
    (c : PrivateLeaves.Center (markedComponent p)) : p.InComponent (componentOwned p c) :=
  (Classical.choose_spec ((mem_markedComponent p c.val).mp c.property)).2

def markedBase (p : OwnedBase G μ) : BaseVertex G μ :=
  ⟨p.vertex, p.horizontal_edge.1⟩

theorem markedBase_mem (p : OwnedBase G μ) : markedBase p ∈ markedComponent p :=
  (mem_markedComponent p _).mpr ⟨p, rfl, Relation.ReflTransGen.refl⟩

def markedCenter (p : OwnedBase G μ) : PrivateLeaves.Center (markedComponent p) :=
  ⟨markedBase p, markedBase_mem p⟩

theorem componentOwned_markedCenter (h : RootedLegal G μ) (p : OwnedBase G μ) :
    componentOwned p (markedCenter p) = p :=
  OwnedBase.vertex_injective h (componentOwned_vertex p (markedCenter p))

theorem logicalMove_adjacent {x y : OwnedBase G μ} (d : Fin 4)
    (he : LogicalMove G μ d x.vertex y.vertex) : OwnedBase.Adjacent x y := by
  fin_cases d
  · exact Or.inl he
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr he))
  · exact Or.inr (Or.inl he)

theorem component_exit_incomplete (h : RootedLegal G μ) (p : OwnedBase G μ)
    (e : PrivateLeaves.Exit (baseNetwork h) (markedComponent p)) :
    ¬ IsComplete (G := G) (μ := μ) e.target.val := by
  intro hc
  let x := componentOwned p e.center
  let y := ownedOfComplete e.target hc
  have he : LogicalMove G μ e.port x.vertex y.vertex := by
    have he := (baseNetwork_neighbor_iff h e.center.val e.target e.port).mp e.edge
    simpa only [x, y, ownedOfComplete, componentOwned_vertex] using he
  have hy : p.InComponent y :=
    (componentOwned_component p e.center).tail (logicalMove_adjacent e.port he)
  exact e.outside ((mem_markedComponent p e.target).mpr ⟨y, rfl, hy⟩)

theorem depth_zero_of_reachable {R : V → V → Prop} {root x : V}
    (hx : ParentDepth.Reachable R root x) (hd : ParentDepth.depth R root x = 0) : x = root := by
  classical
  have hp : ParentDepth.Path R root (ParentDepth.depth R root x) x := by
    rw [ParentDepth.depth, dif_pos hx]
    exact Nat.find_spec hx
  rw [hd] at hp
  cases hp
  rfl

namespace OwnedBase

variable {p : OwnedBase G μ} (h : RootedLegal G μ) (hm : Marked G μ p.vertex)
include h hm

theorem coordinates_logicalMove {x y : OwnedBase G μ}
    (hx : p.CoordinateDomain x) (hy : p.CoordinateDomain y)
    (d : Fin 4) (he : LogicalMove G μ d x.vertex y.vertex) :
    Walks.predecessor (p.coordinates x) d = some (p.coordinates y) := by
  fin_cases d
  · have hc := coordinates_E h hm hx he
    simp only [Walks.predecessor, Option.some.injEq]
    exact Prod.ext hc.1.symm hc.2.symm
  · have hc := coordinates_E h hm hy he
    have hi : (p.coordinates x).1 ≠ 0 := by omega
    simp only [Walks.predecessor, hi, ite_false, Option.some.injEq]
    apply Prod.ext <;> dsimp only <;> omega
  · have hc := coordinates_D h hm hy he
    have hi : (p.coordinates x).1 ≠ 0 := by omega
    simp only [Walks.predecessor, hi, ite_false, Option.some.injEq]
    apply Prod.ext <;> dsimp only <;> omega
  · have hc := coordinates_D h hm hx he
    have hj : (p.coordinates x).2 ≠ 0 := by omega
    simp only [Walks.predecessor, hj, ite_false, Option.some.injEq]
    apply Prod.ext <;> dsimp only <;> omega

theorem horizontal_pos_of_incoming {x : OwnedBase G μ} {y : V}
    (hx : p.CoordinateDomain x)
    (he : CompleteE G μ y x.vertex ∨ CompleteD G μ y x.vertex) :
    0 < (p.coordinates x).1 := by
  by_contra hn
  have hz : ParentDepth.depth (ParentH G μ) p.horizontal x.horizontal = 0 :=
    Nat.eq_zero_of_not_pos hn
  have howner := depth_zero_of_reachable hx.1 hz
  have ho : OwnerEdge G μ 0 x.vertex p.horizontal := howner ▸ x.horizontal_edge
  exact h.boundaryH p.vertex x.vertex y p.horizontal hm p.horizontal_edge ho he

theorem vertical_pos_of_outgoing_D {x : OwnedBase G μ} {y : V}
    (hx : p.CoordinateDomain x) (he : CompleteD G μ x.vertex y) :
    0 < (p.coordinates x).2 := by
  by_contra hn
  have hz : ParentDepth.depth (ParentV G μ) p.vertical x.vertical = 0 :=
    Nat.eq_zero_of_not_pos hn
  have howner := depth_zero_of_reachable hx.2 hz
  have ho : OwnerEdge G μ 1 x.vertex p.vertical := howner ▸ x.vertical_edge
  exact h.boundaryV p.vertex x.vertex y p.vertical hm p.vertical_edge ho he

theorem predecessor_exists_of_logicalMove {x : OwnedBase G μ} {y : V}
    (hx : p.CoordinateDomain x) (d : Fin 4) (he : LogicalMove G μ d x.vertex y) :
    ∃ q, Walks.predecessor (p.coordinates x) d = some q := by
  fin_cases d
  · exact ⟨((p.coordinates x).1 + 1, (p.coordinates x).2), rfl⟩
  · have hi := horizontal_pos_of_incoming h hm hx (Or.inl he)
    exact ⟨((p.coordinates x).1 - 1, (p.coordinates x).2), by
      simp [Walks.predecessor, Nat.ne_of_gt hi]⟩
  · have hi := horizontal_pos_of_incoming h hm hx (Or.inr he)
    exact ⟨((p.coordinates x).1 - 1, (p.coordinates x).2 + 1), by
      simp [Walks.predecessor, Nat.ne_of_gt hi]⟩
  · have hj := vertical_pos_of_outgoing_D h hm hx he
    exact ⟨((p.coordinates x).1 + 1, (p.coordinates x).2 - 1), by
      simp [Walks.predecessor, Nat.ne_of_gt hj]⟩

end OwnedBase

noncomputable def componentCoordinate (p : OwnedBase G μ)
    (c : PrivateLeaves.Center (markedComponent p)) : Walks.Point :=
  p.coordinates (componentOwned p c)

theorem componentCoordinate_root (h : RootedLegal G μ) {p : OwnedBase G μ}
    (hm : Marked G μ p.vertex) : componentCoordinate p (markedCenter p) = (0, 0) := by
  unfold componentCoordinate
  rw [componentOwned_markedCenter h]
  exact OwnedBase.coordinates_self h hm

theorem componentCoordinate_step (h : RootedLegal G μ) {p : OwnedBase G μ}
    (hm : Marked G μ p.vertex) (c c' : PrivateLeaves.Center (markedComponent p)) (d : Fin 4)
    (he : (baseNetwork h).neighbor c.val d = some c'.val) :
    Walks.predecessor (componentCoordinate p c) d = some (componentCoordinate p c') := by
  have hx := OwnedBase.coordinateDomain_of_component h hm (componentOwned_component p c)
  have hy := OwnedBase.coordinateDomain_of_component h hm (componentOwned_component p c')
  apply OwnedBase.coordinates_logicalMove h hm hx hy d
  rw [componentOwned_vertex, componentOwned_vertex]
  exact (baseNetwork_neighbor_iff h c.val c'.val d).mp he

theorem componentCoordinate_exit (h : RootedLegal G μ) {p : OwnedBase G μ}
    (hm : Marked G μ p.vertex)
    (e : PrivateLeaves.Exit (baseNetwork h) (markedComponent p)) :
    ∃ q, Walks.predecessor (componentCoordinate p e.center) e.port = some q := by
  apply OwnedBase.predecessor_exists_of_logicalMove h hm
    (OwnedBase.coordinateDomain_of_component h hm (componentOwned_component p e.center)) e.port
  rw [componentOwned_vertex]
  exact (baseNetwork_neighbor_iff h e.center.val e.target e.port).mp e.edge

noncomputable def privateNetwork (h : RootedLegal G μ) (p : OwnedBase G μ) :=
  PrivateLeaves.network (baseNetwork h) (markedComponent p)

noncomputable def privateProjection (h : RootedLegal G μ) {p : OwnedBase G μ}
    (hm : Marked G μ p.vertex) : Projection (privateNetwork h p) (Sum.inl (markedCenter p)) :=
  PrivateLeaves.projection (baseNetwork h) (markedComponent p) (markedCenter p)
    (componentCoordinate p) (componentCoordinate_root h hm)
    (componentCoordinate_step h hm) (componentCoordinate_exit h hm)

noncomputable def privateWeight (h : RootedLegal G μ) (p : OwnedBase G μ) (w : V → ℝ) :=
  PrivateLeaves.cloneWeight (baseNetwork h) (markedComponent p) (fun x => w x.val)

theorem privateWeight_mark (h : RootedLegal G μ) (p : OwnedBase G μ) (w : V → ℝ) :
    privateWeight h p w (Sum.inl (markedCenter p)) = w p.vertex := rfl

theorem privateNetwork_energy_le (h : RootedLegal G μ) (p : OwnedBase G μ) (w : V → ℝ) :
    (privateNetwork h p).energy (privateWeight h p w) ≤
      (baseNetwork h).energy (fun x => w x.val) +
        12 * incompleteSquares (G := G) (μ := μ) w := by
  classical
  let B : Finset (BaseVertex G μ) := Finset.univ.filter
    (fun x => ¬ IsComplete (G := G) (μ := μ) x.val)
  have hB (e : PrivateLeaves.Exit (baseNetwork h) (markedComponent p)) : e.target ∈ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact component_exit_incomplete h p e
  have he := PrivateLeaves.energy_clone_le (baseNetwork h) (markedComponent p) B hB
    (fun x => w x.val)
  simpa only [privateNetwork, privateWeight, B, Finset.sum_filter, incompleteSquares] using he

end TranscendentalTuran.Source
