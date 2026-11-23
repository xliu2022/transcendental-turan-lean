module

public import TranscendentalTuran.Encoding.Layout
public import TranscendentalTuran.Encoding.PositivePatterns

@[expose] public section

/-!
# The manuscript's local rooted rules

Formalization author and responsible maintainer: Xizhi Liu.

All structural relations below are read from present ordinary triples.
Owners and complete moves are inferred relations. In particular no absent
edge is used to declare a type, a mark, or an inferred parent arrow.
Same-sign links are excluded between two leaves sharing a center in an
individual layer; the matching/ownership axioms make this the star-component
condition from the manuscript.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Parameters Encoding Network

variable {V : Type*} [DecidableEq V]

def Data (μ : Rooting Root V) (x : V) : Prop := x ∉ μ.range

def Link (G : RGraph V 3) (μ : Rooting Root V) (r : Root) (x y : V) : Prop :=
  Data μ x ∧ Data μ y ∧ ∃ v, μ.val r = some v ∧ {v, x, y} ∈ G.edges

def PairLink (G : RGraph V 3) (μ : Rooting Root V) (r s : Root) (x : V) : Prop :=
  Data μ x ∧ ∃ u v, μ.val r = some u ∧ μ.val s = some v ∧ {u, v, x} ∈ G.edges

def Marked (G : RGraph V 3) (μ : Rooting Root V) (x : V) : Prop :=
  PairLink G μ markerLeft markerRight x

def Declared (G : RGraph V 3) (μ : Rooting Root V) (τ : PhysicalType) (x : V) : Prop :=
  Data μ x ∧
    ((∃ j : Fin N, PairLink G μ
      (declaringRoot ((physicalIndex τ, j), 0))
      (declaringRoot ((physicalIndex τ, j), 1)) x) ∨
    (τ = .base ∧ Marked G μ x))

theorem marked_declared {G : RGraph V 3} {μ : Rooting Root V} {x : V}
    (hx : Marked G μ x) : Declared G μ .base x :=
  ⟨hx.1, Or.inr ⟨rfl, hx⟩⟩

theorem link_symm {G : RGraph V 3} {μ : Rooting Root V} {r : Root} {x y : V}
    (h : Link G μ r x y) : Link G μ r y x := by
  obtain ⟨hx, hy, v, hv, he⟩ := h
  refine ⟨hy, hx, v, hv, ?_⟩
  have hs : ({v, y, x} : Finset V) = {v, x, y} := by
    rw [Finset.pair_comm y x]
  simpa only [hs] using he

/-- Oriented structural edges in a matching-block union. -/
def MatchingEdge (G : RGraph V 3) (μ : Rooting Root V)
    (b : Fin 4) (x y : V) : Prop :=
  ∃ τ σ, Declared G μ τ x ∧ Declared G μ σ y ∧
    AllowedIncidence (matchingBlock b) τ σ ∧
    ∃ j : Fin M, Link G μ (matchingRoot b j) x y

/-- A base-to-owner incidence in the appropriate repetition-block union. -/
def OwnerEdge (G : RGraph V 3) (μ : Rooting Root V)
    (b : Fin 2) (x o : V) : Prop :=
  Declared G μ .base x ∧ Declared G μ (ownerType b) o ∧
    ∃ j : Fin κ, Link G μ (ownershipRoot b j) x o

def IsCenter (G : RGraph V 3) (μ : Rooting Root V) (x : V) : Prop :=
  Declared G μ .center13 x ∨ Declared G μ .center02 x

def CompleteE (G : RGraph V 3) (μ : Rooting Root V) (x y : V) : Prop :=
  Declared G μ .base x ∧ Declared G μ .base y ∧
  ∃ p c p', Declared G μ .port01 p ∧ Declared G μ .center13 c ∧
    Declared G μ .port23 p' ∧
    MatchingEdge G μ 0 x p ∧ MatchingEdge G μ 1 c p ∧
    MatchingEdge G μ 3 c p' ∧ MatchingEdge G μ 2 y p'

def CompleteD (G : RGraph V 3) (μ : Rooting Root V) (x y : V) : Prop :=
  Declared G μ .base x ∧ Declared G μ .base y ∧
  ∃ p c p', Declared G μ .port01 p ∧ Declared G μ .center02 c ∧
    Declared G μ .port23 p' ∧
    MatchingEdge G μ 1 x p ∧ MatchingEdge G μ 0 c p ∧
    MatchingEdge G μ 2 c p' ∧ MatchingEdge G μ 3 y p'

def ParentH (G : RGraph V 3) (μ : Rooting Root V) (a b : V) : Prop :=
  ∃ x y, (CompleteE G μ x y ∨ CompleteD G μ x y) ∧
    OwnerEdge G μ 0 x a ∧ OwnerEdge G μ 0 y b

def ParentV (G : RGraph V 3) (μ : Rooting Root V) (a b : V) : Prop :=
  ∃ x y, CompleteD G μ x y ∧ OwnerEdge G μ 1 y a ∧ OwnerEdge G μ 1 x b

/-- This graph uses one actual layer, not its repetition-block union. -/
def StructuralAt (G : RGraph V 3) (μ : Rooting Root V) (r : Layer) (x y : V) : Prop :=
  ∃ τ σ, Declared G μ τ x ∧ Declared G μ σ y ∧
    Active r.1 τ ∧ Active r.1 σ ∧ sign r.1 τ = -sign r.1 σ ∧
    Link G μ (layerRoot r) x y

/-- The concrete ordinary rooting rules. Each implication uses only positive
edge witnesses; the conclusions record forbidden equalities or inequalities. -/
structure RootedLegal (G : RGraph V 3) (μ : Rooting Root V) : Prop where
  covers_edges : ∀ e ∈ G.edges, ∃ v ∈ e, v ∈ μ.range
  passive_empty : ∀ r, IsPassive r → ∀ x y, ¬ Link G μ r x y
  declarations_unique : ∀ x τ σ, Declared G μ τ x → Declared G μ σ x → τ = σ
  generic_different : ∀ r, IsGeneric r → ∀ x y τ σ,
    Declared G μ τ x → Declared G μ σ y → Link G μ r x y → τ ≠ σ
  special_allowed : ∀ r x y τ σ,
    Declared G μ τ x → Declared G μ σ y → Link G μ (layerRoot r) x y →
    Active r.1 τ ∧ Active r.1 σ ∧
      (sign r.1 τ = sign r.1 σ ∨ AllowedIncidence r.1 τ σ ∨ AllowedIncidence r.1 σ τ)
  matching_left : ∀ b x y z,
    MatchingEdge G μ b x y → MatchingEdge G μ b x z → y = z
  matching_right : ∀ b x y z,
    MatchingEdge G μ b x z → MatchingEdge G μ b y z → x = y
  port_base_unique : ∀ b c x y p,
    Declared G μ .base x → Declared G μ .base y →
    MatchingEdge G μ b x p → MatchingEdge G μ c y p → b = c ∧ x = y
  port_center_unique : ∀ b c x y p,
    IsCenter G μ x → IsCenter G μ y →
    MatchingEdge G μ b x p → MatchingEdge G μ c y p → b = c ∧ x = y
  owner_functional : ∀ b x a a', OwnerEdge G μ b x a → OwnerEdge G μ b x a' → a = a'
  same_component_forbidden : ∀ r x y c,
    StructuralAt G μ r x c → StructuralAt G μ r y c → ¬ Link G μ (layerRoot r) x y
  marks_unique : ∀ x y, Marked G μ x → Marked G μ y → x = y
  E_preserves_vertical : ∀ x y a b,
    CompleteE G μ x y → OwnerEdge G μ 1 x a → OwnerEdge G μ 1 y b → a = b
  parentH_unique : ∀ a b c, ParentH G μ a c → ParentH G μ b c → a = b
  parentV_unique : ∀ a b c, ParentV G μ a c → ParentV G μ b c → a = b
  boundaryH : ∀ m x y o, Marked G μ m → OwnerEdge G μ 0 m o → OwnerEdge G μ 0 x o →
    ¬ (CompleteE G μ y x ∨ CompleteD G μ y x)
  boundaryV : ∀ m x y o, Marked G μ m → OwnerEdge G μ 1 m o → OwnerEdge G μ 1 x o →
    ¬ CompleteD G μ x y

def Admissible (G : RGraph V 3) : Prop := ∃ μ, RootedLegal G μ

theorem rootedLegal_empty_rooting (G : RGraph V 3) (hG : G.edges = ∅) :
    RootedLegal G Rooting.empty := by
  constructor <;> intros
  all_goals
    simp_all [Link, PairLink, Marked, Declared, MatchingEdge, OwnerEdge,
      IsCenter, CompleteE, CompleteD, StructuralAt, ParentH, ParentV, Rooting.empty]

theorem edgeless_admissible (G : RGraph V 3) (hG : G.edges = ∅) : Admissible G :=
  ⟨Rooting.empty, rootedLegal_empty_rooting G hG⟩

theorem root_cover {G : RGraph V 3} {μ : Rooting Root V} (h : RootedLegal G μ)
    {e : Finset V} (he : e ∈ G.edges) : ∃ v ∈ e, v ∈ μ.range := h.covers_edges e he

end TranscendentalTuran.Source
