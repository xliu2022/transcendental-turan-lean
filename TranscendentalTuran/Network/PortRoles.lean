module

public import TranscendentalTuran.Network.MatchingEnergy
public import TranscendentalTuran.Network.PartialIsoRelation
public import TranscendentalTuran.Network.PartialIsoSeries

@[expose] public section

/-!
# The two orientations of actual path ports

Formalization author and responsible maintainer: Xizhi Liu.

Every port is assigned to one of the two four-edge path families. An unused
port may be assigned arbitrarily. The local matching and role uniqueness
rules guarantee that every occupied incidence receives the correct family.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network
open scoped BigOperators

attribute [local irreducible] Parameters.q Parameters.N
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

abbrev TypedVertex (G : RGraph V 3) (μ : Rooting Root V) (τ : PhysicalType) :=
  {x : V // Declared G μ τ x}

noncomputable instance (τ : PhysicalType) : Fintype (TypedVertex G μ τ) := Fintype.ofFinite _

def Port01E (G : RGraph V 3) (μ : Rooting Root V) (p : V) : Prop :=
  (∃ x, Declared G μ .base x ∧ MatchingEdge G μ 0 x p) ∨
    (∃ c, Declared G μ .center13 c ∧ MatchingEdge G μ 1 c p)

def Port23E (G : RGraph V 3) (μ : Rooting Root V) (p : V) : Prop :=
  (∃ x, Declared G μ .base x ∧ MatchingEdge G μ 2 x p) ∨
    (∃ c, Declared G μ .center13 c ∧ MatchingEdge G μ 3 c p)

theorem port01E_of_base {x p : V} (hx : Declared G μ .base x)
    (he : MatchingEdge G μ 0 x p) : Port01E G μ p := Or.inl ⟨x, hx, he⟩

theorem port01E_of_center {x p : V} (hx : Declared G μ .center13 x)
    (he : MatchingEdge G μ 1 x p) : Port01E G μ p := Or.inr ⟨x, hx, he⟩

theorem port23E_of_base {x p : V} (hx : Declared G μ .base x)
    (he : MatchingEdge G μ 2 x p) : Port23E G μ p := Or.inl ⟨x, hx, he⟩

theorem port23E_of_center {x p : V} (hx : Declared G μ .center13 x)
    (he : MatchingEdge G μ 3 x p) : Port23E G μ p := Or.inr ⟨x, hx, he⟩

theorem not_port01E_of_base (h : RootedLegal G μ) {x p : V}
    (hx : Declared G μ .base x) (he : MatchingEdge G μ 1 x p) : ¬ Port01E G μ p := by
  rintro (⟨y, hy, ey⟩ | ⟨c, hc, ec⟩)
  · have hh := (h.port_base_unique 0 1 y x p hy hx ey he).1
    cases hh
  · have hh := h.matching_right 1 c x p ec he
    subst c
    have ht := h.declarations_unique x .center13 .base hc hx
    cases ht

theorem not_port01E_of_center (h : RootedLegal G μ) {x p : V}
    (hx : Declared G μ .center02 x) (he : MatchingEdge G μ 0 x p) : ¬ Port01E G μ p := by
  rintro (⟨y, hy, ey⟩ | ⟨c, hc, ec⟩)
  · have hh := h.matching_right 0 y x p ey he
    subst y
    have ht := h.declarations_unique x .base .center02 hy hx
    cases ht
  · have hh := (h.port_center_unique 1 0 c x p (Or.inl hc) (Or.inr hx) ec he).1
    cases hh

theorem not_port23E_of_base (h : RootedLegal G μ) {x p : V}
    (hx : Declared G μ .base x) (he : MatchingEdge G μ 3 x p) : ¬ Port23E G μ p := by
  rintro (⟨y, hy, ey⟩ | ⟨c, hc, ec⟩)
  · have hh := (h.port_base_unique 2 3 y x p hy hx ey he).1
    cases hh
  · have hh := h.matching_right 3 c x p ec he
    subst c
    have ht := h.declarations_unique x .center13 .base hc hx
    cases ht

theorem not_port23E_of_center (h : RootedLegal G μ) {x p : V}
    (hx : Declared G μ .center02 x) (he : MatchingEdge G μ 2 x p) : ¬ Port23E G μ p := by
  rintro (⟨y, hy, ey⟩ | ⟨c, hc, ec⟩)
  · have hh := h.matching_right 2 y x p ey he
    subst y
    have ht := h.declarations_unique x .base .center02 hy hx
    cases ht
  · have hh := (h.port_center_unique 3 2 c x p (Or.inl hc) (Or.inr hx) ec he).1
    cases hh

abbrev EPort01 (G : RGraph V 3) (μ : Rooting Root V) :=
  {p : TypedVertex G μ .port01 // Port01E G μ p.val}
abbrev DPort01 (G : RGraph V 3) (μ : Rooting Root V) :=
  {p : TypedVertex G μ .port01 // ¬ Port01E G μ p.val}
abbrev EPort23 (G : RGraph V 3) (μ : Rooting Root V) :=
  {p : TypedVertex G μ .port23 // Port23E G μ p.val}
abbrev DPort23 (G : RGraph V 3) (μ : Rooting Root V) :=
  {p : TypedVertex G μ .port23 // ¬ Port23E G μ p.val}

end TranscendentalTuran.Source
