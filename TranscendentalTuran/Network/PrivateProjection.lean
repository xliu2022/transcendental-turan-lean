module

public import TranscendentalTuran.Network.PrivateLeaves

@[expose] public section

/-!
# Coordinate projection of a private-leaf network

Formalization author and responsible maintainer: Xizhi Liu.

An exit leaf is placed at the endpoint of its occupied port. Coordinates may
coincide: the Green comparison needs preservation of directions, not an
injective coordinate map.
-/

namespace TranscendentalTuran.Network.PrivateLeaves

open Green Green.FiniteNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem predecessor_reverse {p q : Walks.Point} {d : Fin 4}
    (hd : Walks.predecessor p d = some q) :
    Walks.predecessor q (reverseDirection d) = some p := by
  rcases p with ⟨i, j⟩
  fin_cases d
  · simp only [Walks.predecessor, Option.some.injEq] at hd
    subst q
    simp [Walks.predecessor, reverseDirection]
  · by_cases hi : i = 0
    · simp [Walks.predecessor, hi] at hd
    · simp [Walks.predecessor, hi] at hd
      subst q
      simp [Walks.predecessor, reverseDirection, Prod.mk.injEq]
      omega
  · by_cases hi : i = 0
    · simp [Walks.predecessor, hi] at hd
    · simp [Walks.predecessor, hi] at hd
      subst q
      simp [Walks.predecessor, reverseDirection, Prod.mk.injEq]
      omega
  · by_cases hj : j = 0
    · simp [Walks.predecessor, hj] at hd
    · simp [Walks.predecessor, hj] at hd
      subst q
      simp [Walks.predecessor, reverseDirection, Prod.mk.injEq]
      omega

noncomputable def leafCoordinate (N : DirectionalNetwork V) (C : Finset V)
    (coord : Center C → Walks.Point)
    (hExit : ∀ e : Exit N C, ∃ p, Walks.predecessor (coord e.center) e.port = some p)
    (e : Exit N C) : Walks.Point := Classical.choose (hExit e)

theorem leafCoordinate_spec (N : DirectionalNetwork V) (C : Finset V)
    (coord : Center C → Walks.Point)
    (hExit : ∀ e : Exit N C, ∃ p, Walks.predecessor (coord e.center) e.port = some p)
    (e : Exit N C) :
    Walks.predecessor (coord e.center) e.port = some (leafCoordinate N C coord hExit e) :=
  Classical.choose_spec (hExit e)

noncomputable def projection (N : DirectionalNetwork V) (C : Finset V)
    (o : Center C) (coord : Center C → Walks.Point) (hroot : coord o = (0, 0))
    (hstep : ∀ c c' : Center C, ∀ d, N.neighbor c.val d = some c'.val →
      Walks.predecessor (coord c) d = some (coord c'))
    (hExit : ∀ e : Exit N C, ∃ p, Walks.predecessor (coord e.center) e.port = some p) :
    Projection (network N C) (Sum.inl o) where
  coord := Sum.elim coord (leafCoordinate N C coord hExit)
  root := hroot
  step := by
    intro v w d hd
    cases v with
    | inl c =>
      cases w with
      | inl c' =>
        exact hstep c c' d ((neighbor_center_center_iff N C c c' d).mp hd)
      | inr e =>
        obtain ⟨rfl, rfl⟩ := (neighbor_center_leaf_iff N C c e d).mp hd
        exact leafCoordinate_spec N C coord hExit e
    | inr e =>
      cases w with
      | inl c =>
        obtain ⟨rfl, hc⟩ := (neighbor_leaf_center_iff N C e c d).mp hd
        subst c
        exact predecessor_reverse (leafCoordinate_spec N C coord hExit e)
      | inr f => exact False.elim (neighbor_leaf_leaf N C e f d hd)

end TranscendentalTuran.Network.PrivateLeaves
