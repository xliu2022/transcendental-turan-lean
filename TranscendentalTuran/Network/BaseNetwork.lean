module

public import TranscendentalTuran.Network.Moves
public import TranscendentalTuran.Network.OwnerPenalty
public import TranscendentalTuran.Green.FiniteNetwork.Basic

@[expose] public section

/-!
# The actual four-port network on declared base vertices

Formalization author and responsible maintainer: Xizhi Liu.

A port is occupied exactly when the four actual matching relations complete
the corresponding east, west, northwest, or southeast chain. The ordinary
local rules prove that every port has at most one endpoint.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Network Green.FiniteNetwork

attribute [local irreducible] Parameters.q Parameters.N

variable {V : Type*} [Fintype V] [DecidableEq V] {G : RGraph V 3} {μ : Rooting Root V}

noncomputable def baseNeighbor (G : RGraph V 3) (μ : Rooting Root V)
    (x : BaseVertex G μ) (d : Fin 4) : Option (BaseVertex G μ) := by
  classical
  exact if he : ∃ y : BaseVertex G μ, LogicalMove G μ d x.val y.val then
    some (Classical.choose he) else none

theorem baseNeighbor_iff (h : RootedLegal G μ) (x y : BaseVertex G μ) (d : Fin 4) :
    baseNeighbor G μ x d = some y ↔ LogicalMove G μ d x.val y.val := by
  classical
  unfold baseNeighbor
  split
  · rename_i he
    simp only [Option.some.injEq]
    constructor
    · intro heq
      exact heq ▸ Classical.choose_spec he
    · intro hy
      exact Subtype.ext (logicalMove_deterministic h d (Classical.choose_spec he) hy)
  · rename_i he
    simp only [reduceCtorEq, false_iff]
    intro hy
    exact he ⟨y, hy⟩

theorem reverseDirection_eq_reversePort (d : Fin 4) : reverseDirection d = reversePort d := by
  fin_cases d <;> rfl

noncomputable def baseNetwork (h : RootedLegal G μ) : DirectionalNetwork (BaseVertex G μ) where
  neighbor := baseNeighbor G μ
  reverse_step x y d := by
    rw [baseNeighbor_iff h, baseNeighbor_iff h, reverseDirection_eq_reversePort]
    exact (logicalMove_reverse d x.val y.val).symm

theorem baseNetwork_neighbor_iff (h : RootedLegal G μ) (x y : BaseVertex G μ) (d : Fin 4) :
    (baseNetwork h).neighbor x d = some y ↔ LogicalMove G μ d x.val y.val :=
  baseNeighbor_iff h x y d

end TranscendentalTuran.Source
