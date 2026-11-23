module

public import TranscendentalTuran.Encoding.LocalRules

@[expose] public section

/-! # Every graph on the root set belongs to the source class
Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source

open TuranUniversality Encoding

attribute [local irreducible] Parameters.q Parameters.N
set_option maxRecDepth 4000

def totalRooting : Rooting Root Root :=
  ⟨some, fun a b v ha hb => Option.some.inj (ha.trans hb.symm)⟩

theorem totalRooting_range (v : Root) : v ∈ totalRooting.range :=
  (Rooting.mem_range _ _).mpr ⟨v, rfl⟩

theorem no_data_totalRooting (v : Root) : ¬ Data totalRooting v :=
  fun h => h (totalRooting_range v)

theorem rootGraph_legal (G : RGraph Root 3) : RootedLegal G totalRooting := by
  constructor
  · intro e he
    have hn : e.Nonempty := Finset.card_pos.mp (by rw [G.uniform e he]; decide)
    obtain ⟨v, hv⟩ := hn
    exact ⟨v, hv, totalRooting_range v⟩
  all_goals
    intros
    simp_all [Link, PairLink, Marked, Declared, MatchingEdge, OwnerEdge,
      IsCenter, CompleteE, CompleteD, StructuralAt, ParentH, ParentV,
      no_data_totalRooting]

theorem rootGraph_admissible (G : RGraph Root 3) : Admissible G :=
  ⟨totalRooting, rootGraph_legal G⟩

end TranscendentalTuran.Source
