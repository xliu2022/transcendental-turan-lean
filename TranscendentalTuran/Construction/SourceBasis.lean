module

public import TranscendentalTuran.Encoding.Certificates.Enumeration
public import TranscendentalTuran.Transfer.FactorRecovery
public import TuranUniversality.Hypergraph.Clique

@[expose] public section

namespace TranscendentalTuran.Source

open TuranUniversality Encoding Certificates Parameters

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

def finiteClass : FiniteGraph 3 → Prop := fun G => Admissible G.2

instance : DecidablePred finiteClass := fun G =>
  inferInstanceAs (Decidable (Admissible G.2))

@[macro_inline] def obstructionOrder : ℕ := patternBound q 13

theorem finiteClass_monotone : FiniteGraph.ClassMonotone finiteClass := by
  intro A G hAG hG
  obtain ⟨f, hf⟩ := hAG
  exact admissible_of_embedding hf hG

theorem finiteClass_bounded (G : FiniteGraph 3) (hG : ¬ finiteClass G) :
    ∃ A : FiniteGraph 3, A.1 ≤ obstructionOrder ∧ ¬ finiteClass A ∧ A.Contains G := by
  have hp : ¬ patternFiniteClass forbiddenPatterns G := fun h =>
    hG ((admissible_iff_patternClass G.2).mpr h)
  obtain ⟨A, hsize, hbad, hAG⟩ := patternFiniteClass_bounded forbiddenPatterns 13
    (fun _ hp => forbiddenPatterns_data hp) G hp
  refine ⟨A, ?_, ?_, hAG⟩
  · simpa only [obstructionOrder, Fintype.card_fin] using hsize
  · exact fun h => hbad ((admissible_iff_patternClass A.2).mp h)

/-- The finite forbidden basis is an explicit enumeration, with no choice
of a basis hidden in the definition. -/
@[macro_inline] def forbiddenBasis : Finset (FiniteGraph 3) := patternBasis forbiddenPatterns 13

theorem forbiddenBasis_spec (G : FiniteGraph 3) : finiteClass G ↔
    ∀ A ∈ forbiddenBasis, ¬ A.Contains G := by
  exact (admissible_iff_patternClass G.2).trans
    (patternBasis_spec forbiddenPatterns 13 (fun _ hp => forbiddenPatterns_data hp) G)

theorem forbiddenBasis_has_edges {A : FiniteGraph 3} (hA : A ∈ forbiddenBasis) :
    A.2.edges.Nonempty :=
  patternBasis_has_edges forbiddenPatterns 13 (fun _ hp => forbiddenPatterns_have_edges hp) hA

theorem large_clique_not_admissible (n : ℕ) (hn : q + 3 ≤ n) :
    ¬ Admissible (RGraph.clique (Fin n) 3) := by
  classical
  rintro ⟨μ, hμ⟩
  let D := Finset.univ \ μ.range
  have hroot : μ.range.card ≤ q := by
    simpa only [Fintype.card_fin] using Transfer.rooting_range_card_le μ
  have hsplit : D.card + μ.range.card = n := by
    simpa only [D, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ μ.range)
  have hD : 2 < D.card := by omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hD
  have he : {x, y, z} ∈ (RGraph.clique (Fin n) 3).edges := by
    exact (RGraph.mem_clique _).mpr (by simp [hxy, hxz, hyz])
  obtain ⟨v, hv, hrootv⟩ := hμ.covers_edges _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact (Finset.mem_sdiff.mp hx).2 hrootv
  · exact (Finset.mem_sdiff.mp hy).2 hrootv
  · exact (Finset.mem_sdiff.mp hz).2 hrootv

theorem forbiddenBasis_nonempty : forbiddenBasis.Nonempty := by
  classical
  by_contra h
  have hempty : forbiddenBasis = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hadm := (forbiddenBasis_spec ⟨q + 3, RGraph.clique (Fin (q + 3)) 3⟩).mpr
    (by simp [hempty])
  exact large_clique_not_admissible (q + 3) le_rfl hadm

end TranscendentalTuran.Source
