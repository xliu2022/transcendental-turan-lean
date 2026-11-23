module

public import TranscendentalTuran.Construction.SourceValue
public import TranscendentalTuran.Construction.ExecutableWitness
public import TranscendentalTuran.Network.BlockSourceGain
public import TranscendentalTuran.Optimization.PaperValue

@[expose] public section

/-!
# An effectively constructed finite three-graph with transcendental Turán density

Formalization author and responsible maintainer: Xizhi Liu.

The witness `Construction.singleGraph` is an executable finite graph
definition. Its density is the ordinary binomial-normalized extremal limit.
-/

namespace TranscendentalTuran

open TuranUniversality
open scoped Topology

/-- The manuscript's arithmetic theorem for the actual ordinary source class. -/
theorem Source.classLambda_transcendental :
    Transcendental ℚ (classLambda Source.finiteClass) := by
  rw [Source.classLambda_eq_Ψ_value]
  exact Optimization.Paper.Ψ_green_transcendental

theorem singleGraph_density_value :
    turanDensity Construction.singleGraph.2 = 6 * Optimization.Paper.Ψ Green.value := by
  rw [Construction.singleGraph_turanDensity, Source.classLambda_eq_Ψ_value]

theorem singleGraph_density_transcendental :
    Transcendental ℚ (turanDensity Construction.singleGraph.2) := by
  rw [singleGraph_density_value]
  exact Optimization.Paper.six_Ψ_green_transcendental

/-- The value is the limit of ordinary forbidden-subgraph extremal densities. -/
theorem singleGraph_extremalDensity_tendsto :
    Filter.Tendsto (extremalDensity Construction.singleGraph.2) Filter.atTop
      (𝓝 (6 * Optimization.Paper.Ψ Green.value)) := by
  rw [← singleGraph_density_value]
  exact extremalDensity_tendsto Construction.singleGraph.2
    (Finset.card_pos.mpr Construction.singleGraph_has_edges)

/-- The executable constructor returns a graph with the stated transcendental
ordinary density when enabled. This theorem does not evaluate that graph. -/
theorem executable_main_result :
    ∃ P : FiniteGraph 3, Construction.buildSingleGraph true = some P ∧
      P.2.edges.Nonempty ∧ Transcendental ℚ (turanDensity P.2) :=
  ⟨Construction.singleGraph, Construction.buildSingleGraph_true,
    Construction.singleGraph_has_edges, singleGraph_density_transcendental⟩

/-- The manuscript's main theorem, with the explicit computable witness. -/
theorem main_result :
    ∃ n : ℕ, ∃ P : RGraph (Fin n) 3,
      P.edges.Nonempty ∧ Transcendental ℚ (turanDensity P) :=
  ⟨Construction.singleGraph.1, Construction.singleGraph.2,
    Construction.singleGraph_has_edges, singleGraph_density_transcendental⟩

end TranscendentalTuran
