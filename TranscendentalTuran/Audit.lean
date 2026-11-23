module

public import TranscendentalTuran.Main

@[expose] public section

/-!
# Release dependency audit

Formalization author and responsible maintainer: Xizhi Liu.

These commands ask Lean for the complete transitive axiom dependencies of
the final result and its principal mathematical interfaces. The independent
Challenge is deliberately absent from this import closure.
-/

#print axioms TranscendentalTuran.main_result
#print axioms TranscendentalTuran.executable_main_result
#print axioms TranscendentalTuran.Construction.buildSingleGraph
#print axioms TranscendentalTuran.singleGraph_density_value
#print axioms TranscendentalTuran.singleGraph_density_transcendental
#print axioms TranscendentalTuran.singleGraph_extremalDensity_tendsto
#print axioms TranscendentalTuran.Source.classLambda_eq_Ψ_cornerGreen
#print axioms TranscendentalTuran.Source.classLambda_transcendental
#print axioms TranscendentalTuran.Source.classLambda_le_Ψ
#print axioms TranscendentalTuran.Source.source_gain_block_means
#print axioms TranscendentalTuran.Green.Realization.Ψ_cornerGreen_le_classLambda
#print axioms TranscendentalTuran.Construction.singleGraph_turanDensity
#print axioms TranscendentalTuran.Optimization.Paper.six_Ψ_green_transcendental

