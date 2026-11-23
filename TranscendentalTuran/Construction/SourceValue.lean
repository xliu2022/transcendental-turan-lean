module

public import TranscendentalTuran.Construction.SourceUpper
public import TranscendentalTuran.Green.Realization.ClassLower
public import TranscendentalTuran.Green.CornerTranscendence

@[expose] public section

/-!
# The exact value of the ordinary source class

Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Source

theorem classLambda_eq_Ψ_cornerGreen :
    classLambda finiteClass = Optimization.Paper.Ψ Green.cornerGreen :=
  le_antisymm classLambda_le_Ψ Green.Realization.Ψ_cornerGreen_le_classLambda

theorem classLambda_eq_Ψ_value :
    classLambda finiteClass = Optimization.Paper.Ψ Green.value := by
  rw [classLambda_eq_Ψ_cornerGreen, Green.cornerGreen_eq_value]

end TranscendentalTuran.Source
