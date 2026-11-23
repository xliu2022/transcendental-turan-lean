module

public import TranscendentalTuran.Optimization.PaperObjective
public import TranscendentalTuran.Green.Constants

@[expose] public section

/-!
# Transcendence of the paper's concrete candidate value

Formalization author and responsible maintainer: Xizhi Liu.

This result concerns the explicitly defined optimization value. The final
single-forbidden-graph theorem must additionally identify its ordinary
Turán density with six times this value.
-/

namespace TranscendentalTuran.Optimization.Paper

theorem Ψ_green_transcendental : Transcendental ℚ (Ψ Green.value) :=
  Ψ_transcendental Green.value_transcendental

theorem six_Ψ_green_transcendental : Transcendental ℚ (6 * Ψ Green.value) := by
  intro h
  apply Ψ_green_transcendental
  have ha := h.mul (isAlgebraic_natCast 6 : IsAlgebraic ℚ (6 : ℝ)).inv
  convert ha using 1 <;> ring

end TranscendentalTuran.Optimization.Paper

#print axioms LeanFormalizations.Transcendence.transcendental_pi_axiomClean
#print axioms TranscendentalTuran.Green.value_transcendental
#print axioms TranscendentalTuran.Optimization.Paper.Ψ_green_transcendental
#print axioms TranscendentalTuran.Optimization.Paper.six_Ψ_green_transcendental
