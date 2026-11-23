/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.BoxMoves
public import TranscendentalTuran.Green.Realization.TemplateLegal

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Encoding TuranUniversality Source

/-- The actual finite ordinary three-graph realizing the subdivided box. -/
def boxGraph (n : ℕ) : RGraph (Root ⊕ Vertex n) 3 := (boxData n).graph

theorem boxGraph_rootedLegal (n : ℕ) : RootedLegal (boxGraph n) (sumRooting (Vertex n)) :=
  (boxData n).graph_rootedLegal (boxData_legal n)

theorem boxGraph_admissible (n : ℕ) : Admissible (boxGraph n) :=
  ⟨sumRooting (Vertex n), boxGraph_rootedLegal n⟩

end TranscendentalTuran.Green.Realization
