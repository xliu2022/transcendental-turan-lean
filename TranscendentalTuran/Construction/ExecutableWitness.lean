module

public import TranscendentalTuran.Construction.SingleGraph

@[expose] public section

/-!
# A compiled executable constructor for the finite forbidden graph

Formalization author and responsible maintainer: Xizhi Liu.

The Boolean gate keeps module initialization finite and small. The enabled
branch is the explicit finite construction; its enormous size makes evaluating
that branch unnecessary for checking its definition and the density theorem.
-/

namespace TranscendentalTuran.Construction

open TuranUniversality

attribute [local irreducible] Parameters.q Parameters.N
set_option compiler.extract_closed false
set_option maxRecDepth 4000

/-- A regular compiled function, without `macro_inline`, whose enabled branch
constructs the actual single forbidden three-graph. -/
def buildSingleGraph (enabled : Bool) : Option (FiniteGraph 3) :=
  if enabled then some singleGraph else none

@[simp] theorem buildSingleGraph_true :
    buildSingleGraph true = some singleGraph := rfl

@[simp] theorem buildSingleGraph_false :
    buildSingleGraph false = none := rfl

/-- Any output of the enabled constructor has the proved ordinary density. -/
theorem buildSingleGraph_density {G : FiniteGraph 3}
    (hG : buildSingleGraph true = some G) :
    turanDensity G.2 = 6 * classLambda Source.finiteClass := by
  have h : singleGraph = G := Option.some.inj hG
  subst G
  exact singleGraph_turanDensity

-- This only evaluates the disabled branch, and tests safe module initialization.
#eval (buildSingleGraph false).isNone

end TranscendentalTuran.Construction
