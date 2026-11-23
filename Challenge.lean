module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

/-!
# Target statement: a single finite three-graph with transcendental density

Formalization author and responsible maintainer: Xizhi Liu.

This independent statement imports only Mathlib. The graph, ordinary
embedding, extremal number and Turan density definitions are restated here
so that Comparator can check the advertised conclusion without importing
the proof development. No weighted or homomorphism density substitutes for
ordinary Turan density. The single intentional hole below is a Challenge
target, not an available theorem in the proof development.

The effective construction is to be supplied by an explicit executable
finite graph code in the solution development. Its implementation and
correctness are part of the completion requirements, beyond merely stating
the existential conclusion here.
-/

namespace TuranUniversality

universe u v

/-- A finite simple uniform edge set, on the indicated vertex type. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- Ordinary containment: global vertex injectivity and edge preservation. -/
def RGraph.IsEmbedding {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] {r : ℕ}
    (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

noncomputable section

/-- Maximum edge count among actual forbidden-graph-free hosts. -/
def extremalNumber {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ H : RGraph (Fin n) r,
    (¬ ∃ f, F.IsEmbedding H f) ∧ H.edges.card = m) (n.choose r)

def extremalDensity {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℝ :=
  (extremalNumber F n : ℝ) / (n.choose r : ℝ)

/-- The infimum of the ordinary normalized extremal numbers for `n ≥ r`.
The proof development establishes that this is their limit. -/
def turanDensity {r k : ℕ} (F : RGraph (Fin k) r) : ℝ :=
  ⨅ n : ℕ, extremalDensity F (n + r)

end
end TuranUniversality

namespace TranscendentalTuran

/-- The main existential conclusion, with a nonempty finite forbidden graph. -/
theorem main_result :
    ∃ n : ℕ, ∃ P : TuranUniversality.RGraph (Fin n) 3,
      P.edges.Nonempty ∧ Transcendental ℚ (TuranUniversality.turanDensity P) := by
  sorry

end TranscendentalTuran
