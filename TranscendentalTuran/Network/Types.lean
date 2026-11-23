module

public import TranscendentalTuran.Construction.Parameters
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Seven physical types and six layer blocks

Formalization author and responsible maintainer: Xizhi Liu.
The four matching blocks are listed in the order used in the manuscript.
-/

namespace TranscendentalTuran.Network

inductive PhysicalType
  | base | port01 | port23 | center13 | center02 | ownerH | ownerV
  deriving DecidableEq

inductive Block
  | match0 | match1 | match2 | match3 | ownerH | ownerV
  deriving DecidableEq

instance : Fintype PhysicalType :=
  ⟨{.base, .port01, .port23, .center13, .center02, .ownerH, .ownerV}, by
    intro t; cases t <;> simp⟩

instance : Fintype Block :=
  ⟨{.match0, .match1, .match2, .match3, .ownerH, .ownerV}, by
    intro b; cases b <;> simp⟩

open PhysicalType

def sign : Block → PhysicalType → ℤ
  | .match0, .base | .match0, .center02 => 1
  | .match0, .port01 => -1
  | .match1, .base | .match1, .center13 => 1
  | .match1, .port01 => -1
  | .match2, .base | .match2, .center02 => 1
  | .match2, .port23 => -1
  | .match3, .base | .match3, .center13 => 1
  | .match3, .port23 => -1
  | .ownerH, .ownerH | .ownerV, .ownerV => 1
  | .ownerH, .base | .ownerV, .base => -1
  | _, _ => 0

def Active (b : Block) (t : PhysicalType) : Prop := sign b t ≠ 0

instance (b : Block) (t : PhysicalType) : Decidable (Active b t) :=
  inferInstanceAs (Decidable (sign b t ≠ 0))

/-- Oriented from a positive type to a negative type. -/
def AllowedIncidence : Block → PhysicalType → PhysicalType → Prop
  | .match0, .base, .port01 | .match0, .center02, .port01 => True
  | .match1, .base, .port01 | .match1, .center13, .port01 => True
  | .match2, .base, .port23 | .match2, .center02, .port23 => True
  | .match3, .base, .port23 | .match3, .center13, .port23 => True
  | .ownerH, .ownerH, .base | .ownerV, .ownerV, .base => True
  | _, _, _ => False

instance (b : Block) (a c : PhysicalType) : Decidable (AllowedIncidence b a c) := by
  cases b <;> cases a <;> cases c <;> simp only [AllowedIncidence] <;> infer_instance

theorem incidence_signs {b : Block} {a c : PhysicalType} (h : AllowedIncidence b a c) :
    sign b a = 1 ∧ sign b c = -1 := by
  cases b <;> cases a <;> cases c <;> simp_all [AllowedIncidence, sign]

theorem incidence_distinct {b : Block} {a c : PhysicalType} (h : AllowedIncidence b a c) :
    a ≠ c := by
  obtain ⟨ha, hc⟩ := incidence_signs h
  intro he
  rw [he, hc] at ha
  norm_num at ha

theorem sign_trichotomy (b : Block) (t : PhysicalType) :
    sign b t = -1 ∨ sign b t = 0 ∨ sign b t = 1 := by
  cases b <;> cases t <;> simp [sign]

def repetitions : Block → ℕ
  | .match0 | .match1 | .match2 | .match3 => Parameters.M
  | .ownerH | .ownerV => Parameters.κ

abbrev Layer := (b : Block) × Fin (repetitions b)

theorem repetitions_pos (b : Block) : 0 < repetitions b := by
  cases b <;> first | exact Parameters.M_pos | exact Parameters.κ_pos

theorem type_card : Fintype.card PhysicalType = 7 := by decide
theorem block_card : Fintype.card Block = 6 := by decide
theorem layer_card : Fintype.card Layer = Parameters.K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change Parameters.M + (Parameters.M + (Parameters.M + (Parameters.M +
    (Parameters.κ + (Parameters.κ + 0))))) = Parameters.K
  unfold Parameters.K
  omega

end TranscendentalTuran.Network
