module

public import TranscendentalTuran.Encoding.RootPairs
public import TranscendentalTuran.Network.Types

@[expose] public section

/-! # The concrete root layout
Formalization author and responsible maintainer: Xizhi Liu.
-/

namespace TranscendentalTuran.Encoding

open Parameters Network

def physicalIndex : PhysicalType → Fin 7
  | .base => 0
  | .port01 => 1
  | .port23 => 2
  | .center13 => 3
  | .center02 => 4
  | .ownerH => 5
  | .ownerV => 6

theorem physicalIndex_injective : Function.Injective physicalIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [physicalIndex]

def matchingRoot (b : Fin 4) (j : Fin M) : Root :=
  ⟨b.val * M + j.val, by
    have hb := b.isLt
    have hj := j.isLt
    have hq : 4 * M ≤ q := by unfold q K; omega
    simp only [M] at *
    omega⟩

def ownershipRoot (b : Fin 2) (j : Fin κ) : Root :=
  ⟨4 * M + b.val * κ + j.val, by
    have hb := b.isLt
    have hj := j.isLt
    have hq : 4 * M + 2 * κ ≤ q := by unfold q K; omega
    simp only [κ, M] at *
    omega⟩

def genericRoot (j : Fin N) : Root :=
  ⟨K + j.val, by have hj := j.isLt; unfold q; omega⟩

def matchingBlock : Fin 4 → Block := ![.match0, .match1, .match2, .match3]
def ownerType : Fin 2 → PhysicalType := ![.ownerH, .ownerV]

def layerRoot : Layer → Root
  | ⟨.match0, j⟩ => matchingRoot 0 j
  | ⟨.match1, j⟩ => matchingRoot 1 j
  | ⟨.match2, j⟩ => matchingRoot 2 j
  | ⟨.match3, j⟩ => matchingRoot 3 j
  | ⟨.ownerH, j⟩ => ownershipRoot 0 j
  | ⟨.ownerV, j⟩ => ownershipRoot 1 j

def IsGeneric (r : Root) : Prop := K ≤ r.val ∧ r.val < K + N
def IsPassive (r : Root) : Prop := K + N ≤ r.val

instance (r : Root) : Decidable (IsGeneric r) :=
  inferInstanceAs (Decidable (K ≤ r.val ∧ r.val < K + N))
instance (r : Root) : Decidable (IsPassive r) :=
  inferInstanceAs (Decidable (K + N ≤ r.val))

theorem genericRoot_isGeneric (j : Fin N) : IsGeneric (genericRoot j) := by
  have hj := j.isLt
  change K ≤ K + j.val ∧ K + j.val < K + N
  omega

theorem layerRoot_special (r : Layer) : (layerRoot r).val < K := by
  obtain ⟨b, j⟩ := r
  cases b
  all_goals
    have hj := j.isLt
    norm_num [layerRoot, matchingRoot, ownershipRoot, repetitions, K, κ, M] at *
    omega

theorem layerRoot_not_passive (r : Layer) : ¬ IsPassive (layerRoot r) := by
  have h := layerRoot_special r
  unfold IsPassive
  omega

end TranscendentalTuran.Encoding
