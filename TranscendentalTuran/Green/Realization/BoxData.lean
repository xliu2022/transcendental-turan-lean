/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xizhi Liu
-/
module

public import TranscendentalTuran.Green.Realization.PartialInverse
public import TranscendentalTuran.Green.FiniteNetwork.BoxGeometry
public import TranscendentalTuran.Network.Types

@[expose] public section

noncomputable section

namespace TranscendentalTuran.Green.Realization

open Network FiniteNetwork

/-- Anchors of horizontal chains incident with the box; the first coordinate is
shifted by one, so anchor zero represents an omitted endpoint at `i=-1`. -/
abbrev EAnchor (n : ℕ) := Fin (n + 2) × Fin (n + 1)

/-- Anchors of diagonal chains.  The two additional chains without a base endpoint
are harmless components of zero weight, and make this a rectangular finite type. -/
abbrev DAnchor (n : ℕ) := Fin (n + 2) × Fin (n + 2)

def eStart (n : ℕ) : Box n ↪ EAnchor n where
  toFun v := (v.1.succ, v.2)
  inj' := by
    intro v w h
    apply Prod.ext
    · apply Fin.ext
      have hh := congrArg (fun e : EAnchor n => e.1.val) h
      simpa using hh
    · exact congrArg (fun e : EAnchor n => e.2) h

def eEnd (n : ℕ) : Box n ↪ EAnchor n where
  toFun v := (v.1.castSucc, v.2)
  inj' := by
    intro v w h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun e : EAnchor n => e.1.val) h)
    · exact congrArg (fun e : EAnchor n => e.2) h

def dStart (n : ℕ) : Box n ↪ DAnchor n where
  toFun v := (v.1.succ, v.2.castSucc)
  inj' := by
    intro v w h
    apply Prod.ext
    · apply Fin.ext
      have hh := congrArg (fun e : DAnchor n => e.1.val) h
      simpa using hh
    · exact Fin.ext (congrArg (fun e : DAnchor n => e.2.val) h)

def dEnd (n : ℕ) : Box n ↪ DAnchor n where
  toFun v := (v.1.castSucc, v.2.succ)
  inj' := by
    intro v w h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun e : DAnchor n => e.1.val) h)
    · apply Fin.ext
      have hh := congrArg (fun e : DAnchor n => e.2.val) h
      simpa using hh

/-- The fiber of each of the seven physical types. -/
def Fiber (n : ℕ) : PhysicalType → Type
  | .base => Box n
  | .port01 | .port23 => EAnchor n ⊕ DAnchor n
  | .center13 => EAnchor n
  | .center02 => DAnchor n
  | .ownerH | .ownerV => Fin (n + 1)

instance (n : ℕ) (τ : PhysicalType) : Fintype (Fiber n τ) := by
  cases τ <;> dsimp [Fiber] <;> infer_instance

instance (n : ℕ) (τ : PhysicalType) : DecidableEq (Fiber n τ) := by
  cases τ <;> dsimp [Fiber] <;> infer_instance

abbrev Vertex (n : ℕ) := (τ : PhysicalType) × Fiber n τ

def type {n : ℕ} (v : Vertex n) : PhysicalType := v.1

def base {n : ℕ} (v : Box n) : Vertex n := ⟨.base, v⟩
def port01E {n : ℕ} (e : EAnchor n) : Vertex n := ⟨.port01, Sum.inl e⟩
def port01D {n : ℕ} (e : DAnchor n) : Vertex n := ⟨.port01, Sum.inr e⟩
def port23E {n : ℕ} (e : EAnchor n) : Vertex n := ⟨.port23, Sum.inl e⟩
def port23D {n : ℕ} (e : DAnchor n) : Vertex n := ⟨.port23, Sum.inr e⟩
def center13 {n : ℕ} (e : EAnchor n) : Vertex n := ⟨.center13, e⟩
def center02 {n : ℕ} (e : DAnchor n) : Vertex n := ⟨.center02, e⟩
def ownerH {n : ℕ} (i : Fin (n + 1)) : Vertex n := ⟨.ownerH, i⟩
def ownerV {n : ℕ} (j : Fin (n + 1)) : Vertex n := ⟨.ownerV, j⟩

/-- Every individual matching layer uses the same private four-resistor chains;
every ownership layer attaches a base to its row or column owner. -/
def center (n : ℕ) : Block → Vertex n → Option (Vertex n)
  | .match0, ⟨.port01, Sum.inl e⟩ => (partialInverse (eStart n) e).map base
  | .match0, ⟨.port01, Sum.inr e⟩ => some (center02 e)
  | .match1, ⟨.port01, Sum.inl e⟩ => some (center13 e)
  | .match1, ⟨.port01, Sum.inr e⟩ => (partialInverse (dStart n) e).map base
  | .match2, ⟨.port23, Sum.inl e⟩ => (partialInverse (eEnd n) e).map base
  | .match2, ⟨.port23, Sum.inr e⟩ => some (center02 e)
  | .match3, ⟨.port23, Sum.inl e⟩ => some (center13 e)
  | .match3, ⟨.port23, Sum.inr e⟩ => (partialInverse (dEnd n) e).map base
  | .ownerH, ⟨.base, v⟩ => some (ownerH v.1)
  | .ownerV, ⟨.base, v⟩ => some (ownerV v.2)
  | _, _ => none

/-- The lower-left base is the unique marked vertex. -/
def mark (n : ℕ) : Vertex n := base (boxRoot n)

@[simp] theorem type_base {n : ℕ} (v : Box n) : type (base v) = .base := rfl
@[simp] theorem type_mark (n : ℕ) : type (mark n) = .base := rfl

@[simp] theorem base_inj {n : ℕ} (v w : Box n) : base v = base w ↔ v = w := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact congrArg base h

@[simp] theorem center_m0_p01E {n : ℕ} (e : EAnchor n) (v : Box n) :
    center n .match0 (port01E e) = some (base v) ↔ eStart n v = e := by
  simp [center, port01E, Option.map_eq_some_iff, partialInverse_some_iff, base_inj]

@[simp] theorem center_m1_p01D {n : ℕ} (e : DAnchor n) (v : Box n) :
    center n .match1 (port01D e) = some (base v) ↔ dStart n v = e := by
  simp [center, port01D, Option.map_eq_some_iff, partialInverse_some_iff, base_inj]

@[simp] theorem center_m2_p23E {n : ℕ} (e : EAnchor n) (v : Box n) :
    center n .match2 (port23E e) = some (base v) ↔ eEnd n v = e := by
  simp [center, port23E, Option.map_eq_some_iff, partialInverse_some_iff, base_inj]

@[simp] theorem center_m3_p23D {n : ℕ} (e : DAnchor n) (v : Box n) :
    center n .match3 (port23D e) = some (base v) ↔ dEnd n v = e := by
  simp [center, port23D, Option.map_eq_some_iff, partialInverse_some_iff, base_inj]

/-- A complete horizontal chain changes precisely the first coordinate by one. -/
theorem e_endpoint_coordinates {n : ℕ} {v w : Box n} (h : eStart n v = eEnd n w) :
    w.1.val = v.1.val + 1 ∧ w.2 = v.2 := by
  constructor
  · exact (congrArg (fun e : EAnchor n => e.1.val) h).symm
  · exact (congrArg Prod.snd h).symm

/-- A complete diagonal chain increases the first coordinate and decreases the
second coordinate by one; the second equality is written without subtraction. -/
theorem d_endpoint_coordinates {n : ℕ} {v w : Box n} (h : dStart n v = dEnd n w) :
    w.1.val = v.1.val + 1 ∧ v.2.val = w.2.val + 1 := by
  exact ⟨(congrArg (fun e : DAnchor n => e.1.val) h).symm,
    congrArg (fun e : DAnchor n => e.2.val) h⟩

end TranscendentalTuran.Green.Realization
