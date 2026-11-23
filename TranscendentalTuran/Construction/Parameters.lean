module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Range
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Exact construction parameters

Formalization author and responsible maintainer: Xizhi Liu.

The constants are represented symbolically. In particular, no evaluation of
the finite type of all roots or of all candidate forbidden graphs is needed.
-/

namespace TranscendentalTuran.Parameters

def M : ℕ := 512
def κ : ℕ := 8 * M
def K : ℕ := 4 * M + 2 * κ
def N : ℕ := K ^ 4
def q : ℕ := 32 * N + K
def profileCount : ℕ := 64
def guardBlockSize : ℕ := 512
def certificateData : ℕ := 13
def certificateRoots : ℕ := 40

theorem M_value : M = 512 := rfl
theorem κ_value : κ = 4096 := by norm_num [κ, M]
theorem K_value : K = 10240 := by norm_num [K, κ, M]
theorem N_value : N = 10995116277760000 := by norm_num [N, K, κ, M]
theorem q_value : q = 351843720888330240 := by norm_num [q, N, K, κ, M]
theorem M_pos : 0 < M := by norm_num [M]
theorem κ_pos : 0 < κ := by norm_num [κ, M]
theorem K_pos : 0 < K := by norm_num [K, κ, M]
theorem N_pos : 0 < N := by norm_num [N, K, κ, M]
theorem q_pos : 0 < q := by norm_num [q, N, K, κ, M]
theorem q_large : 10 ^ 12 < q := by norm_num [q, N, K, κ, M]
theorem q_large_K : 10 ^ 6 * K < q := by norm_num [q, N, K, κ, M]
theorem q_guard_large : 256 * guardBlockSize ^ 3 < q := by
  norm_num [q, N, K, κ, M, guardBlockSize]
theorem guard_divides : 4 * guardBlockSize ∣ 3 * q := by
  refine ⟨515396075520015, ?_⟩
  norm_num [q, N, K, κ, M, guardBlockSize]
theorem profiles_fit : 6 * profileCount < guardBlockSize := by
  norm_num [profileCount, guardBlockSize]
theorem certificate_avoidance : certificateRoots + certificateData - 1 < profileCount := by
  norm_num [certificateRoots, certificateData, profileCount]
theorem passive_pair_room : 2 * (7 * N) < 31 * N := by
  have := N_pos
  omega

/-- The finite obstruction order supplied by the bounded-root search.
Keeping the root count as an argument avoids evaluating the astronomically
large closed expression when this module is loaded. -/
def obstructionBound (rootCount : ℕ) : ℕ :=
  certificateData * ∑ i ∈ Finset.range (rootCount + 1), (certificateData * rootCount) ^ i

private theorem geometric_bound_pos (a b w : ℕ) (hw : 0 < w) :
    0 < w * ∑ i ∈ Finset.range (a + 1), b ^ i := by
  apply Nat.mul_pos hw
  have h := Finset.single_le_sum (f := fun i : ℕ => b ^ i)
    (fun _ _ => Nat.zero_le _) (show 0 ∈ Finset.range (a + 1) by simp)
  simp only [pow_zero] at h
  omega

theorem obstructionBound_pos (rootCount : ℕ) : 0 < obstructionBound rootCount :=
  geometric_bound_pos rootCount (certificateData * rootCount) certificateData
    (by norm_num [certificateData])

end TranscendentalTuran.Parameters
