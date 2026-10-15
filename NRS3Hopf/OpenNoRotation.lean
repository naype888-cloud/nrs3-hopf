/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.SpinAxes
public import NavaRobertsonIndependent.Mathematics.D6_Fiedler

/-!
# The open axis conserves no rotation, the closed axis conserves one

A rotation generator is an antisymmetric matrix, `Kᵀ = −K`. On the open axis the Fiedler modes
`s_k`, with angles `(k + 1)π/(d + 1)`, are real eigenvectors of `T_d` with distinct eigenvalues
(`D6`). If `K` commutes with `T_d`, it keeps each mode, `K s_k = λ_k s_k`; antisymmetry gives
`s_kᵀ K s_k = 0`, and `s_kᵀ s_k > 0` since the mode is real, so `λ_k = 0`. `K` annihilates the
basis of modes: `K = 0`.

On the closed axis with three positions the generator `K = U − Uᵀ` of the rotation by `2π/3`
is antisymmetric, nonzero, and commutes with `T°` (`SpinAxes`). Closing the axis is what makes
the transport conserve a rotation.

## Main results

- `OpenNoRotation.open_no_rotation` : on the open axis, an antisymmetric matrix commuting with
  `T_d` is `0`.
- `OpenNoRotation.closed_rotation` : on the closed axis a nonzero antisymmetric matrix commutes
  with `T°`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace OpenNoRotation

variable {d : ℕ}

/-- `vᵀ K v = 0` for antisymmetric `K`. -/
theorem dotProduct_mulVec_self {K : Matrix (Fin d) (Fin d) ℂ} (hK : Kᵀ = -K) (v : Fin d → ℂ) :
    v ⬝ᵥ (K *ᵥ v) = 0 := by
  have h : v ⬝ᵥ (K *ᵥ v) = -(v ⬝ᵥ (K *ᵥ v)) := by
    calc v ⬝ᵥ (K *ᵥ v) = (v ᵥ* K) ⬝ᵥ v := dotProduct_mulVec v K v
      _ = (Kᵀ *ᵥ v) ⬝ᵥ v := by rw [mulVec_transpose]
      _ = -(v ⬝ᵥ (K *ᵥ v)) := by rw [hK, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linear_combination h / 2

/-- A Fiedler mode has `s_kᵀ s_k ≠ 0`: it is real and nonzero. -/
theorem sineMode_dotProduct_ne_zero (hd : 1 ≤ d) (k : Fin d) :
    sineMode d k ⬝ᵥ sineMode d k ≠ 0 := by
  have hreal : sineMode d k ⬝ᵥ sineMode d k =
      ((∑ j : Fin d, Real.sin (((j.val : ℝ) + 1) * modeAngle d k) ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, sineMode, sq]
  rw [hreal, Complex.ofReal_ne_zero]
  obtain ⟨j, hj⟩ : ∃ j, sineMode d k j ≠ 0 := by
    by_contra h
    push Not at h
    exact sineMode_ne_zero hd k (funext h)
  have hj' : Real.sin (((j.val : ℝ) + 1) * modeAngle d k) ≠ 0 := by
    intro h; apply hj; simp only [sineMode, h, Complex.ofReal_zero]
  exact (Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ _, by positivity⟩).ne'

/-- A matrix commuting with `A_d` keeps each Fiedler mode. -/
theorem mulVec_sineMode (hd : 1 ≤ d) {K : Matrix (Fin d) (Fin d) ℂ} (hc : Ad d * K = K * Ad d)
    (k : Fin d) : K *ᵥ sineMode d k = (sineModeBasis hd).repr (K *ᵥ sineMode d k) k •
      sineMode d k := by
  set w := K *ᵥ sineMode d k
  have hAw : Matrix.toLin' (Ad d) w = eigenvalueAd d k • w := by
    have hs : (fun i => (2 * Real.cos (modeAngle d k) : ℂ) * sineMode d k i) =
        eigenvalueAd d k • sineMode d k := by
      funext i; simp [eigenvalueAd]
    rw [Matrix.toLin'_apply, mulVec_mulVec, hc, ← mulVec_mulVec, Ad_sineMode hd k, hs,
      mulVec_smul]
  have hzero (j : Fin d) (hj : j ≠ k) : (sineModeBasis hd).repr w j = 0 := by
    have h := repr_Ad hd w j
    rw [hAw, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have hne : eigenvalueAd d j - eigenvalueAd d k ≠ 0 :=
      sub_ne_zero.mpr (fun h => hj (eigenvalueAd_injective h))
    have : (eigenvalueAd d j - eigenvalueAd d k) * (sineModeBasis hd).repr w j = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left hne
  conv_lhs => rw [← (sineModeBasis hd).sum_repr w]
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hzero j hj, zero_smul]) (by simp),
    sineModeBasis_apply]

/-- **The open axis conserves no rotation**: an antisymmetric matrix commuting with `T_d` is
`0`. -/
theorem open_no_rotation (hd : 2 ≤ d) {K : Matrix (Fin d) (Fin d) ℂ} (hK : Kᵀ = -K)
    (hc : ⁅Td d, K⁆ = 0) : K = 0 := by
  have hd1 : 1 ≤ d := by omega
  have hρ : ((rho d : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (rho_pos d hd).ne')
  have hA : Ad d * K = K * Ad d := by
    rw [Ring.lie_def, SlTwoIdentity.Td_eq, smul_mul_assoc, mul_smul_comm, ← smul_sub,
      smul_eq_zero] at hc
    exact sub_eq_zero.mp (hc.resolve_left hρ)
  have hkill (k : Fin d) : K *ᵥ sineMode d k = 0 := by
    have hk := mulVec_sineMode hd1 hA k
    set c := (sineModeBasis hd1).repr (K *ᵥ sineMode d k) k
    have h0 := dotProduct_mulVec_self hK (sineMode d k)
    rw [hk, dotProduct_smul, smul_eq_mul] at h0
    have hc0 : c = 0 := (mul_eq_zero.mp h0).resolve_right (sineMode_dotProduct_ne_zero hd1 k)
    rw [hk, hc0, zero_smul]
  have hlin : Matrix.toLin' K = 0 := (sineModeBasis hd1).ext fun k => by
    rw [sineModeBasis_apply, Matrix.toLin'_apply, hkill, LinearMap.zero_apply]
  exact Matrix.toLin'.injective (by rw [hlin, map_zero])

/-- **The closed axis conserves a rotation**: `K = U − Uᵀ` is antisymmetric, nonzero, and
commutes with `T°`. -/
theorem closed_rotation : ∃ K : Matrix (Fin 3) (Fin 3) ℂ, K ≠ 0 ∧ Kᵀ = -K ∧
    ⁅ClosedThree.Tc, K⁆ = 0 := by
  refine ⟨SpinAxes.K, fun h => ?_, ?_, SpinAxes.lie_Tc_K⟩
  · have := congrFun (congrFun h 1) 0
    simp [SpinAxes.K, SpinAxes.U] at this
  · simp [SpinAxes.K, transpose_sub]

end OpenNoRotation
