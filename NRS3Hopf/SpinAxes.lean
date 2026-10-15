/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.EqualSteps
public import NRS3Hopf.SlTwoIdentity

/-!
# Spin on the open axis, rotation on the closed one

**The open axis.** With `j = (d − 1)/2`, the centred positions are `m/j`, so `P_d = J_z/j` for
every `d`. The transport is `J_x/j` only for `d = 2`, `3`: `T₂ = σ_x`, `P₂ = −σ_z` (Pauli 1927,
spin `1/2`) and `T₃ = L_x`, `P₃ = L_z` (spin `1`). There the algebra of spin closes,
`[T, [T, P]] = c P` as for `[J_x, [J_x, J_z]] = J_z`, and NRS on `T_d : P_d` is Robertson for
angular momentum. For `d ≥ 4` it does not close (`LieClosure.closure_iff`, `D49i`). The algebra
of spin closes exactly where Robertson saturates (`D23`).

**The closed axis.** On the ring of three positions the cyclic step `U`, `0 → 1 → 2 → 0`, is a
rotation: `UᵀU = 1`, `det U = 1`, `U³ = 1`. With `K = U − Uᵀ`, `K³ = −3K`, so `N = K/√3` is the
generator of rotations about the axis `(1, 1, 1)`, `N³ = −N`, and

  `U = 1 + (1/2) K + (1/2) K² = 1 + sin(2π/3) N + (1 − cos(2π/3)) N²`,

the rotation by `2π/3`. The transport of the ring is its symmetric part, `T° = (U + Uᵀ)/2`, and
it commutes with the generator, `[T°, K] = 0`: closing the axis makes the transport conserve a
rotation.

## Main results

- `SpinAxes.Td_two` : `T₂ = σ_x` (with `P₂ = −σ_z`, `SlTwoIdentity.Pd_two`).
- `SpinAxes.Td_three` : `T₃ = L_x` (with `P₃ = L_z`, `SlTwoIdentity.Pd_three`).
- `SpinAxes.spin_closes_iff` : `[T_d, [T_d, P_d]] = c P_d` for some `c` exactly when
  `d = 2` or `d = 3`.
- `SpinAxes.U_rotation` : `UᵀU = 1`, `det U = 1`, `U³ = 1`.
- `SpinAxes.rodrigues` : `U = 1 + (1/2) K + (1/2) K²`, with `K³ = −3K`.
- `SpinAxes.Tc_eq`, `SpinAxes.lie_Tc_K` : `T° = (U + Uᵀ)/2`, and `[T°, K] = 0`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace SpinAxes

/-! ## 1. Spin `1/2` and spin `1` on the open axis -/

theorem rho_two : rho 2 = 1 := by
  rw [rho, show Real.pi / ((2 : ℕ) + 1 : ℝ) = Real.pi / 3 by norm_num, Real.cos_pi_div_three]
  norm_num

theorem rho_three : rho 3 = √2 := by
  rw [rho, show Real.pi / ((3 : ℕ) + 1 : ℝ) = Real.pi / 4 by norm_num, Real.cos_pi_div_four]
  ring

/-- **`T₂ = σ_x`**, and `P₂ = −σ_z` (`SlTwoIdentity.Pd_two`). -/
theorem Td_two : Td 2 = !![0, 1; 1, 0] := by
  rw [SlTwoIdentity.Td_eq, rho_two, SlTwoIdentity.Ad_two]; simp

/-- **`T₃ = L_x`**, the spin-`1` matrix `(1/√2)·(adjacency of three positions)`, and
`P₃ = L_z` (`SlTwoIdentity.Pd_three`). -/
theorem Td_three : Td 3 = ((√2 : ℝ) : ℂ)⁻¹ • !![0, 1, 0; 1, 0, 1; 0, 1, 0] := by
  rw [SlTwoIdentity.Td_eq, rho_three, SlTwoIdentity.Ad_three]

theorem spin_two : ⁅Td 2, ⁅Td 2, Pd 2⁆⁆ = (4 : ℂ) • Pd 2 := by
  rw [SlTwoIdentity.Td_eq, rho_two, Complex.ofReal_one, inv_one, one_smul, SlTwoIdentity.two_A]

theorem spin_three : ⁅Td 3, ⁅Td 3, Pd 3⁆⁆ = (1 : ℂ) • Pd 3 := by
  have hs : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ * 2 = 1 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [SlTwoIdentity.Td_eq, rho_three, smul_lie, smul_lie, lie_smul, SlTwoIdentity.three_A,
    smul_smul, smul_smul, hs]

theorem lie_lie_eq_D (d : ℕ) : ⁅Td d, ⁅Td d, Pd d⁆⁆ = LieClosure.D d := by
  simp only [Ring.lie_def, LieClosure.D, LieClosure.C]

/-- **The algebra of spin closes exactly for `d = 2`, `3`**, where Robertson saturates. -/
theorem spin_closes_iff {d : ℕ} (hd : 2 ≤ d) :
    (∃ c : ℂ, ⁅Td d, ⁅Td d, Pd d⁆⁆ = c • Pd d) ↔ d = 2 ∨ d = 3 := by
  constructor
  · rintro ⟨c, hc⟩
    exact (LieClosure.closure_iff hd).mp ⟨0, c, 0, by rw [← lie_lie_eq_D, hc]; simp⟩
  · rintro (rfl | rfl)
    exacts [⟨4, spin_two⟩, ⟨1, spin_three⟩]

/-! ## 2. The cyclic step of the ring is a rotation -/

/-- The cyclic step `0 → 1 → 2 → 0` of the closed axis. -/
def U : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The generator `K = U − Uᵀ`, `√3` times the rotation generator about `(1, 1, 1)`. -/
def K : Matrix (Fin 3) (Fin 3) ℂ := U - Uᵀ

/-- **The cyclic step is a rotation of order three**: `UᵀU = 1`, `det U = 1`, `U³ = 1`. -/
theorem U_rotation : Uᵀ * U = 1 ∧ U.det = 1 ∧ U ^ 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [U, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [U, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem K_cube : K * K * K = (-3 : ℂ) • K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K, U, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- **Rodrigues**: `U = 1 + (1/2) K + (1/2) K²`, the rotation by `2π/3` about `(1, 1, 1)`. -/
theorem rodrigues : U = 1 + (1 / 2 : ℂ) • K + (1 / 2 : ℂ) • (K * K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, U, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem K_axis : K *ᵥ ![1, 1, 1] = 0 := by
  ext i; fin_cases i <;> simp [K, U, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **The transport of the ring is the symmetric part of the rotation.** -/
theorem Tc_eq : ClosedThree.Tc = (1 / 2 : ℂ) • (U + Uᵀ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ClosedThree.Tc, U]

/-- **The transport of the ring conserves the rotation**: `[T°, K] = 0`. -/
theorem lie_Tc_K : ⁅ClosedThree.Tc, K⁆ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, ClosedThree.Tc, K, U, Matrix.mul_apply, Fin.sum_univ_three]

end SpinAxes
