/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.KogutSusskind
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The lattice side of Planck's dichotomy

Poincaré's theorem (`NRS3Poincare.Poincare1912_Discreteness.no_density_planck`; in Physlib,
`quantizedOscillator_meanEnergy_lt` and `spectralRadiance_lt_rayleighJeans`, #1761) says that
Planck's law cannot come from an energy weight `w(E) dE` with a density: it has an atom at
`E = 0`. This file shows the other half of the dichotomy for the Yang-Mills lattice at fixed
spacing: its thermal energy measure is purely atomic, hence it is never a density.

A finite-dimensional Hermitian operator has finitely many eigenvalues, and its thermal energy
measure `∑ᵢ δ_{λᵢ}` has an atom at each of them. The Kogut-Susskind Hamiltonian of
`KogutSusskind` is such an operator, for every gauge group `G`, every lattice and every spacing.

## Main results

- `PlanckBridge.thermal_ne_withDensity` : the thermal energy measure of a Hermitian matrix is
  never `volume.withDensity w`.
- `PlanckBridge.lintegral_thermal` : its partition function is `∑ᵢ e^{-β λᵢ}`.
- `PlanckBridge.hamMatrix` : the Kogut-Susskind Hamiltonian as a matrix on the link
  configurations; `hamMatrix_isHermitian`, `ham_eq_mulVec`.
- `PlanckBridge.ham_thermal_ne_withDensity` : **no energy weight with a density is the thermal
  measure of the lattice Hamiltonian**, for every volume and every coupling.

Nothing here sends the spacing to zero, and nothing is claimed about a continuum limit: the
statement is that at every `a > 0` the theory is on the atomic side of Planck's dichotomy.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix

namespace PlanckBridge

/-! ## 1. A Hermitian matrix has an atomic thermal measure -/

section Atomic

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The thermal energy measure: one atom at each eigenvalue. -/
def thermal (hA : A.IsHermitian) : Measure ℝ := ∑ i, Measure.dirac (hA.eigenvalues i)

/-- Every eigenvalue is an atom. -/
theorem thermal_atom (hA : A.IsHermitian) (i : n) : 1 ≤ thermal hA {hA.eigenvalues i} := by
  unfold thermal
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact le_trans (by simp) (Finset.single_le_sum (f := fun j =>
    Measure.dirac (hA.eigenvalues j) {hA.eigenvalues i}) (fun _ _ => bot_le)
    (Finset.mem_univ i))

/-- **The thermal measure of a finite-dimensional Hermitian operator is never a density.** -/
theorem thermal_ne_withDensity [Nonempty n] (hA : A.IsHermitian) (w : ℝ → ENNReal) :
    thermal hA ≠ volume.withDensity w := fun h => by
  obtain ⟨i⟩ := ‹Nonempty n›
  have h0 : volume.withDensity w {hA.eigenvalues i} = 0 :=
    withDensity_absolutelyContinuous _ _ Real.volume_singleton
  have := thermal_atom hA i
  rw [h, h0] at this
  simp at this

/-- The partition function is the finite sum `∑ᵢ e^{-β λᵢ}`. -/
theorem lintegral_thermal (hA : A.IsHermitian) (β : ℝ) :
    ∫⁻ E, ENNReal.ofReal (Real.exp (-β * E)) ∂thermal hA
      = ∑ i, ENNReal.ofReal (Real.exp (-β * hA.eigenvalues i)) := by
  unfold thermal
  rw [lintegral_finset_sum_measure]
  exact Finset.sum_congr rfl fun i _ => lintegral_dirac' _ (by fun_prop)

end Atomic

/-! ## 2. The Kogut-Susskind Hamiltonian is such an operator -/

section Lattice

open KogutSusskind

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G] {n : ℕ} (ρ : G →* unitaryGroup (Fin n) ℂ)
  (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ)) (lE lB : ℝ)

theorem ham_add (φ ψ : State ι δ G) :
    ham ρ τ R lE lB (φ + ψ) = ham ρ τ R lE lB φ + ham ρ τ R lE lB ψ := by
  funext U
  simp only [ham, elecTotal, elec, elecProj, mag, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    add_sub_add_comm]
  ring

theorem ham_smul (c : ℂ) (ψ : State ι δ G) :
    ham ρ τ R lE lB (c • ψ) = c • ham ρ τ R lE lB ψ := by
  funext U
  simp only [ham, elecTotal, elec, elecProj, mag, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The Hamiltonian as a matrix on the link configurations. -/
def hamMatrix : Matrix (Conf ι δ G) (Conf ι δ G) ℂ :=
  fun U V => ham ρ τ R lE lB (Pi.single V 1) U

theorem ham_eq_mulVec (ψ : State ι δ G) : ham ρ τ R lE lB ψ = hamMatrix ρ τ R lE lB *ᵥ ψ := by
  have hψ : ψ = ∑ V, ψ V • (Pi.single V 1 : State ι δ G) := by
    funext U; simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ s : Finset (Conf ι δ G), ham ρ τ R lE lB (∑ V ∈ s, ψ V • (Pi.single V 1 : State ι δ G))
      = ∑ V ∈ s, ψ V • ham ρ τ R lE lB (Pi.single V 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using ham_smul ρ τ R lE lB 0 0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ham_add, ham_smul, ih]
  funext U
  conv_lhs => rw [hψ, hlin]
  simp [mulVec, dotProduct, hamMatrix, Finset.sum_apply, mul_comm]

theorem hamMatrix_isHermitian : (hamMatrix ρ τ R lE lB).IsHermitian := by
  ext U V
  have h := ham_symm ρ τ R lE lB (Pi.single U 1) (Pi.single V 1)
  simp only [ip, Pi.single_apply, hamMatrix, conjTranspose_apply] at h ⊢
  simpa [ite_mul, mul_ite] using h.symm

/-- **No energy weight with a density is the thermal measure of the lattice Hamiltonian**, for
every volume, every gauge group and every coupling. -/
theorem ham_thermal_ne_withDensity (w : ℝ → ENNReal) :
    thermal (hamMatrix_isHermitian ρ τ R lE lB) ≠ volume.withDensity w :=
  haveI : Nonempty (Conf ι δ G) := ⟨fun _ _ => 1⟩
  thermal_ne_withDensity _ w

end Lattice

end PlanckBridge
