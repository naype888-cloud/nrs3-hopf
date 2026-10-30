/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.LatticeFiberDirac

/-!
# The floor of the lattice spacing from the mass gap

On `ℤ³ × w` the Dirac operator `D` has `|E| ≥ 1/2` for every eigenvalue
(`LatticeFiberDirac.abs_energy_ge`). `D` is dimensionless: with spacing `a` the physical energy is
`E_phys = (ħ c / a) E`, so the mass gap is `ħ c / (2 a)` and it grows like `1 / a`. If the physical
energies are bounded by a maximum `Emax` (the Planck energy, say), the spacing cannot be smaller
than `ħ c / (2 Emax)`: the gap alone already exceeds `Emax` below that. Sending `a` to `0`
sends the gap to infinity.

## Main results

- `DiracFloor.abs_physical_energy_ge` : `ħ c / (2 a) ≤ |(ħ c / a) E|` for every eigenvalue.
- `DiracFloor.spacing_floor` : if an eigenvalue has physical energy at most `Emax`, then
  `ħ c / (2 Emax) ≤ a`.
- `DiracFloor.no_zero_spacing` : no sequence of spacings tends to `0` while the physical energies
  of one eigenvector each stay below `Emax`.

The bound `Emax` is a hypothesis; it is not derived here.
-/

@[expose] public noncomputable section

open Filter Topology

namespace DiracFloor

/-- **The physical mass gap**: with spacing `a > 0`, every eigenvalue of `D` has physical energy
at least `ħ c / (2 a)`. -/
theorem abs_physical_energy_ge {a hc E : ℝ} (ha : 0 < a) (hhc : 0 < hc)
    {χ : LatticeFiberDirac.H} (hχ : χ ≠ 0) (hE : LatticeFiberDirac.dirac χ = (E : ℂ) • χ) :
    hc / (2 * a) ≤ |hc / a * E| := by
  have h := LatticeFiberDirac.abs_energy_ge hχ hE
  rw [abs_mul, abs_of_pos (div_pos hhc ha)]
  calc hc / (2 * a) = hc / a * (1 / 2) := by field_simp
    _ ≤ hc / a * |E| := mul_le_mul_of_nonneg_left h (div_pos hhc ha).le

/-- **The floor of the spacing**: if an eigenvalue of `D` has physical energy at most `Emax`,
then `a ≥ ħ c / (2 Emax)`. -/
theorem spacing_floor {a hc E Emax : ℝ} (ha : 0 < a) (hhc : 0 < hc) (hEmax : 0 < Emax)
    {χ : LatticeFiberDirac.H} (hχ : χ ≠ 0) (hE : LatticeFiberDirac.dirac χ = (E : ℂ) • χ)
    (hle : |hc / a * E| ≤ Emax) : hc / (2 * Emax) ≤ a := by
  have h := (abs_physical_energy_ge ha hhc hχ hE).trans hle
  rw [div_le_iff₀ (by positivity)] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **No zero spacing**: there is no sequence of positive spacings tending to `0` with, for each,
an eigenvector of physical energy at most `Emax`. -/
theorem no_zero_spacing {hc Emax : ℝ} (hhc : 0 < hc) (hEmax : 0 < Emax) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hev : ∀ n, ∃ (E : ℝ) (χ : LatticeFiberDirac.H), χ ≠ 0 ∧
      LatticeFiberDirac.dirac χ = (E : ℂ) • χ ∧ |hc / a n * E| ≤ Emax) :
    ¬ Tendsto a atTop (𝓝 0) := fun h => by
  have hpos : 0 < hc / (2 * Emax) := by positivity
  have hev' := (h.eventually (gt_mem_nhds hpos)).exists
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨E, χ, hχ, hE, hle⟩ := hev n
  exact absurd (spacing_floor (ha n) hhc hEmax hχ hE hle) (not_le.mpr hn)

end DiracFloor
