/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.KogutSusskindGap
public import Mathlib.Algebra.Group.Defs

/-!
# Kogut-Susskind Yang-Mills on the four axes of the box

The Yang-Mills chain of `KogutSusskind*` is stated for arbitrary sites with commuting steps. Here
it is placed on the topology of this repository: the sites are the points `(x, y, z, w)` of the
box, one coordinate per axis, with the four steps `τ μ` (one per axis) and the plaquettes in the
`6` planes `(μ, ν)`, `μ < ν`.

## Main results

- `HopfYangMills.step_comm` : the steps of different axes commute.
- `HopfYangMills.planes` : the `6` planes of the four axes.
- `HopfYangMills.ham_gauge` : **Gauss law** for the Hamiltonian on the four axes.
- `HopfYangMills.gap_ham` : the strong-coupling gap `λE` above the constants at finite volume.
-/

@[expose] public noncomputable section

open Finset KogutSusskind KogutSusskindGap

namespace HopfYangMills

/-- The sites of the box: one position in `Z` (a cyclic group `ℤ/L`) on each of the four axes. -/
abbrev Site (Z : Type*) := Fin 4 → Z

variable {Z : Type*} [AddCommGroup Z] [One Z] [DecidableEq Z]

/-- The step of one unit on the axis `μ`. -/
def step (Z : Type*) [AddCommGroup Z] [One Z] [DecidableEq Z] (μ : Fin 4) : Site Z ≃ Site Z where
  toFun p := Function.update p μ (p μ + 1)
  invFun p := Function.update p μ (p μ - 1)
  left_inv p := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp
    · simp [h]
  right_inv p := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp
    · simp [h]

/-- The steps of different axes commute. -/
theorem step_comm (μ ν : Fin 4) (p : Site Z) :
    step Z ν (step Z μ p) = step Z μ (step Z ν p) := by
  by_cases h : μ = ν
  · subst h; rfl
  · funext κ
    by_cases hμ : κ = μ
    · subst hμ; simp [step, h]
    · by_cases hν : κ = ν
      · subst hν; simp [step, h, Ne.symm h]
      · simp [step, hμ, hν]

/-- The plaquettes: every site, in each of the `6` planes `(μ, ν)` with `μ < ν`. -/
def planes (Z : Type*) [AddCommGroup Z] [One Z] [DecidableEq Z] [Fintype Z] :
    Finset (Site Z × Fin 4 × Fin 4) :=
  Finset.univ.filter fun r => r.2.1 < r.2.2

variable [Fintype Z] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Gauss law on the four axes**: the Hamiltonian commutes with every gauge transformation. -/
theorem ham_gauge {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (lE lB : ℝ)
    (g : Site Z → G) (ψ : State (Site Z) (Fin 4) G) :
    ham ρ (step Z) (planes Z) lE lB (gaugeState (step Z) g ψ)
      = gaugeState (step Z) g (ham ρ (step Z) (planes Z) lE lB ψ) :=
  by
  have h : ∀ r ∈ planes Z, step Z r.2.2 (step Z r.2.1 r.1) = step Z r.2.1 (step Z r.2.2 r.1) :=
    fun r _ => step_comm r.2.1 r.2.2 r.1
  exact KogutSusskind.ham_gauge (ι := Site Z) (δ := Fin 4) (step Z) ρ (planes Z) lE lB g ψ h

/-- **Strong-coupling gap on the four axes**, at finite volume. -/
theorem gap_ham {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) {lE lB : ℝ}
    (hE : 0 ≤ lE) (hB : 0 ≤ lB) (ψ : State (Site Z) (Fin 4) G) (h0 : ∑ U, ψ U = 0) :
    lE * nsq ψ ≤ (ip ψ (ham ρ (step Z) (planes Z) lE lB ψ)).re :=
  KogutSusskindGap.gap_ham ρ (step Z) (planes Z) hE hB ψ h0

end HopfYangMills
