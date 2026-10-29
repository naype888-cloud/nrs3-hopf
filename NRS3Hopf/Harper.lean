/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Harper operator: a magnetic flux makes the step and the position not commute

On the ring of `N` positions `ZMod N` take the step `S` (one position forward) and the position
phase `Z_q = diag (e^{2πi q j / N})`, the phase of a flux `q/N` of the flux quantum per plaquette.
Both are unitary, and

  `Z_q S = e^{2πi q / N} S Z_q`.

So the flux is exactly the failure of `S` and `Z_q` to commute: with no flux they commute, with any
flux they do not, and the failure is the whole phase. The Harper operator
`H = S + S⋆ + Z_q + Z_q⋆` is the sum of the two Hermitian parts, the hopping along the ring and
the hopping of the dual ring; the Hofstadter butterfly is its spectrum as `q/N` varies.

## Main results

- `Harper.clock_mul_shift` : `Z_q S = e^{2πi q / N} S Z_q`.
- `Harper.commute_iff` : `S` and `Z_q` commute if and only if `q = 0` (no flux).
- `Harper.isHermitian_harper` : the Harper operator is Hermitian.
- `Harper.shift_mul_conjTranspose`, `Harper.clock_mul_conjTranspose` : `S` and `Z_q` are unitary.
-/

@[expose] public noncomputable section

open Matrix Complex ZMod

namespace Harper

variable {N : ℕ} [NeZero N]

/-- The step: `(S ψ) (i) = ψ (i - 1)`, one position forward. -/
def shift (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

/-- The position phase of a flux `q / N` per plaquette: `Z_q = diag (e^{2πi q j / N})`. -/
def clock (N : ℕ) [NeZero N] (q : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.diagonal fun j => stdAddChar (q * j)

/-- The Harper operator `S + S⋆ + Z_q + Z_q⋆`. -/
def harper (N : ℕ) [NeZero N] (q : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  shift N + (shift N)ᴴ + clock N q + (clock N q)ᴴ

/-- The phase of the flux `q / N`. -/
abbrev phase (q : ZMod N) : ℂ := stdAddChar q

lemma shift_apply (i j : ZMod N) : shift N i j = if i = j + 1 then 1 else 0 := rfl

lemma norm_stdAddChar (x : ZMod N) : ‖(stdAddChar x : ℂ)‖ = 1 := by
  rw [stdAddChar_apply]; exact Circle.norm_coe _

lemma conj_stdAddChar (x : ZMod N) : (starRingEnd ℂ) (stdAddChar x) = stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar x)]

/-- The Weyl relation: the flux is the failure of the step and the position phase to commute. -/
theorem clock_mul_shift (q : ZMod N) :
    clock N q * shift N = phase q • (shift N * clock N q) := by
  ext i j
  simp only [clock, shift, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j + 1
  · subst h
    simp [mul_add, AddChar.map_add_eq_mul, phase]
    ring
  · simp [h]

lemma shift_mul_conjTranspose : shift N * (shift N)ᴴ = 1 := by
  ext i j
  simp only [shift, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (i - 1)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro k _ hk
    have : ¬ i = k + 1 := fun h => hk (by rw [h]; simp)
    simp [this]
  · simp

lemma conjTranspose_shift_mul : (shift N)ᴴ * shift N = 1 := by
  ext i j
  simp only [shift, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (i + 1)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro k _ hk
    have : ¬ k = i + 1 := hk
    simp [this]
  · simp

lemma clock_mul_conjTranspose (q : ZMod N) : clock N q * (clock N q)ᴴ = 1 := by
  rw [clock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext j
  simp [conj_stdAddChar, ← AddChar.map_add_eq_mul]

lemma conjTranspose_clock_mul (q : ZMod N) : (clock N q)ᴴ * clock N q = 1 := by
  rw [clock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext j
  simp [conj_stdAddChar, ← AddChar.map_add_eq_mul]

/-- **The flux is the non-commutativity**: the step and the position phase of the flux `q / N`
commute if and only if there is no flux. -/
theorem commute_iff (q : ZMod N) : Commute (shift N) (clock N q) ↔ q = 0 := by
  constructor
  · intro h
    have h1 := clock_mul_shift q
    rw [← h.eq] at h1
    have h2 : (1 : Matrix (ZMod N) (ZMod N) ℂ) = phase q • 1 := by
      have := congrArg (fun m => (shift N)ᴴ * m * (clock N q)ᴴ) h1
      simp only [Matrix.mul_smul, Matrix.smul_mul] at this
      simpa only [conjTranspose_shift_mul, Matrix.one_mul, Matrix.mul_assoc,
        clock_mul_conjTranspose, Matrix.mul_one] using this
    have h3 := congrFun (congrFun h2 0) 0
    simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h3
    rw [phase, ← AddChar.map_zero_eq_one (stdAddChar (N := N))] at h3
    exact injective_stdAddChar h3.symm
  · rintro rfl
    have h1 := clock_mul_shift (0 : ZMod N)
    simp only [phase, AddChar.map_zero_eq_one, one_smul] at h1
    exact h1.symm

/-- The Harper operator is Hermitian. -/
theorem isHermitian_harper (q : ZMod N) : (harper N q).IsHermitian := by
  unfold harper Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  abel

end Harper
