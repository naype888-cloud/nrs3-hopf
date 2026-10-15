/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxNoState

/-!
# Robertson 1934 is strict on the box with the closed fiber in its band

On the box with any number of positions on `x`, `y`, `z` and the closed fiber with three
positions, take a unit state with the fiber in its band, `|⟨i[T°, P₃]⟩| > 1`.

Operators of different axes commute, so `Ω` is block diagonal for every state and
`|det Ω| = Π_i (t_i/2)²`, `t_i` the tension of axis `i`. If `det Ω ≠ 0`, at equality:

* the fiber has a positive defect (`ClosedAxisEntangled`), so the relations cross it in both
  directions (`RobertsonEqualityPlane`);
* the open axes have equal steps, `[P_d, [P_d, T_d]] = h² T_d` for every `d`, which no basis of
  the plane of `T°`, `P₃` satisfies (`EqualSteps`), so the algebra of the relations reaches the
  fiber alone and leaves no state (`BoxNoState`).

So equality never holds with `det Ω ≠ 0`. With `det Ω = 0` it holds only as `0 = 0`, when
`det Σ₈ = 0`, as for a position eigenstate on `x`. So in the band Robertson 1934 is strict exactly
when `det Σ₈ ≠ 0`, and always when `x`, `y`, `z` carry nonzero tensions, for every such state,
entangled with `x`, `y`, `z` or not.

## Main results

- `BoxStrict.abs_det_imMatrix_eq` : on `n` commuting axes, `|det Ω| = (Π_i t_i/2)²`.
- `BoxStrict.robertson_det_box_lt_of_det` : strict when `det Ω ≠ 0`.
- `BoxStrict.robertson_det_box_lt_iff` : in the band, strict exactly when `det Σ₈ ≠ 0`.
- `BoxStrict.robertson_det_box_lt` : strict when `x`, `y`, `z` carry nonzero tensions.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant FourAxes CubeInBox
open RobertsonDeterminant3D SpectralExtremal

namespace BoxStrict

/-! ## 1. `Ω` on commuting axes -/

section Generic

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {L : Fin 2 × Fin n → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (Φ : EuclideanSpace ℂ ι)

/-- **On commuting axes `|det Ω| = (Π_i t_i/2)²`**, for every state. -/
theorem abs_det_imMatrix_eq
    (hcomm : ∀ s t i j, i ≠ j → ∀ ψ, L (t, j) (L (s, i) ψ) = L (s, i) (L (t, j) ψ))
    (hsym : ∀ p, (L p).IsSymmetric) :
    |(imMatrix L Φ).det| = (∏ i, tensionG (L (0, i)) (L (1, i)) Φ / 2) ^ 2 := by
  set ω : Fin n → ℝ := fun i =>
    (inner ℂ (centeredG (L (0, i)) Φ) (centeredG (L (1, i)) Φ)).im
  have hblock : imMatrix L Φ = blockDiagonal fun i => !![0, ω i; -ω i, 0] := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [imMatrix, of_apply, blockDiagonal_apply]
    split_ifs with h
    · subst h
      fin_cases a <;> fin_cases b
      · simp [← Complex.ofReal_pow]
      · rfl
      · simpa [ω] using inner_im_swap _ _
      · simp [← Complex.ofReal_pow]
    · have hc : opCommutator (L (a, i)) (L (b, j)) = 0 := by
        ext1 ψ
        simp [opCommutator, hcomm a b i j h ψ]
      have hs := tensionG_eq (Φ := Φ) (hsym (a, i)) (hsym (b, j))
      simp only [tensionG, observableTension, hc, smul_zero, LinearMap.zero_apply,
        inner_zero_right, Complex.zero_re] at hs
      linarith
  have ht (i : Fin n) : tensionG (L (0, i)) (L (1, i)) Φ / 2 = -ω i := by
    rw [tensionG_eq (hsym _) (hsym _)]; ring
  have hdet (i : Fin n) : (!![0, ω i; -ω i, 0]).det =
      (tensionG (L (0, i)) (L (1, i)) Φ / 2) ^ 2 := by
    rw [det_fin_two_of, ht]; ring
  rw [hblock, det_blockDiagonal]
  simp only [hdet]
  rw [Finset.prod_pow, abs_of_nonneg (sq_nonneg _)]

end Generic

/-! ## 2. The box -/

variable {dx dy dz : ℕ}

/-- **With `det Ω ≠ 0`, Robertson 1934 is strict on the box with the closed fiber in its band.**
For every size of `x`, `y`, `z`, every unit state with `det Ω ≠ 0` and `|⟨i[T°, P₃]⟩| > 1` has
`|det Ω₈| < det Σ₈`. -/
theorem robertson_det_box_lt_of_det {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0) :
    |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det| <
      (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det := by
  exact (robertson_det _ Φ).lt_of_ne fun heq => BoxNoState.eq_zero_of_det_eq hΦ hb hΩ heq.symm

/-- **In the band, Robertson 1934 on the box is strict exactly when `det Σ₈ ≠ 0`**: the only
equality left is `0 = 0`. -/
theorem robertson_det_box_lt_iff {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|) :
    |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det| <
        (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ↔
      (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0 := by
  have hle := robertson_det (boxPairs dx dy dz 3 closedPair) Φ
  refine ⟨fun h => (lt_of_le_of_lt (abs_nonneg _) h).ne', fun hS => ?_⟩
  by_cases hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det = 0
  · rw [hΩ, abs_zero] at hle ⊢
    exact lt_of_le_of_ne hle (Ne.symm hS)
  · exact robertson_det_box_lt_of_det hΦ hb hΩ

/-- **Robertson 1934 is strict on the box with the closed fiber in its band**, whenever `x`, `y`,
`z` carry nonzero tensions: for every size of `x`, `y`, `z`, `|det Ω₈| < det Σ₈`. -/
theorem robertson_det_box_lt {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (ht : ∀ i : Fin 3, tensionG (boxPairs dx dy dz 3 closedPair (0, i.castSucc))
      (boxPairs dx dy dz 3 closedPair (1, i.castSucc)) Φ ≠ 0) :
    |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det| <
      (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det := by
  refine robertson_det_box_lt_of_det hΦ hb fun hΩ => ?_
  have h := abs_det_imMatrix_eq Φ
    (fun s t i j h ψ => BoxCommute.boxPairs_comm closedPair s t i j h ψ)
    BoxEverySize.boxPairs_isSymmetric
  rw [hΩ, abs_zero, eq_comm, Fin.prod_univ_four] at h
  have hw : tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hb; norm_num at hb
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1 h2
  exact (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (div_ne_zero h0 two_ne_zero)
    (div_ne_zero h1 two_ne_zero)) (div_ne_zero h2 two_ne_zero)) (div_ne_zero hw two_ne_zero))) h

end BoxStrict
