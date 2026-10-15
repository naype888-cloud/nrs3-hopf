/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.FourAxes
public import NRS3Hopf.ClosedThreeBand

/-!
# The cube inside the box of four axes

The six observables of `x`, `y`, `z` inside the box of four axes, with any pair on the fourth
axis `w`. On a product state `u ⊗ v ⊗ w ⊗ s`:

* the `6 × 6` matrices `Σ` and `Ω` of `x`, `y`, `z` are those of the cube at `u ⊗ v ⊗ w`: the
  three axes see the cube, whatever the fourth axis carries;
* the determinants factor, `det Σ₈ = det Σ₆ · det Σ_w` and `|det Ω₈| = |det Ω₆| · |det Ω_w|`, so
  the fourth axis multiplies the Robertson ratio by its own ratio, never below `1`.

With the fourth axis closed with three positions (`ClosedThree`) and its state in the band, its
factor is strictly above `1`: Robertson 1934 is strict on the whole box as soon as the cube has
`det Σ₆ > 0`, even when the cube itself saturates. At `3 × 3 × 3` the maximal current state of
the cube saturates (`D49c`, `C_Nava(3) = 1`); with a closed fourth axis in its band the box is
strict.

## Main results

- `CubeInBox.covMatrix_xyz`, `CubeInBox.imMatrix_xyz` : the `x`, `y`, `z` part of the box is
  the cube.
- `CubeInBox.det_covMatrix_box`, `CubeInBox.abs_det_imMatrix_box` : the determinants factor.
- `CubeInBox.robertson_det_box_strict` : a closed fourth axis in its band makes the box strict.
- `CubeInBox.cube_saturates_box_strict` : the `3 × 3 × 3` cube saturates at its maximal current
  state, and the box with a closed fourth axis in its band is strict.
-/

@[expose] public noncomputable section

open Matrix TransportPosition SpectralExtremal NearMaxTension PathGraph3DNRS
open RobertsonDeterminant RobertsonDeterminant3D RobertsonDeterminantProduct CubeSpectrum
open CubePythagoras FourAxes NRSInequality EigenvectorSaturation

namespace CubeInBox

variable {dx dy dz dw : ℕ}

/-- The six observables of `x`, `y`, `z` among the eight of the box. -/
def xyz (p : Fin 2 × Fin 3) : Fin 2 × Fin 4 := (p.1, p.2.castSucc)

section Cube

variable {u : Hd dx} {v : Hd dy} {w : Hd dz}
  (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
include hu hv hw

/-- The centered vectors of the cube at a product state, axis by axis. -/
theorem inner_centered_cube (a b : Fin 2) (i j : Fin 3) :
    inner ℂ (centeredG (pairs dx dy dz (a, i)) (prod3 u v w))
        (centeredG (pairs dx dy dz (b, j)) (prod3 u v w)) =
      if i = j then
        ![inner ℂ (centeredG (pair dx a) u) (centeredG (pair dx b) u),
          inner ℂ (centeredG (pair dy a) v) (centeredG (pair dy b) v),
          inner ℂ (centeredG (pair dz a) w) (centeredG (pair dz b) w)] i
      else 0 := by
  have ul a := inner_self_centeredG (pair_isSymmetric dx a) hu
  have ur a := inner_centeredG_self (pair_isSymmetric dx a) hu
  have vl a := inner_self_centeredG (pair_isSymmetric dy a) hv
  have vr a := inner_centeredG_self (pair_isSymmetric dy a) hv
  have wl a := inner_self_centeredG (pair_isSymmetric dz a) hw
  have wr a := inner_centeredG_self (pair_isSymmetric dz a) hw
  fin_cases i <;> fin_cases j <;>
    simp [centered_pairs_x hv hw, centered_pairs_y hu hw, centered_pairs_z hu hv, inner_prod3,
      ul, ur, vl, vr, wl, wr, hu, hv, hw]

theorem imMatrix_prod3 :
    imMatrix (pairs dx dy dz) (prod3 u v w) =
      blockDiagonal ![imMatrix (pair dx) u, imMatrix (pair dy) v, imMatrix (pair dz) w] := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [imMatrix, of_apply, blockDiagonal_apply, inner_centered_cube hu hv hw]
  split_ifs with h
  · subst h; fin_cases i <;> rfl
  · rfl

variable {s : Hd dw} (hs : ‖s‖ = 1) {M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ}
  (hM : ∀ a, (M a).IsHermitian)
include hs hM

/-- **The `x`, `y`, `z` part of `Σ` is the cube**, whatever the fourth axis carries. -/
theorem covMatrix_xyz :
    covMatrix (fun p => boxPairs dx dy dz dw M (xyz p)) (prod4 u v w s) =
      covMatrix (pairs dx dy dz) (prod3 u v w) := by
  change (covMatrix (boxPairs dx dy dz dw M) (prod4 u v w s)).submatrix xyz xyz = _
  rw [covMatrix_box hu hv hw hs hM, covMatrix_prod3 hu hv hw]
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases i <;> fin_cases j <;> simp [blockDiagonal_apply, xyz]

/-- **The `x`, `y`, `z` part of `Ω` is the cube.** -/
theorem imMatrix_xyz :
    imMatrix (fun p => boxPairs dx dy dz dw M (xyz p)) (prod4 u v w s) =
      imMatrix (pairs dx dy dz) (prod3 u v w) := by
  change (imMatrix (boxPairs dx dy dz dw M) (prod4 u v w s)).submatrix xyz xyz = _
  rw [imMatrix_box hu hv hw hs hM, imMatrix_prod3 hu hv hw]
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases i <;> fin_cases j <;> simp [blockDiagonal_apply, xyz]

/-- **`det Σ₈ = det Σ₆ · det Σ_w`.** -/
theorem det_covMatrix_box :
    (covMatrix (boxPairs dx dy dz dw M) (prod4 u v w s)).det =
      (covMatrix (pairs dx dy dz) (prod3 u v w)).det * (covMatrix (wPair M) s).det := by
  rw [covMatrix_box hu hv hw hs hM, covMatrix_prod3 hu hv hw, det_blockDiagonal,
    det_blockDiagonal, Fin.prod_univ_four, Fin.prod_univ_three]
  rfl

/-- **`|det Ω₈| = |det Ω₆| · |det Ω_w|`.** -/
theorem abs_det_imMatrix_box :
    |(imMatrix (boxPairs dx dy dz dw M) (prod4 u v w s)).det| =
      |(imMatrix (pairs dx dy dz) (prod3 u v w)).det| * |(imMatrix (wPair M) s).det| := by
  rw [imMatrix_box hu hv hw hs hM, imMatrix_prod3 hu hv hw, det_blockDiagonal,
    det_blockDiagonal, Fin.prod_univ_four, Fin.prod_univ_three, ← abs_mul]
  rfl

end Cube

/-! ## A closed fourth axis -/

/-- The closed axis with three positions as the pair of the fourth axis. -/
def closedPair : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ := ![ClosedThree.Tc, Pd 3]

theorem closedPair_isHermitian : ∀ a, (closedPair a).IsHermitian := by
  intro a; fin_cases a
  exacts [ClosedThree.Tc_isHermitian, Pd_isHermitian 3]

theorem det_covMatrix_closed (ψ : Hd 3) :
    (covMatrix (wPair closedPair) ψ).det =
      gramDefectAt ClosedThree.TcOp (PdOp 3) ψ + imPart ClosedThree.TcOp (PdOp 3) ψ ^ 2 := by
  rw [det_fin_two, gramDefectAt_eq_gap]
  simp only [covMatrix, of_apply, covarianceG]
  have hsw : (inner ℂ (centeredG (wPair closedPair 1) ψ) (centeredG (wPair closedPair 0) ψ)).re
      = (inner ℂ (centeredG (wPair closedPair 0) ψ) (centeredG (wPair closedPair 1) ψ)).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  rw [hsw]
  have e0 : centeredG (wPair closedPair 0) ψ = centered ClosedThree.TcOp ψ := rfl
  have e1 : centeredG (wPair closedPair 1) ψ = centered (PdOp 3) ψ := rfl
  have hn (x : Hd 3) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [e0, e1, hn, hn]
  unfold variance covariance
  ring

theorem abs_det_imMatrix_closed (ψ : Hd 3) :
    |(imMatrix (wPair closedPair) ψ).det| = imPart ClosedThree.TcOp (PdOp 3) ψ ^ 2 := by
  have e0 : centeredG (wPair closedPair 0) ψ = centered ClosedThree.TcOp ψ := rfl
  have e1 : centeredG (wPair closedPair 1) ψ = centered (PdOp 3) ψ := rfl
  have h0 (x : Hd 3) : (inner ℂ x x).im = 0 := by simpa using inner_self_im (𝕜 := ℂ) x
  rw [det_fin_two]
  simp only [imMatrix, of_apply, e0, e1, h0, imPart]
  rw [inner_im_swap]
  have key (x : ℝ) : |0 * 0 - -x * x| = (-x) ^ 2 := by
    rw [show (0 : ℝ) * 0 - -x * x = (-x) ^ 2 by ring]
    exact abs_of_nonneg (sq_nonneg _)
  exact key _

/-- **A closed fourth axis in its band makes Robertson strict on the whole box**, as soon as the
cube has `det Σ₆ > 0`. -/
theorem robertson_det_box_strict {u : Hd dx} {v : Hd dy} {w : Hd dz} {s : Hd 3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hs : ‖s‖ = 1)
    (hband : 1 < |ClosedThree.tension s|)
    (hcube : 0 < (covMatrix (pairs dx dy dz) (prod3 u v w)).det) :
    |(imMatrix (boxPairs dx dy dz 3 closedPair) (prod4 u v w s)).det| <
      (covMatrix (boxPairs dx dy dz 3 closedPair) (prod4 u v w s)).det := by
  rw [abs_det_imMatrix_box hu hv hw hs closedPair_isHermitian,
    det_covMatrix_box hu hv hw hs closedPair_isHermitian, abs_det_imMatrix_closed,
    det_covMatrix_closed]
  have h6 := robertson_det (pairs dx dy dz) (prod3 u v w)
  have hg := ClosedThree.surplus_pos_of_one_lt hs hband
  have hi := sq_nonneg (imPart ClosedThree.TcOp (PdOp 3) s)
  have ha := abs_nonneg (imMatrix (pairs dx dy dz) (prod3 u v w)).det
  calc |(imMatrix (pairs dx dy dz) (prod3 u v w)).det| * imPart ClosedThree.TcOp (PdOp 3) s ^ 2
      ≤ (covMatrix (pairs dx dy dz) (prod3 u v w)).det *
          imPart ClosedThree.TcOp (PdOp 3) s ^ 2 := mul_le_mul_of_nonneg_right h6 hi
    _ < _ := mul_lt_mul_of_pos_left (by linarith) hcube

/-- The `3 × 3 × 3` cube at its maximal current state: `det Σ₆ = |det Ω₆| = (1/8)²`. -/
theorem cube_three_saturates :
    (covMatrix (pairs 3 3 3) (maxCurrentCubeState 3 3 3)).det =
        |(imMatrix (pairs 3 3 3) (maxCurrentCubeState 3 3 3)).det| ∧
      0 < (covMatrix (pairs 3 3 3) (maxCurrentCubeState 3 3 3)).det := by
  have hC : Gnomon.CoherenceConstant 3 = 1 :=
    (Gnomon.CoherenceConstant_eq_one_iff 3 (by norm_num)).mpr (Or.inr rfl)
  have hΦ := maxCurrentCubeState_eq_prod3 (dx := 3) (dy := 3) (dz := 3)
  have hu := norm_maxCurrentState (d := 3) (by norm_num)
  obtain ⟨tx, ty, tz⟩ := tensions_prod3 hu hu hu
  have ht := tension_maxCurrentState (d := 3) (by norm_num)
  have hdet := det_covMatrix_maxCurrentCubeState (dx := 3) (dy := 3) (dz := 3) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hC, hΦ, tx, ty, tz, ht] at hdet
  have hom (i : Fin 3) : tensionG (pairs 3 3 3 (0, i)) (pairs 3 3 3 (1, i))
      (maxCurrentCubeState 3 3 3) = -2 * omega (maxCurrentCubeState 3 3 3) i :=
    tensionG_eq (pairs_isSymmetric 3 3 3 _) (pairs_isSymmetric 3 3 3 _)
  have h0 := hom 0
  have h1 := hom 1
  have h2 := hom 2
  rw [show pairs 3 3 3 (0, 0) = TX 3 3 3 from rfl, show pairs 3 3 3 (1, 0) = PX 3 3 3 from rfl,
    hΦ, tx, ht] at h0
  rw [show pairs 3 3 3 (0, 1) = TY 3 3 3 from rfl, show pairs 3 3 3 (1, 1) = PY 3 3 3 from rfl,
    hΦ, ty, ht] at h1
  rw [show pairs 3 3 3 (0, 2) = TZ 3 3 3 from rfl, show pairs 3 3 3 (1, 2) = PZ 3 3 3 from rfl,
    hΦ, tz, ht] at h2
  rw [hΦ, hdet, abs_det_imMatrix_pairs]
  have e : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  rw [e] at h0 h1 h2
  rw [e]
  have o0 : omega (prod3 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)) 0 =
    -1 / 2 := by linarith
  have o1 : omega (prod3 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)) 1 =
    -1 / 2 := by linarith
  have o2 : omega (prod3 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)) 2 =
    -1 / 2 := by linarith
  rw [o0, o1, o2]
  norm_num

/-- **The cube saturates, the box does not.** With the `3 × 3 × 3` cube at its maximal current
state, which saturates Robertson, and the closed fourth axis at its own maximal current state,
Robertson 1934 is strict on the box of four axes. -/
theorem cube_saturates_box_strict :
    |(imMatrix (boxPairs 3 3 3 3 closedPair)
        (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
          ClosedThree.maxState)).det| <
      (covMatrix (boxPairs 3 3 3 3 closedPair)
        (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
          ClosedThree.maxState)).det := by
  have hu := norm_maxCurrentState (d := 3) (by norm_num)
  refine robertson_det_box_strict hu hu hu ClosedThree.norm_maxState ?_ ?_
  · rw [ClosedThree.tension_maxState, abs_of_pos (by positivity)]
    have : (2 : ℝ) < √6 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  · exact (maxCurrentCubeState_eq_prod3 (dx := 3) (dy := 3) (dz := 3)) ▸ cube_three_saturates.2

end CubeInBox
