/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.HarperCube
public import NRS3Hopf.HarperRobertson

/-!
# Robertson 1934 for the Harper observables of the cube: the flux of each axis switches on its block

The six Hermitian observables of the cube, the hopping `S + S⋆` and the phase `Z_q + Z_q⋆` of each
axis `x`, `y`, `z`, are a finite family of observables on `ℓ²(ZMod N × ZMod M × ZMod K)`.
Robertson's relation `|det Ω| ≤ det Σ` holds for them in every state.

Observables of different axes commute, so the entries of `Ω` across axes vanish **in every state**,
not only in product states: `Ω` is block diagonal, one `2 × 2` block per axis, as for the six
observables `(H, X)` of the open cube. If the flux of an axis is zero its step and its phase
commute, so its block vanishes; and with a flux there is a state in which the block does not.

## Main results

- `HarperCubeRobertson.robertson_det_harperCube` : `|det Ω| ≤ det Σ` for the six observables.
- `HarperCubeRobertson.imMatrix_cross` : `Ω` vanishes across axes, in every state.
- `HarperCubeRobertson.imMatrix_x_eq_zero`, `HarperCubeRobertson.imMatrix_y_eq_zero`,
  `HarperCubeRobertson.imMatrix_z_eq_zero` : with no flux on an axis, the block of that axis
  vanishes in every state.
- `HarperCubeRobertson.exists_imMatrix_x_ne_zero` (and `y`, `z`) : with a flux, there is a state in
  which the block of that axis does not vanish: the flux switches on exactly its own block.
-/

@[expose] public noncomputable section

open Matrix Harper HarperCube HarperRobertson RobertsonDeterminant PathGraph3DNRS SpectralExtremal

namespace HarperCubeRobertson

variable {N M K : ℕ} [NeZero N] [NeZero M] [NeZero K]

/-- The six Harper observables of the cube: hopping and phase of the axes `x`, `y`, `z`. -/
def obsMat (N M K : ℕ) [NeZero N] [NeZero M] [NeZero K] (q : ZMod N) (r : ZMod M) (s : ZMod K) :
    Fin 6 → Matrix (ZMod N × ZMod M × ZMod K) (ZMod N × ZMod M × ZMod K) ℂ :=
  ![axisX (hop N), axisX (phaseObs N q), axisY (hop M), axisY (phaseObs M r),
    axisZ (hop K), axisZ (phaseObs K s)]

/-- The six Harper observables as operators of the Hilbert space. -/
def obs (N M K : ℕ) [NeZero N] [NeZero M] [NeZero K] (q : ZMod N) (r : ZMod M) (s : ZMod K)
    (j : Fin 6) : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K) →ₗ[ℂ]
      EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K) :=
  Matrix.toEuclideanLin (obsMat N M K q r s j)

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisX_isHermitian {A : Matrix (ZMod N) (ZMod N) ℂ} (h : A.IsHermitian) :
    (axisX (M := M) (K := K) A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [axisX_conjTranspose, h.eq]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisY_isHermitian {B : Matrix (ZMod M) (ZMod M) ℂ} (h : B.IsHermitian) :
    (axisY (N := N) (K := K) B).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [axisY_conjTranspose, h.eq]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisZ_isHermitian {C : Matrix (ZMod K) (ZMod K) ℂ} (h : C.IsHermitian) :
    (axisZ (N := N) (M := M) C).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [axisZ_conjTranspose, h.eq]

lemma obsMat_isHermitian (q : ZMod N) (r : ZMod M) (s : ZMod K) (j : Fin 6) :
    (obsMat N M K q r s j).IsHermitian := by
  fin_cases j
  · exact axisX_isHermitian hop_isHermitian
  · exact axisX_isHermitian (phaseObs_isHermitian q)
  · exact axisY_isHermitian hop_isHermitian
  · exact axisY_isHermitian (phaseObs_isHermitian r)
  · exact axisZ_isHermitian hop_isHermitian
  · exact axisZ_isHermitian (phaseObs_isHermitian s)

lemma obs_isSymmetric (q : ZMod N) (r : ZMod M) (s : ZMod K) (j : Fin 6) :
    (obs N M K q r s j).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (obsMat_isHermitian q r s j)

/-- **Robertson 1934 for the six Harper observables of the cube**, in every state. -/
theorem robertson_det_harperCube (q : ZMod N) (r : ZMod M) (s : ZMod K)
    (Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K)) :
    |(imMatrix (obs N M K q r s) Φ).det| ≤ (covMatrix (obs N M K q r s) Φ).det :=
  robertson_det _ Φ

/-- Each of the six observables acts on one axis. -/
lemma obsMat_axis (q : ZMod N) (r : ZMod M) (s : ZMod K) (j : Fin 6) :
    (j.val / 2 = 0 ∧ ∃ A, obsMat N M K q r s j = axisX A) ∨
    (j.val / 2 = 1 ∧ ∃ B, obsMat N M K q r s j = axisY B) ∨
    (j.val / 2 = 2 ∧ ∃ C, obsMat N M K q r s j = axisZ C) := by
  fin_cases j
  · exact Or.inl ⟨rfl, _, rfl⟩
  · exact Or.inl ⟨rfl, _, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, _, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, _, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)

/-- Observables of different axes commute. -/
lemma obsMat_commute_of_ne (q : ZMod N) (r : ZMod M) (s : ZMod K) {j k : Fin 6}
    (h : j.val / 2 ≠ k.val / 2) :
    obsMat N M K q r s j * obsMat N M K q r s k = obsMat N M K q r s k * obsMat N M K q r s j := by
  rcases obsMat_axis q r s j with ⟨hj, A, hA⟩ | ⟨hj, A, hA⟩ | ⟨hj, A, hA⟩ <;>
    rcases obsMat_axis q r s k with ⟨hk, B, hB⟩ | ⟨hk, B, hB⟩ | ⟨hk, B, hB⟩ <;>
    rw [hA, hB]
  · exact absurd (hj.trans hk.symm) h
  · exact (commute_xy A B).eq
  · exact (commute_xz A B).eq
  · exact (commute_xy B A).symm.eq
  · exact absurd (hj.trans hk.symm) h
  · exact (commute_yz A B).eq
  · exact (commute_xz B A).symm.eq
  · exact (commute_yz B A).symm.eq
  · exact absurd (hj.trans hk.symm) h

/-- **`Ω` is block diagonal in every state**: observables of different axes have no entry. -/
theorem imMatrix_cross (q : ZMod N) (r : ZMod M) (s : ZMod K)
    (Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K)) {j k : Fin 6}
    (h : j.val / 2 ≠ k.val / 2) : imMatrix (obs N M K q r s) Φ j k = 0 :=
  imMatrix_entry_eq_zero (obs_isSymmetric q r s j) (obs_isSymmetric q r s k)
    (toEuclideanLin_comp_eq _ _ (obsMat_commute_of_ne q r s h)) Φ

/-- With no flux on the axis `x`, its block of `Ω` vanishes in every state. -/
theorem imMatrix_x_eq_zero (r : ZMod M) (s : ZMod K)
    (Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K)) :
    imMatrix (obs N M K 0 r s) Φ 0 1 = 0 := by
  have hc : obsMat N M K 0 r s 0 * obsMat N M K 0 r s 1 =
      obsMat N M K 0 r s 1 * obsMat N M K 0 r s 0 := by
    simp only [obsMat, Matrix.cons_val_zero, Matrix.cons_val_one, axisX_mul]
    rw [hop_commute_phaseObs_zero]
  exact imMatrix_entry_eq_zero (obs_isSymmetric 0 r s 0) (obs_isSymmetric 0 r s 1)
    (toEuclideanLin_comp_eq _ _ hc) Φ

/-- With no flux on the axis `y`, its block of `Ω` vanishes in every state. -/
theorem imMatrix_y_eq_zero (q : ZMod N) (s : ZMod K)
    (Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K)) :
    imMatrix (obs N M K q 0 s) Φ 2 3 = 0 := by
  have hc : obsMat N M K q 0 s 2 * obsMat N M K q 0 s 3 =
      obsMat N M K q 0 s 3 * obsMat N M K q 0 s 2 := by
    simp only [obsMat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, axisY_mul]
    rw [hop_commute_phaseObs_zero]
  exact imMatrix_entry_eq_zero (obs_isSymmetric q 0 s 2) (obs_isSymmetric q 0 s 3)
    (toEuclideanLin_comp_eq _ _ hc) Φ

/-- With no flux on the axis `z`, its block of `Ω` vanishes in every state. -/
theorem imMatrix_z_eq_zero (q : ZMod N) (r : ZMod M)
    (Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K)) :
    imMatrix (obs N M K q r 0) Φ 4 5 = 0 := by
  have hc : obsMat N M K q r 0 4 * obsMat N M K q r 0 5 =
      obsMat N M K q r 0 5 * obsMat N M K q r 0 4 := by
    have h4 : obsMat N M K q r 0 4 = axisZ (hop K) := rfl
    have h5 : obsMat N M K q r 0 5 = axisZ (phaseObs K 0) := rfl
    rw [h4, h5, axisZ_mul, axisZ_mul, hop_commute_phaseObs_zero]
  exact imMatrix_entry_eq_zero (obs_isSymmetric q r 0 4) (obs_isSymmetric q r 0 5)
    (toEuclideanLin_comp_eq _ _ hc) Φ

/-- If two of the observables do not commute, there is a state in which their entry of `Ω` does
not vanish. -/
lemma exists_imMatrix_ne_zero (q : ZMod N) (r : ZMod M) (s : ZMod K) {j k : Fin 6}
    (hne : obsMat N M K q r s j * obsMat N M K q r s k ≠
      obsMat N M K q r s k * obsMat N M K q r s j) :
    ∃ Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K), imMatrix (obs N M K q r s) Φ j k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hc := eq_zero_of_tensionG_eq_zero (obs_isSymmetric q r s j) (obs_isSymmetric q r s k)
    (fun Φ => hcon Φ)
  apply hne
  have : (Matrix.toEuclideanLin (obsMat N M K q r s j * obsMat N M K q r s k)) =
      (Matrix.toEuclideanLin (obsMat N M K q r s k * obsMat N M K q r s j)) := by
    ext v i
    have := LinearMap.congr_fun hc v
    simpa [obs, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun w => w.ofLp i) this
  exact Matrix.toEuclideanLin.injective this

/-- **The flux switches the block on**: with a flux on the axis `x`, there is a state in which its
entry of `Ω` does not vanish. -/
theorem exists_imMatrix_x_ne_zero {q : ZMod N} (hq : q ≠ 0) (r : ZMod M) (s : ZMod K) :
    ∃ Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K),
      imMatrix (obs N M K q r s) Φ 0 1 ≠ 0 := by
  refine exists_imMatrix_ne_zero q r s fun h => hop_phaseObs_not_commute hq ?_
  apply axisX_injective (M := M) (K := K)
  simpa [obsMat, axisX_mul] using h

/-- **The flux switches the block on**: with a flux on the axis `y`, there is a state in which its
entry of `Ω` does not vanish. -/
theorem exists_imMatrix_y_ne_zero (q : ZMod N) {r : ZMod M} (hr : r ≠ 0) (s : ZMod K) :
    ∃ Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K),
      imMatrix (obs N M K q r s) Φ 2 3 ≠ 0 := by
  refine exists_imMatrix_ne_zero q r s fun h => hop_phaseObs_not_commute hr ?_
  apply axisY_injective (N := N) (K := K)
  simpa [obsMat, axisY_mul] using h

/-- **The flux switches the block on**: with a flux on the axis `z`, there is a state in which its
entry of `Ω` does not vanish. -/
theorem exists_imMatrix_z_ne_zero (q : ZMod N) (r : ZMod M) {s : ZMod K} (hs : s ≠ 0) :
    ∃ Φ : EuclideanSpace ℂ (ZMod N × ZMod M × ZMod K),
      imMatrix (obs N M K q r s) Φ 4 5 ≠ 0 := by
  refine exists_imMatrix_ne_zero q r s fun h => hop_phaseObs_not_commute hs ?_
  apply axisZ_injective (N := N) (M := M)
  simpa [obsMat, axisZ_mul] using h

end HarperCubeRobertson
