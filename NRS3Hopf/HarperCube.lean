/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Harper
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Harper operator on the cube: one Weyl pair per axis

On `ℓ²(ZMod N × ZMod M × ZMod K)` take the step and the position phase of the axis `x` acting on
the first factor, those of `y` on the second and those of `z` on the third. Along one axis they
satisfy the Weyl relation with the flux of that axis; across axes everything commutes. The Harper
operator of the cube is the sum of the three axis operators.

So the non-commutativity of the cube is block diagonal, one `2 × 2` block per axis, as in the
six observables `(H, X)` of the open cube: the flux of an axis switches on exactly its own block.

## Main results

- `HarperCube.weyl_x`, `HarperCube.weyl_y`, `HarperCube.weyl_z` : the Weyl relation on each axis.
- `HarperCube.commute_xy`, `HarperCube.commute_xz`, `HarperCube.commute_yz` : different axes
  commute, operator by operator.
- `HarperCube.commute_x_iff`, `HarperCube.commute_y_iff`, `HarperCube.commute_z_iff` : the step and
  the phase of an axis commute if and only if the flux of that axis is zero.
- `HarperCube.isHermitian_harperCube` : the Harper operator of the cube is Hermitian.
- `HarperCube.harperCube_commute` : the axis operators commute with each other.
-/

@[expose] public noncomputable section

open Matrix Harper
open scoped Kronecker

namespace HarperCube

variable {N M K : ℕ} [NeZero N] [NeZero M] [NeZero K]

/-- An operator on the axis `x`: acts on the first factor. -/
def axisX (A : Matrix (ZMod N) (ZMod N) ℂ) :
    Matrix (ZMod N × ZMod M × ZMod K) (ZMod N × ZMod M × ZMod K) ℂ :=
  A ⊗ₖ (1 : Matrix (ZMod M × ZMod K) (ZMod M × ZMod K) ℂ)

/-- An operator on the axis `y`: acts on the second factor. -/
def axisY (B : Matrix (ZMod M) (ZMod M) ℂ) :
    Matrix (ZMod N × ZMod M × ZMod K) (ZMod N × ZMod M × ZMod K) ℂ :=
  (1 : Matrix (ZMod N) (ZMod N) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix (ZMod K) (ZMod K) ℂ))

/-- An operator on the axis `z`: acts on the third factor. -/
def axisZ (C : Matrix (ZMod K) (ZMod K) ℂ) :
    Matrix (ZMod N × ZMod M × ZMod K) (ZMod N × ZMod M × ZMod K) ℂ :=
  (1 : Matrix (ZMod N) (ZMod N) ℂ) ⊗ₖ ((1 : Matrix (ZMod M) (ZMod M) ℂ) ⊗ₖ C)

lemma axisX_mul (A A' : Matrix (ZMod N) (ZMod N) ℂ) :
    axisX (M := M) (K := K) A * axisX A' = axisX (A * A') := by
  simp [axisX, ← Matrix.mul_kronecker_mul]

lemma axisY_mul (B B' : Matrix (ZMod M) (ZMod M) ℂ) :
    axisY (N := N) (K := K) B * axisY B' = axisY (B * B') := by
  simp [axisY, ← Matrix.mul_kronecker_mul]

lemma axisZ_mul (C C' : Matrix (ZMod K) (ZMod K) ℂ) :
    axisZ (N := N) (M := M) C * axisZ C' = axisZ (C * C') := by
  simp [axisZ, ← Matrix.mul_kronecker_mul]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisX_smul (c : ℂ) (A : Matrix (ZMod N) (ZMod N) ℂ) :
    axisX (M := M) (K := K) (c • A) = c • axisX A := by
  simp [axisX, Matrix.smul_kronecker]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisY_smul (c : ℂ) (B : Matrix (ZMod M) (ZMod M) ℂ) :
    axisY (N := N) (K := K) (c • B) = c • axisY B := by
  simp [axisY, Matrix.smul_kronecker, Matrix.kronecker_smul]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisZ_smul (c : ℂ) (C : Matrix (ZMod K) (ZMod K) ℂ) :
    axisZ (N := N) (M := M) (c • C) = c • axisZ C := by
  simp [axisZ, Matrix.kronecker_smul]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisX_injective : Function.Injective (axisX (N := N) (M := M) (K := K)) := by
  intro A A' h
  ext i j
  have := congrFun (congrFun h (i, 0, 0)) (j, 0, 0)
  simpa [axisX, Matrix.kroneckerMap_apply] using this

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisY_injective : Function.Injective (axisY (N := N) (M := M) (K := K)) := by
  intro B B' h
  ext i j
  have := congrFun (congrFun h (0, i, 0)) (0, j, 0)
  simpa [axisY, Matrix.kroneckerMap_apply] using this

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisZ_injective : Function.Injective (axisZ (N := N) (M := M) (K := K)) := by
  intro C C' h
  ext i j
  have := congrFun (congrFun h (0, 0, i)) (0, 0, j)
  simpa [axisZ, Matrix.kroneckerMap_apply] using this

/-- The Weyl relation on the axis `x`, with the flux `q / N`. -/
theorem weyl_x (q : ZMod N) :
    axisX (M := M) (K := K) (clock N q) * axisX (shift N) =
      phase q • (axisX (shift N) * axisX (clock N q)) := by
  rw [axisX_mul, axisX_mul, clock_mul_shift, axisX_smul]

/-- The Weyl relation on the axis `y`, with the flux `r / M`. -/
theorem weyl_y (r : ZMod M) :
    axisY (N := N) (K := K) (clock M r) * axisY (shift M) =
      phase r • (axisY (shift M) * axisY (clock M r)) := by
  rw [axisY_mul, axisY_mul, clock_mul_shift, axisY_smul]

/-- The Weyl relation on the axis `z`, with the flux `s / K`. -/
theorem weyl_z (s : ZMod K) :
    axisZ (N := N) (M := M) (clock K s) * axisZ (shift K) =
      phase s • (axisZ (shift K) * axisZ (clock K s)) := by
  rw [axisZ_mul, axisZ_mul, clock_mul_shift, axisZ_smul]

/-- Operators of the axes `x` and `y` commute. -/
theorem commute_xy (A : Matrix (ZMod N) (ZMod N) ℂ) (B : Matrix (ZMod M) (ZMod M) ℂ) :
    Commute (axisX (M := M) (K := K) A) (axisY B) := by
  show axisX A * axisY B = axisY B * axisX A
  simp [axisX, axisY, ← Matrix.mul_kronecker_mul]

/-- Operators of the axes `x` and `z` commute. -/
theorem commute_xz (A : Matrix (ZMod N) (ZMod N) ℂ) (C : Matrix (ZMod K) (ZMod K) ℂ) :
    Commute (axisX (M := M) (K := K) A) (axisZ C) := by
  show axisX A * axisZ C = axisZ C * axisX A
  simp [axisX, axisZ, ← Matrix.mul_kronecker_mul]

/-- Operators of the axes `y` and `z` commute. -/
theorem commute_yz (B : Matrix (ZMod M) (ZMod M) ℂ) (C : Matrix (ZMod K) (ZMod K) ℂ) :
    Commute (axisY (N := N) (K := K) B) (axisZ C) := by
  show axisY B * axisZ C = axisZ C * axisY B
  simp [axisY, axisZ, ← Matrix.mul_kronecker_mul]

/-- The step and the phase of the axis `x` commute if and only if its flux is zero. -/
theorem commute_x_iff (q : ZMod N) :
    Commute (axisX (M := M) (K := K) (shift N)) (axisX (clock N q)) ↔ q = 0 := by
  rw [← commute_iff]
  constructor
  · intro h
    exact axisX_injective (by simpa [axisX_mul] using h.eq)
  · intro h
    show axisX _ * axisX _ = axisX _ * axisX _
    rw [axisX_mul, axisX_mul, h.eq]

/-- The step and the phase of the axis `y` commute if and only if its flux is zero. -/
theorem commute_y_iff (r : ZMod M) :
    Commute (axisY (N := N) (K := K) (shift M)) (axisY (clock M r)) ↔ r = 0 := by
  rw [← commute_iff]
  constructor
  · intro h
    exact axisY_injective (by simpa [axisY_mul] using h.eq)
  · intro h
    show axisY _ * axisY _ = axisY _ * axisY _
    rw [axisY_mul, axisY_mul, h.eq]

/-- The step and the phase of the axis `z` commute if and only if its flux is zero. -/
theorem commute_z_iff (s : ZMod K) :
    Commute (axisZ (N := N) (M := M) (shift K)) (axisZ (clock K s)) ↔ s = 0 := by
  rw [← commute_iff]
  constructor
  · intro h
    exact axisZ_injective (by simpa [axisZ_mul] using h.eq)
  · intro h
    show axisZ _ * axisZ _ = axisZ _ * axisZ _
    rw [axisZ_mul, axisZ_mul, h.eq]

/-- The Harper operator of the cube: the Harper operator of each axis, with its own flux. -/
def harperCube (N M K : ℕ) [NeZero N] [NeZero M] [NeZero K] (q : ZMod N) (r : ZMod M)
    (s : ZMod K) : Matrix (ZMod N × ZMod M × ZMod K) (ZMod N × ZMod M × ZMod K) ℂ :=
  axisX (harper N q) + axisY (harper M r) + axisZ (harper K s)

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisX_conjTranspose (A : Matrix (ZMod N) (ZMod N) ℂ) :
    (axisX (M := M) (K := K) A)ᴴ = axisX Aᴴ := by
  simp [axisX, Matrix.conjTranspose_kronecker]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisY_conjTranspose (B : Matrix (ZMod M) (ZMod M) ℂ) :
    (axisY (N := N) (K := K) B)ᴴ = axisY Bᴴ := by
  simp [axisY, Matrix.conjTranspose_kronecker]

omit [NeZero N] [NeZero M] [NeZero K] in
lemma axisZ_conjTranspose (C : Matrix (ZMod K) (ZMod K) ℂ) :
    (axisZ (N := N) (M := M) C)ᴴ = axisZ Cᴴ := by
  simp [axisZ, Matrix.conjTranspose_kronecker]

/-- The Harper operator of the cube is Hermitian. -/
theorem isHermitian_harperCube (q : ZMod N) (r : ZMod M) (s : ZMod K) :
    (harperCube N M K q r s).IsHermitian := by
  unfold harperCube Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, axisX_conjTranspose,
    axisY_conjTranspose, axisZ_conjTranspose, (isHermitian_harper q).eq,
    (isHermitian_harper r).eq, (isHermitian_harper s).eq]

/-- The three axis operators commute pairwise, so `H = Hₓ + H_y + H_z` is a sum of commuting
Hermitian operators. -/
theorem harperCube_commute (q : ZMod N) (r : ZMod M) (s : ZMod K) :
    Commute (axisX (M := M) (K := K) (harper N q)) (axisY (harper M r)) ∧
    Commute (axisX (M := M) (K := K) (harper N q)) (axisZ (harper K s)) ∧
    Commute (axisY (N := N) (K := K) (harper M r)) (axisZ (harper K s)) :=
  ⟨commute_xy _ _, commute_xz _ _, commute_yz _ _⟩

end HarperCube
