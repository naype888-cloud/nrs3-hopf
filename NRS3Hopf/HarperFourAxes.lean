/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Harper
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Harper operator on four axes: two Weyl planes

On `ℓ²(ZMod N × ZMod M)` take the step and the position phase of the plane `(x, y)` acting on the
first factor and those of the plane `(z, w)` acting on the second. Within a plane they satisfy the
Weyl relation with the flux of that plane; across planes everything commutes. The four-axis Harper
operator is the sum of the two plane operators.

So the non-commutativity of the four axes is block diagonal, one `2 × 2` block per plane, as the
bracket matrix `Ω` of `FourAxes`: the flux of a plane switches on exactly its own block.

## Main results

- `HarperFourAxes.weyl_first`, `HarperFourAxes.weyl_second` : the Weyl relation in each plane.
- `HarperFourAxes.commute_across` : the two planes commute, operator by operator.
- `HarperFourAxes.commute_first_iff`, `HarperFourAxes.commute_second_iff` : the step and the phase
  of a plane commute if and only if the flux of that plane is zero.
- `HarperFourAxes.isHermitian_harper4` : the four-axis Harper operator is Hermitian.
- `HarperFourAxes.harper4_commute` : the plane operators commute with each other, so the spectrum
  of `H` is the sumset of the plane spectra.
-/

@[expose] public noncomputable section

open Matrix Harper
open scoped Kronecker

namespace HarperFourAxes

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The first plane `(x, y)`: acts on the first factor. -/
def first (A : Matrix (ZMod N) (ZMod N) ℂ) :
    Matrix (ZMod N × ZMod M) (ZMod N × ZMod M) ℂ := A ⊗ₖ (1 : Matrix (ZMod M) (ZMod M) ℂ)

/-- The second plane `(z, w)`: acts on the second factor. -/
def second (B : Matrix (ZMod M) (ZMod M) ℂ) :
    Matrix (ZMod N × ZMod M) (ZMod N × ZMod M) ℂ := (1 : Matrix (ZMod N) (ZMod N) ℂ) ⊗ₖ B

lemma first_mul (A A' : Matrix (ZMod N) (ZMod N) ℂ) :
    first (M := M) A * first A' = first (A * A') := by
  simp [first, ← Matrix.mul_kronecker_mul]

lemma second_mul (B B' : Matrix (ZMod M) (ZMod M) ℂ) :
    second (N := N) B * second B' = second (B * B') := by
  simp [second, ← Matrix.mul_kronecker_mul]

omit [NeZero N] [NeZero M] in
lemma first_smul (c : ℂ) (A : Matrix (ZMod N) (ZMod N) ℂ) :
    first (M := M) (c • A) = c • first A := by
  simp [first, Matrix.smul_kronecker]

omit [NeZero N] [NeZero M] in
lemma second_smul (c : ℂ) (B : Matrix (ZMod M) (ZMod M) ℂ) :
    second (N := N) (c • B) = c • second B := by
  simp [second, Matrix.kronecker_smul]

omit [NeZero N] [NeZero M] in
lemma first_injective : Function.Injective (first (N := N) (M := M)) := by
  intro A A' h
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [first, Matrix.kroneckerMap_apply] using this

omit [NeZero N] [NeZero M] in
lemma second_injective : Function.Injective (second (N := N) (M := M)) := by
  intro B B' h
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [second, Matrix.kroneckerMap_apply] using this

/-- The Weyl relation in the first plane, with the flux `q / N`. -/
theorem weyl_first (q : ZMod N) :
    first (M := M) (clock N q) * first (shift N) =
      phase q • (first (shift N) * first (clock N q)) := by
  rw [first_mul, first_mul, clock_mul_shift, first_smul]

/-- The Weyl relation in the second plane, with the flux `r / M`. -/
theorem weyl_second (r : ZMod M) :
    second (N := N) (clock M r) * second (shift M) =
      phase r • (second (shift M) * second (clock M r)) := by
  rw [second_mul, second_mul, clock_mul_shift, second_smul]

/-- Operators of different planes commute. -/
theorem commute_across (A : Matrix (ZMod N) (ZMod N) ℂ) (B : Matrix (ZMod M) (ZMod M) ℂ) :
    Commute (first A) (second B) := by
  show first A * second B = second B * first A
  simp [first, second, ← Matrix.mul_kronecker_mul]

/-- The step and the phase of the first plane commute if and only if its flux is zero. -/
theorem commute_first_iff (q : ZMod N) :
    Commute (first (M := M) (shift N)) (first (clock N q)) ↔ q = 0 := by
  rw [← commute_iff]
  constructor
  · intro h
    exact first_injective (by simpa [first_mul] using h.eq)
  · intro h
    show first _ * first _ = first _ * first _
    rw [first_mul, first_mul, h.eq]

/-- The step and the phase of the second plane commute if and only if its flux is zero. -/
theorem commute_second_iff (r : ZMod M) :
    Commute (second (N := N) (shift M)) (second (clock M r)) ↔ r = 0 := by
  rw [← commute_iff]
  constructor
  · intro h
    exact second_injective (by simpa [second_mul] using h.eq)
  · intro h
    show second _ * second _ = second _ * second _
    rw [second_mul, second_mul, h.eq]

/-- The four-axis Harper operator: the Harper operator of each plane, with its own flux. -/
def harper4 (N M : ℕ) [NeZero N] [NeZero M] (q : ZMod N) (r : ZMod M) :
    Matrix (ZMod N × ZMod M) (ZMod N × ZMod M) ℂ :=
  first (harper N q) + second (harper M r)

omit [NeZero N] [NeZero M] in
lemma first_conjTranspose (A : Matrix (ZMod N) (ZMod N) ℂ) :
    (first (M := M) A)ᴴ = first Aᴴ := by
  simp [first, Matrix.conjTranspose_kronecker]

omit [NeZero N] [NeZero M] in
lemma second_conjTranspose (B : Matrix (ZMod M) (ZMod M) ℂ) :
    (second (N := N) B)ᴴ = second Bᴴ := by
  simp [second, Matrix.conjTranspose_kronecker]

/-- The four-axis Harper operator is Hermitian. -/
theorem isHermitian_harper4 (q : ZMod N) (r : ZMod M) : (harper4 N M q r).IsHermitian := by
  unfold harper4 Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, first_conjTranspose, second_conjTranspose,
    (isHermitian_harper q).eq, (isHermitian_harper r).eq]

/-- The two plane operators commute, so `H = H₁ + H₂` is a sum of commuting Hermitian operators. -/
theorem harper4_commute (q : ZMod N) (r : ZMod M) :
    Commute (first (M := M) (harper N q)) (second (N := N) (harper M r)) :=
  commute_across _ _

end HarperFourAxes
