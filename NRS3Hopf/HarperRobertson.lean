/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.HarperFourAxes
public import NavaRobertsonIndependent.Mathematics.D49_RobertsonDeterminant

/-!
# Robertson 1934 for the Harper observables: the flux of each plane switches on its own block

The four Hermitian observables of the two Weyl planes, the hoppings `S + S⋆` and the phases
`Z_q + Z_q⋆` of the planes `(x, y)` and `(z, w)`, are a finite family of observables on
`ℓ²(ZMod N × ZMod M)`. Robertson's relation `|det Ω| ≤ det Σ` holds for them in every state.

The matrix `Ω` is `Ω_jk = Im ⟨c_j, c_k⟩ = -½ ⟨i[L_j, L_k]⟩` (`tensionG_eq`): it only sees the
brackets. Observables of different planes commute, so the entries across planes vanish **in every
state**, not only in product states: `Ω` is block diagonal, one `2 × 2` block per plane. And if the
flux of a plane is zero, its step and its phase commute, so its block vanishes too.

## Main results

- `HarperRobertson.robertson_det_harper` : `|det Ω| ≤ det Σ` for the four Harper observables.
- `HarperRobertson.imMatrix_cross` : `Ω` vanishes across planes, in every state.
- `HarperRobertson.imMatrix_first_eq_zero`, `HarperRobertson.imMatrix_second_eq_zero` : with no
  flux in a plane, the block of that plane vanishes in every state.
- `HarperRobertson.hop_phaseObs_not_commute` : with a flux `q ≠ 0`, the hopping and the phase of a
  plane do not commute.
- `HarperRobertson.exists_imMatrix_first_ne_zero` : and then there is a state in which the entry of
  `Ω` of that plane does not vanish: the flux switches the block on, and only that block.
-/

@[expose] public noncomputable section

open Matrix Harper HarperFourAxes RobertsonDeterminant PathGraph3DNRS SpectralExtremal

namespace HarperRobertson

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The hopping of a plane: `S + S⋆`. -/
def hop (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ := shift N + (shift N)ᴴ

/-- The phase of a plane: `Z_q + Z_q⋆`. -/
def phaseObs (N : ℕ) [NeZero N] (q : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  clock N q + (clock N q)ᴴ

/-- The four Harper observables: hopping and phase of the plane `(x, y)`, then of `(z, w)`. -/
def obsMat (N M : ℕ) [NeZero N] [NeZero M] (q : ZMod N) (r : ZMod M) :
    Fin 4 → Matrix (ZMod N × ZMod M) (ZMod N × ZMod M) ℂ :=
  ![first (hop N), first (phaseObs N q), second (hop M), second (phaseObs M r)]

/-- The four Harper observables as operators of the Hilbert space. -/
def obs (N M : ℕ) [NeZero N] [NeZero M] (q : ZMod N) (r : ZMod M) (j : Fin 4) :
    EuclideanSpace ℂ (ZMod N × ZMod M) →ₗ[ℂ] EuclideanSpace ℂ (ZMod N × ZMod M) :=
  Matrix.toEuclideanLin (obsMat N M q r j)

lemma hop_isHermitian : (hop N).IsHermitian := by
  unfold hop Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

lemma phaseObs_isHermitian (q : ZMod N) : (phaseObs N q).IsHermitian := by
  unfold phaseObs Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

omit [NeZero N] [NeZero M] in
lemma first_isHermitian {A : Matrix (ZMod N) (ZMod N) ℂ} (h : A.IsHermitian) :
    (first (M := M) A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [first_conjTranspose, h.eq]

omit [NeZero N] [NeZero M] in
lemma second_isHermitian {B : Matrix (ZMod M) (ZMod M) ℂ} (h : B.IsHermitian) :
    (second (N := N) B).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [second_conjTranspose, h.eq]

lemma obsMat_isHermitian (q : ZMod N) (r : ZMod M) (j : Fin 4) :
    (obsMat N M q r j).IsHermitian := by
  fin_cases j
  · exact first_isHermitian hop_isHermitian
  · exact first_isHermitian (phaseObs_isHermitian q)
  · exact second_isHermitian hop_isHermitian
  · exact second_isHermitian (phaseObs_isHermitian r)

lemma obs_isSymmetric (q : ZMod N) (r : ZMod M) (j : Fin 4) : (obs N M q r j).IsSymmetric :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr (obsMat_isHermitian q r j))

/-- **Robertson 1934 for the four Harper observables**, in every state. -/
theorem robertson_det_harper (q : ZMod N) (r : ZMod M) (Φ : EuclideanSpace ℂ (ZMod N × ZMod M)) :
    |(imMatrix (obs N M q r) Φ).det| ≤ (covMatrix (obs N M q r) Φ).det :=
  robertson_det _ Φ

/-- Commuting symmetric operators have a vanishing entry of `Ω`, in every state. -/
lemma imMatrix_entry_eq_zero {ι : Type*} [Fintype ι]
    {L M' : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
    (hL : L.IsSymmetric) (hM : M'.IsSymmetric) (hc : L ∘ₗ M' = M' ∘ₗ L)
    (Φ : EuclideanSpace ℂ ι) :
    (inner ℂ (centeredG L Φ) (centeredG M' Φ)).im = 0 := by
  have h := tensionG_eq (Φ := Φ) hL hM
  have h0 : tensionG L M' Φ = 0 := by
    simp [tensionG, observableTension, opCommutator, hc]
  linarith

lemma toEuclideanLin_comp_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : A * B = B * A) :
    Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B =
      Matrix.toEuclideanLin B ∘ₗ Matrix.toEuclideanLin A := by
  ext v i
  simp only [LinearMap.comp_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec, h]

/-- **`Ω` is block diagonal in every state**: observables of different planes have no entry. -/
theorem imMatrix_cross (q : ZMod N) (r : ZMod M) (Φ : EuclideanSpace ℂ (ZMod N × ZMod M))
    (j k : Fin 4) (hj : j.val < 2) (hk : 2 ≤ k.val) :
    imMatrix (obs N M q r) Φ j k = 0 := by
  have hjk : obsMat N M q r j * obsMat N M q r k = obsMat N M q r k * obsMat N M q r j := by
    have h1 : ∃ A, obsMat N M q r j = first A := by
      fin_cases j <;> simp at hj <;> simp [obsMat]
    have h2 : ∃ B, obsMat N M q r k = second B := by
      fin_cases k <;> simp at hk <;> simp [obsMat]
    obtain ⟨A, hA⟩ := h1
    obtain ⟨B, hB⟩ := h2
    rw [hA, hB]
    exact (commute_across A B).eq
  exact imMatrix_entry_eq_zero (obs_isSymmetric q r j) (obs_isSymmetric q r k)
    (toEuclideanLin_comp_eq _ _ hjk) Φ

lemma clock_zero : clock N 0 = 1 := by
  simp [clock, Matrix.diagonal_one]

lemma hop_commute_phaseObs_zero : hop N * phaseObs N 0 = phaseObs N 0 * hop N := by
  simp [phaseObs, clock_zero, mul_add, add_mul]

/-- With no flux in the plane `(x, y)`, its block of `Ω` vanishes in every state. -/
theorem imMatrix_first_eq_zero (r : ZMod M) (Φ : EuclideanSpace ℂ (ZMod N × ZMod M)) :
    imMatrix (obs N M 0 r) Φ 0 1 = 0 := by
  have hc : obsMat N M 0 r 0 * obsMat N M 0 r 1 = obsMat N M 0 r 1 * obsMat N M 0 r 0 := by
    simp only [obsMat, Matrix.cons_val_zero, Matrix.cons_val_one, first_mul]
    rw [hop_commute_phaseObs_zero]
  exact imMatrix_entry_eq_zero (obs_isSymmetric 0 r 0) (obs_isSymmetric 0 r 1)
    (toEuclideanLin_comp_eq _ _ hc) Φ

/-- With no flux in the plane `(z, w)`, its block of `Ω` vanishes in every state. -/
theorem imMatrix_second_eq_zero (q : ZMod N) (Φ : EuclideanSpace ℂ (ZMod N × ZMod M)) :
    imMatrix (obs N M q 0) Φ 2 3 = 0 := by
  have hc : obsMat N M q 0 2 * obsMat N M q 0 3 = obsMat N M q 0 3 * obsMat N M q 0 2 := by
    simp only [obsMat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, second_mul]
    rw [hop_commute_phaseObs_zero]
  exact imMatrix_entry_eq_zero (obs_isSymmetric q 0 2) (obs_isSymmetric q 0 3)
    (toEuclideanLin_comp_eq _ _ hc) Φ

lemma phaseObs_eq_diagonal (q : ZMod N) :
    phaseObs N q = Matrix.diagonal fun k => ZMod.stdAddChar (q * k) + ZMod.stdAddChar (-(q * k)) := by
  ext i j
  simp only [phaseObs, clock, Matrix.add_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp [Harper.conj_stdAddChar]
  · simp [h, Ne.symm h]

lemma hop_apply_one_zero : hop N 1 0 ≠ 0 := by
  simp only [hop, Matrix.add_apply, Matrix.conjTranspose_apply, shift]
  by_cases h : (0 : ZMod N) = 1 + 1 <;> simp [h]

/-- **The flux switches the block on**: with a flux in a plane, the hopping and the phase of the
plane do not commute. -/
theorem hop_phaseObs_not_commute {q : ZMod N} (hq : q ≠ 0) :
    hop N * phaseObs N q ≠ phaseObs N q * hop N := by
  intro h
  have h1 := congrFun (congrFun h 1) 0
  rw [phaseObs_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : hop N 1 0 * (ZMod.stdAddChar (q * 0) + ZMod.stdAddChar (-(q * 0)) -
      (ZMod.stdAddChar (q * 1) + ZMod.stdAddChar (-(q * 1)))) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hop_apply_one_zero h3
  · have hre : (ZMod.stdAddChar q : ℂ) + ZMod.stdAddChar (-q) = 2 := by
      simp only [mul_zero, mul_one, neg_zero, AddChar.map_zero_eq_one] at h3
      linear_combination -h3
    have hn : (ZMod.stdAddChar q : ℂ) = 1 := by
      have hc : (starRingEnd ℂ) (ZMod.stdAddChar q) = ZMod.stdAddChar (-q) := Harper.conj_stdAddChar q
      have hn1 := Harper.norm_stdAddChar q
      set z : ℂ := ZMod.stdAddChar q
      rw [← hc] at hre
      have hre' : z.re = 1 := by
        have := congrArg Complex.re hre
        simp at this
        linarith
      have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
        have := Complex.sq_norm z
        rw [Complex.normSq_apply, hn1] at this
        nlinarith
      have him : z.im = 0 := by nlinarith
      apply Complex.ext <;> simp [hre', him]
    exact hq (ZMod.injective_stdAddChar (by rw [hn, AddChar.map_zero_eq_one]))

/-- A symmetric operator with vanishing expectation in every state is zero. -/
lemma eq_zero_of_tensionG_eq_zero {ι : Type*} [Fintype ι]
    {L M' : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
    (hL : L.IsSymmetric) (hM : M'.IsSymmetric)
    (h : ∀ Φ, (inner ℂ (centeredG L Φ) (centeredG M' Φ)).im = 0) : L ∘ₗ M' = M' ∘ₗ L := by
  have hK := observableTension_isSymmetric L M' hL hM
  have h0 : ∀ Φ : EuclideanSpace ℂ ι, inner ℂ (observableTension L M' Φ) Φ = 0 := by
    intro Φ
    have h1 := tensionG_eq (Φ := Φ) hL hM
    rw [h Φ] at h1
    have h2 : (inner ℂ Φ (observableTension L M' Φ)).re = 0 := by
      simpa [tensionG] using h1
    have h3 : (inner ℂ Φ (observableTension L M' Φ)).im = 0 := by
      have hc : (starRingEnd ℂ) (inner ℂ (observableTension L M' Φ) Φ) =
          inner ℂ Φ (observableTension L M' Φ) := inner_conj_symm Φ (observableTension L M' Φ)
      rw [hK Φ Φ] at hc
      exact Complex.conj_eq_iff_im.mp hc
    have : inner ℂ Φ (observableTension L M' Φ) = 0 := Complex.ext h2 h3
    rw [← inner_conj_symm, this]; simp
  have hz := (inner_map_self_eq_zero _).mp h0
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun hz v
  simp only [observableTension, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_zero,
    Complex.I_ne_zero, false_or] at this
  simpa [opCommutator, sub_eq_zero] using this

/-- **The flux switches the block on**: with a flux in the plane `(x, y)`, there is a state in
which its entry of `Ω` does not vanish. -/
theorem exists_imMatrix_first_ne_zero {q : ZMod N} (hq : q ≠ 0) (r : ZMod M) :
    ∃ Φ : EuclideanSpace ℂ (ZMod N × ZMod M), imMatrix (obs N M q r) Φ 0 1 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hc := eq_zero_of_tensionG_eq_zero (obs_isSymmetric q r 0) (obs_isSymmetric q r 1)
    (fun Φ => hcon Φ)
  apply hop_phaseObs_not_commute hq
  apply first_injective (M := M)
  have : (Matrix.toEuclideanLin (obsMat N M q r 0 * obsMat N M q r 1)) =
      Matrix.toEuclideanLin (obsMat N M q r 1 * obsMat N M q r 0) := by
    ext v i
    have := LinearMap.congr_fun hc v
    simpa [obs, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun w => w.ofLp i) this
  have h2 := (Matrix.toEuclideanLin.injective this)
  simpa [obsMat, first_mul] using h2

end HarperRobertson
